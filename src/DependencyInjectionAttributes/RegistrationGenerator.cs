using System.Collections.Immutable;
using System.Diagnostics.CodeAnalysis;
using System.Text;
using System.Text.RegularExpressions;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Diagnostics;
using KeyedService = (Microsoft.CodeAnalysis.INamedTypeSymbol Type, Microsoft.CodeAnalysis.TypedConstant? Key);

#pragma warning disable MA0006

namespace DependencyInjectionAttributes;

/// <summary>
/// Discovers annotated services during compilation and generates the partial method
/// implementations for <c>AddServices</c> to invoke.
/// </summary>
[Generator]
public class RegistrationGenerator : IIncrementalGenerator
{
  public static DiagnosticDescriptor AmbiguousLifetime { get; } = new(
    "DIA001",
    "Lifetime registration conflict",
    "More than one registration matches {0} with different lifetimes {1}",
    "Build",
    DiagnosticSeverity.Warning,
    isEnabledByDefault: true);

  private class ServiceSymbol(INamedTypeSymbol type, int lifetime, TypedConstant? key, Location? location)
  {
    public INamedTypeSymbol Type => type;
    public int Lifetime => lifetime;
    public TypedConstant? Key => key;
    public Location? Location => location;

    public override bool Equals(object? obj)
    {
      if (obj is not ServiceSymbol other)
        return false;

      return type.Equals(other.Type, SymbolEqualityComparer.Default) &&
             lifetime == other.Lifetime &&
             // ReSharper disable once SuspiciousTypeConversion.Global
             Equals(key, other);
    }

    public override int GetHashCode()
    {
      unchecked {
        int hash = SymbolEqualityComparer.Default.GetHashCode(type);
        hash = (hash * 17) ^ lifetime.GetHashCode();
        hash = (hash * 397) ^ (key?.GetHashCode() ?? 0);
        return hash;
      }
    }
  }

  record ServiceRegistration(int Lifetime, TypeSyntax? AssignableTo, string? FullNameExpression, Location? Location)
  {
    [field: AllowNull, MaybeNull]
    public Regex Regex => field ??= FullNameExpression is not null
      ? new(FullNameExpression, RegexOptions.CultureInvariant, TimeSpan.FromSeconds(10))
      : new(".*", RegexOptions.CultureInvariant, TimeSpan.FromSeconds(10));
  }

  static bool IsPropertyEnabled(AnalyzerConfigOptionsProvider options, string property)
    => options.GlobalOptions.TryGetValue("build_property." + property, out var value) &&
       bool.TryParse(value, out var isEnabled) && isEnabled;

  public void Initialize(IncrementalGeneratorInitializationContext context)
  {
    var types = context.CompilationProvider.Combine(context.AnalyzerConfigOptionsProvider).SelectMany((x, c) => {
      var (compilation, options) = x;

      // we won't add any registrations in these cases.
      if (IsPropertyEnabled(options, "DesignTimeBuild") || !IsPropertyEnabled(options, "AddServicesExtension"))
        return [];

      var visitor = new TypesVisitor(s => compilation.IsSymbolAccessible(s), c);
      compilation.GlobalNamespace.Accept(visitor);

      // also visit aliased references, which will not become part of the global:: namespace
      foreach (var symbol in compilation.References
                 .Where(r => !r.Properties.Aliases.IsDefaultOrEmpty)
                 .Select(r => compilation.GetAssemblyOrModuleSymbol(r))) {
        symbol?.Accept(visitor);
      }

      return visitor.TypeSymbols.Where(t => !t.IsAbstract && t.TypeKind == TypeKind.Class);
    });

    bool IsService(AttributeData attr) =>
      (attr.AttributeClass?.Name == "ServiceAttribute" || attr.AttributeClass?.Name == "Service") &&
      attr.ConstructorArguments.Length == 1 &&
      // will be error if roslyn can't get type
      attr.ConstructorArguments[0].Kind == TypedConstantKind.Enum &&
      attr.ConstructorArguments[0].Type?.ToDisplayString(SymbolDisplayFormat.FullyQualifiedFormat) ==
      "global::Microsoft.Extensions.DependencyInjection.ServiceLifetime";

    bool IsKeyedService(AttributeData attr) =>
      (attr.AttributeClass?.Name == "ServiceAttribute" || attr.AttributeClass?.Name == "Service" ||
       attr.AttributeClass?.Name == "KeyedService" || attr.AttributeClass?.Name == "KeyedServiceAttribute") &&
      //attr.AttributeClass?.IsGenericType == true &&
      attr.ConstructorArguments.Length == 2 &&
      // will be error if roslyn can't get type
      attr.ConstructorArguments[1].Kind == TypedConstantKind.Enum &&
      attr.ConstructorArguments[1].Type?.ToDisplayString(SymbolDisplayFormat.FullyQualifiedFormat) ==
      "global::Microsoft.Extensions.DependencyInjection.ServiceLifetime";

    // we recognize the attribute by name, not by type for flexability

    var attributedServices = types
      .SelectMany((x, _) => {
        var name = x.Name;
        var attrs = x.GetAttributes();
        var services = new List<ServiceSymbol>();

        foreach (var attr in attrs) {
          var serviceAttr = IsService(attr) || IsKeyedService(attr) ? attr : null;
          if (serviceAttr == null) {
            continue;
          }

          TypedConstant? key = null;
          // matches https://learn.microsoft.com/en-us/dotnet/api/microsoft.extensions.dependencyinjection.servicelifetime?view=net-10.0-pp
          int lifetime;
          if (IsKeyedService(serviceAttr)) {
            key = serviceAttr.ConstructorArguments[0];
            lifetime = (int)serviceAttr.ConstructorArguments[1].Value!;
          }
          else {
            lifetime = (int)serviceAttr.ConstructorArguments[0].Value!;
          }

          services.Add(new(x, lifetime, key,
            attr.ApplicationSyntaxReference?.GetSyntax(CancellationToken.None).GetLocation()));
        }

        return services.ToImmutableArray();
      })
      .Where(x => x != null);

    // conventional registrations.

    // First get all AddServices(type, regex, lifetime) invocations.
    var methodInvocations = context.SyntaxProvider
      .CreateSyntaxProvider(
        predicate: static (node, _) => node is InvocationExpressionSyntax invocation &&
                                       invocation.ArgumentList.Arguments.Count != 0 &&
                                       GetInvokedMethodName(invocation) == "AddServices",
        transform: static (ctx, _) => GetServiceRegistration((InvocationExpressionSyntax)ctx.Node, ctx.SemanticModel))
      .Combine(context.AnalyzerConfigOptionsProvider)
      .Where(x => {
        (var registration, var options) = x;
        return options.GlobalOptions.TryGetValue("build_property.AddServicesExtension", out var value) &&
               bool.TryParse(value, out var addServices) && addServices && registration is not null;
      })
      .Select((x, _) => x.Left)
      .Collect();

    // Project matching service types to register with the given lifetime.
    var conventionServices = types.Combine(methodInvocations.Combine(context.CompilationProvider))
      .SelectMany((pair, cancellationToken) => {
        var (typeSymbol, (registrations, compilation)) = pair;
        var results = ImmutableArray.CreateBuilder<ServiceSymbol>();

        foreach (var registration in registrations) {
          // check of typeSymbol is assignable (is the same type, inherits from it or implements if its an interface) to registration.AssignableTo
          if (registration!.AssignableTo is not null &&
              // Resolve the type against the current compilation
              compilation.GetSemanticModel(registration.AssignableTo.SyntaxTree)
                .GetSymbolInfo(registration.AssignableTo, cancellationToken)
                .Symbol is INamedTypeSymbol assignableTo &&
              !typeSymbol.Is(assignableTo)) {
            continue;
          }

          if (registration!.FullNameExpression != null &&
              !registration.Regex.IsMatch(typeSymbol.ToFullName(compilation))) {
            continue;
          }

          results.Add(new ServiceSymbol(typeSymbol, registration.Lifetime, null, registration.Location));
        }

        return results.ToImmutable();
      });

    // Flatten and remove duplicates
    var finalServices = attributedServices.Collect().Combine(conventionServices.Collect())
      .SelectMany((tuple, _) => ImmutableArray.CreateRange([tuple.Item1, tuple.Item2]))
      .SelectMany((items, _) => items.Distinct().ToImmutableArray());

    RegisterServicesOutput(context, finalServices, context.CompilationProvider);
  }

  void RegisterServicesOutput(IncrementalGeneratorInitializationContext context,
    IncrementalValuesProvider<ServiceSymbol> services,
    IncrementalValueProvider<Compilation> compilation
  )
  {
    context.RegisterImplementationSourceOutput(
      services.Where(x => x!.Lifetime == 0 && x.Key is null).Select((x, _) => new KeyedService(x!.Type, null)).Collect()
        .Combine(compilation),
      (ctx, data) => AddPartial("AddSingleton", ctx, data));

    context.RegisterImplementationSourceOutput(
      services.Where(x => x!.Lifetime == 1 && x.Key is null).Select((x, _) => new KeyedService(x!.Type, null)).Collect()
        .Combine(compilation),
      (ctx, data) => AddPartial("AddScoped", ctx, data));

    context.RegisterImplementationSourceOutput(
      services.Where(x => x!.Lifetime == 2 && x.Key is null).Select((x, _) => new KeyedService(x!.Type, null)).Collect()
        .Combine(compilation),
      (ctx, data) => AddPartial("AddTransient", ctx, data));

    context.RegisterImplementationSourceOutput(
      services.Where(x => x!.Lifetime == 0 && x.Key is not null).Select((x, _) => new KeyedService(x!.Type, x.Key!))
        .Collect().Combine(compilation),
      (ctx, data) => AddPartial("AddKeyedSingleton", ctx, data));

    context.RegisterImplementationSourceOutput(
      services.Where(x => x!.Lifetime == 1 && x.Key is not null).Select((x, _) => new KeyedService(x!.Type, x.Key!))
        .Collect().Combine(compilation),
      (ctx, data) => AddPartial("AddKeyedScoped", ctx, data));

    context.RegisterImplementationSourceOutput(
      services.Where(x => x!.Lifetime == 2 && x.Key is not null).Select((x, _) => new KeyedService(x!.Type, x.Key!))
        .Collect().Combine(compilation),
      (ctx, data) => AddPartial("AddKeyedTransient", ctx, data));

    context.RegisterImplementationSourceOutput(services.Collect(), ReportInconsistencies);
  }

  void ReportInconsistencies(SourceProductionContext context, ImmutableArray<ServiceSymbol> array)
  {
    var grouped = array.GroupBy(x => x.Type, SymbolEqualityComparer.Default).Where(g => g.Count() > 1)
      .ToImmutableArray();
    if (grouped.Length == 0)
      return;

    foreach (var group in grouped) {
      // report if within the group, there are different lifetimes with the same key (or no key)
      foreach (var keyed in group.GroupBy(x => x.Key?.Value).Where(g => g.Count() > 1)) {
        var lifetimes = keyed.Select(x => x.Lifetime).Distinct()
          .Select(x => x switch { 0 => "Singleton", 1 => "Scoped", 2 => "Transient", _ => "Unknown" })
          .ToArray();

        if (lifetimes.Length == 1)
          continue;

        var location = keyed.FirstOrDefault(x => x.Location != null)?.Location;
        var otherLocations = keyed.Where(x => x.Location != null).Skip(1).Select(x => x.Location!);

        context.ReportDiagnostic(Diagnostic.Create(AmbiguousLifetime,
          location, otherLocations, keyed.First().Type.ToDisplayString(), string.Join(", ", lifetimes)));
      }
    }
  }

  static string? GetInvokedMethodName(InvocationExpressionSyntax invocation) => invocation.Expression switch {
    MemberAccessExpressionSyntax memberAccess => memberAccess.Name.Identifier.Text,
    IdentifierNameSyntax identifierName => identifierName.Identifier.Text,
    _ => null,
  };

  static ServiceRegistration? GetServiceRegistration(InvocationExpressionSyntax invocation, SemanticModel semanticModel)
  {
    // this is somewhat expensive, so we try to first discard invocations that don't look like our
    // target first (no args and wrong method name), in the predicate, before moving on to semantic analyis here.
    var options = (CSharpParseOptions)invocation.SyntaxTree.Options;
    var compilation = semanticModel.Compilation;
    var model = compilation.GetSemanticModel(invocation.SyntaxTree);

    var symbolInfo = model.GetSymbolInfo(invocation);
    if (symbolInfo.Symbol is IMethodSymbol methodSymbol &&
        methodSymbol.GetAttributes().Any(static attr => attr.AttributeClass?.Name == "DDIAddServicesAttribute") &&
        methodSymbol.Parameters.Length >= 2) {
      var defaultLifetime = methodSymbol.Parameters
        .FirstOrDefault(x => x.Type.Name == "ServiceLifetime" && x.HasExplicitDefaultValue)?.ExplicitDefaultValue;
      var lifetime = defaultLifetime is int value ? value : 0;
      TypeSyntax? assignableTo = null;
      string? fullNameExpression = null;

      foreach (var argument in invocation.ArgumentList.Arguments) {
        var typeInfo = model.GetTypeInfo(argument.Expression).Type;

        if (typeInfo is INamedTypeSymbol namedType) {
          if (namedType.Name == "ServiceLifetime") {
            lifetime = (int?)model.GetConstantValue(argument.Expression).Value ?? 0;
          }
          else if (namedType.Name == "Type" && argument.Expression is TypeOfExpressionSyntax typeOf &&
                   model.GetSymbolInfo(typeOf.Type).Symbol is INamedTypeSymbol typeSymbol) {
            assignableTo = typeOf.Type;
          }
          else if (namedType.SpecialType == SpecialType.System_String) {
            fullNameExpression = model.GetConstantValue(argument.Expression).Value as string;
          }
        }
      }

      if (assignableTo != null || fullNameExpression != null) {
        return new ServiceRegistration(lifetime, assignableTo, fullNameExpression, invocation.GetLocation());
      }
    }

    return null;
  }

  void AddPartial(string methodName,
    SourceProductionContext ctx,
    (ImmutableArray<KeyedService> Types, Compilation Compilation) data
  )
  {
    var builder = new StringBuilder(512).AppendLine("// <auto-generated />");

    foreach (var alias in data.Compilation.References.SelectMany(r => r.Properties.Aliases)) {
      builder.AppendLine($"extern alias {alias};");
    }

    builder.AppendLine(
      $$"""
        using Microsoft.Extensions.DependencyInjection.Extensions;
        using System;

        namespace Microsoft.Extensions.DependencyInjection
        {
            static partial class AddServicesFromSourceGenerator
            {
                static partial void {{methodName}}Services(IServiceCollection services)
                {
        """);

    AddServices(data.Types.Where(x => x.Key is null).Select(x => x.Type), data.Compilation, methodName, builder);
    AddKeyedServices(data.Types.Where(x => x.Key is not null), data.Compilation, methodName, builder);

    builder.AppendLine(
      """
              }
          }
      }
      """);
    builder.Replace("\r\n", "\n");
    ctx.AddSource(methodName + ".g", builder.ToString());
  }

  void AddServices(IEnumerable<INamedTypeSymbol> services,
    Compilation compilation,
    string methodName,
    StringBuilder output
  )
  {
    foreach (var type in services) {
      var impl = type.ToFullName(compilation);
      var registered = new HashSet<string>(StringComparer.Ordinal);

      var ctor = type.InstanceConstructors
        .Where(IsAccessible)
        .OrderByDescending(m => m.Parameters.Length)
        .FirstOrDefault();

      if (ctor is { Parameters.Length: > 0 }) {
        var args = string.Join(", ", ctor.Parameters.Select(p => {
          var fromKeyed = p.GetAttributes().FirstOrDefault(IsFromKeyed);
          if (fromKeyed is not null)
            return
              $"s.GetRequiredKeyedService<{p.Type.ToFullName(compilation)}>({fromKeyed.ConstructorArguments[0].ToCSharpString()})";

          return $"s.GetRequiredService<{p.Type.ToFullName(compilation)}>()";
        }));
        output.AppendLine($"            services.Try{methodName}(s => new {impl}({args}));");
      }
      else {
        output.AppendLine($"            services.Try{methodName}(s => new {impl}());");
      }

      output.AppendLine($"            services.AddTransient<Func<{impl}>>(s => s.GetRequiredService<{impl}>);");
      output.AppendLine($"            services.AddTransient(s => new Lazy<{impl}>(s.GetRequiredService<{impl}>));");

      foreach (var iface in type.AllInterfaces) {
        if (!compilation.HasImplicitConversion(type, iface))
          continue;

        var ifaceName = iface.ToFullName(compilation);
        if (!registered.Contains(ifaceName)) {
          output.AppendLine($"            services.{methodName}<{ifaceName}>(s => s.GetRequiredService<{impl}>());");
          output.AppendLine(
            $"            services.AddTransient<Func<{ifaceName}>>(s => s.GetRequiredService<{ifaceName}>);");
          output.AppendLine(
            $"            services.AddTransient(s => new Lazy<{ifaceName}>(s.GetRequiredService<{ifaceName}>));");
          registered.Add(ifaceName);
        }

        // register covariant interfaces too, for at most one type parameter
        if (iface.IsGenericType &&
            iface.TypeParameters.Length == 1 &&
            iface.TypeParameters[0].Variance == VarianceKind.Out) {
          var typeParam = iface.TypeArguments[0];
          var candidates = typeParam.AllInterfaces.ToList();
          var baseType = typeParam.BaseType;
          while (baseType != null && baseType.SpecialType != SpecialType.System_Object) {
            candidates.Add(baseType);
            baseType = baseType.BaseType;
          }

          foreach (var candidate in candidates
                     .Where(x => x.SatisfiesConstraints(iface.TypeParameters[0]))
                     .Select(x => iface.ConstructedFrom.Construct(x))
                     .Where(x => x != null && compilation.HasImplicitConversion(type, x))
                     .ToImmutableHashSet(SymbolEqualityComparer.Default)
                     .Select(x => x!.ToFullName(compilation))) {
            if (!registered.Contains(candidate)) {
              output.AppendLine(
                $"            services.{methodName}<{candidate}>(s => s.GetRequiredService<{impl}>());");
              output.AppendLine(
                $"            services.AddTransient<Func<{candidate}>>(s => s.GetRequiredService<{candidate}>);");
              output.AppendLine(
                $"            services.AddTransient(s => new Lazy<{candidate}>(s.GetRequiredService<{candidate}>));");
              registered.Add(candidate);
            }
          }
        }
      }
    }

    return;

    bool IsAccessible(ISymbol s) => compilation.IsSymbolAccessible(s);
  }

  void AddKeyedServices(IEnumerable<KeyedService> services,
    Compilation compilation,
    string methodName,
    StringBuilder output
  )
  {
    bool isAccessible(ISymbol s) => compilation.IsSymbolAccessible(s);

    foreach (var type in services) {
      var impl = type.Type.ToFullName(compilation);
      var registered = new HashSet<string>(StringComparer.Ordinal);
      var key = type.Key!.Value.ToCSharpString();

      var ctor = type.Type.InstanceConstructors
        .Where(isAccessible)
        .OrderByDescending(m => m.Parameters.Length)
        .FirstOrDefault();

      if (ctor is { Parameters.Length: > 0 }) {
        var args = string.Join(", ", ctor.Parameters.Select(p => {
          var fromKeyed = p.GetAttributes().FirstOrDefault(IsFromKeyed);
          if (fromKeyed is not null) {
            return
              $"s.GetRequiredKeyedService<{p.Type.ToFullName(compilation)}>({fromKeyed.ConstructorArguments[0].ToCSharpString()})";
          }

          return $"s.GetRequiredService<{p.Type.ToFullName(compilation)}>()";
        }));
        output.AppendLine($"            services.{methodName}({key}, (s, k) => new {impl}({args}));");
      }
      else {
        output.AppendLine($"            services.{methodName}({key}, (s, k) => new {impl}());");
      }

      output.AppendLine(
        $"            services.AddKeyedTransient<Func<{impl}>>({key}, (s, k) => () => s.GetRequiredKeyedService<{impl}>(k));");
      output.AppendLine(
        $"            services.AddKeyedTransient({key}, (s, k) => new Lazy<{impl}>(() => s.GetRequiredKeyedService<{impl}>(k)));");

      foreach (var iface in type.Type.AllInterfaces) {
        var ifaceName = iface.ToFullName(compilation);
        if (!registered.Contains(ifaceName)) {
          output.AppendLine(
            $"            services.{methodName}<{ifaceName}>({key}, (s, k) => s.GetRequiredKeyedService<{impl}>(k));");
          output.AppendLine(
            $"            services.AddKeyedTransient<Func<{ifaceName}>>({key}, (s, k) => () => s.GetRequiredKeyedService<{ifaceName}>(k));");
          output.AppendLine(
            $"            services.AddKeyedTransient({key}, (s, k) => new Lazy<{ifaceName}>(() => s.GetRequiredKeyedService<{ifaceName}>(k)));");
          registered.Add(ifaceName);
        }

        // register covariant interfaces too, for at most one type parameter
        if (iface.IsGenericType &&
            iface.TypeParameters.Length == 1 &&
            iface.TypeParameters[0].Variance == VarianceKind.Out) {
          var typeParam = iface.TypeArguments[0];
          var candidates = typeParam.AllInterfaces.ToList();
          var baseType = typeParam.BaseType;
          while (baseType != null && baseType.SpecialType != SpecialType.System_Object) {
            candidates.Add(baseType);
            baseType = baseType.BaseType;
          }

          foreach (var candidate in candidates.Select(x => iface.ConstructedFrom.Construct(x))
                     .ToImmutableHashSet(SymbolEqualityComparer.Default)
                     .Where(x => x != null)
                     .Select(x => x!.ToFullName(compilation))) {
            if (!registered.Contains(candidate)) {
              output.AppendLine(
                $"            services.{methodName}<{candidate}>({key}, (s, k) => s.GetRequiredKeyedService<{impl}>(k));");
              output.AppendLine(
                $"            services.AddKeyedTransient<Func<{candidate}>>({key}, (s, k) => () => s.GetRequiredKeyedService<{candidate}>(k));");
              output.AppendLine(
                $"            services.AddKeyedTransient({key}, (s, k) => new Lazy<{candidate}>(() => s.GetRequiredKeyedService<{candidate}>(k)));");
              registered.Add(candidate);
            }
          }
        }
      }
    }
  }

  bool IsFromKeyed(AttributeData attr)
  {
    var attrName = attr.AttributeClass?.ToDisplayString(SymbolDisplayFormat.FullyQualifiedFormat);
    return string.Equals(attrName, "global::Microsoft.Extensions.DependencyInjection.FromKeyedServicesAttribute",
      StringComparison.Ordinal);
  }

  class TypesVisitor : SymbolVisitor
  {
    readonly Func<ISymbol, bool> _isAccessible;
    CancellationToken _cancellation;
    readonly HashSet<INamedTypeSymbol> _types = new(SymbolEqualityComparer.Default);
    public HashSet<INamedTypeSymbol> TypeSymbols => _types;

    public TypesVisitor(Func<ISymbol, bool> isAccessible, CancellationToken cancellation)
    {
      _isAccessible = isAccessible;
      _cancellation = cancellation;
    }

    public override void VisitAssembly(IAssemblySymbol symbol)
    {
      _cancellation.ThrowIfCancellationRequested();
      symbol.GlobalNamespace.Accept(this);
    }

    public override void VisitNamespace(INamespaceSymbol symbol)
    {
      foreach (var namespaceOrType in symbol.GetMembers()) {
        _cancellation.ThrowIfCancellationRequested();
        namespaceOrType.Accept(this);
      }
    }

    public override void VisitNamedType(INamedTypeSymbol type)
    {
      _cancellation.ThrowIfCancellationRequested();

      if (!_isAccessible(type) || !_types.Add(type))
        return;

      var nestedTypes = type.GetTypeMembers();
      if (nestedTypes.IsDefaultOrEmpty)
        return;

      foreach (var nestedType in nestedTypes) {
        _cancellation.ThrowIfCancellationRequested();
        nestedType.Accept(this);
      }
    }
  }
}

using Microsoft.CodeAnalysis.CSharp.Syntax;
using static Microsoft.CodeAnalysis.CSharp.SyntaxFactory;

namespace Microsoft.CodeAnalysis;

internal static class SymbolExtensions
{
  static readonly SymbolDisplayFormat _fullNameFormat = new(
    typeQualificationStyle: SymbolDisplayTypeQualificationStyle.NameAndContainingTypesAndNamespaces,
    genericsOptions: SymbolDisplayGenericsOptions.IncludeTypeParameters,
    miscellaneousOptions: SymbolDisplayMiscellaneousOptions.ExpandNullable);

  static readonly SymbolDisplayFormat _nonGenericFormat = new(
    typeQualificationStyle: SymbolDisplayTypeQualificationStyle.NameAndContainingTypesAndNamespaces,
    genericsOptions: SymbolDisplayGenericsOptions.None,
    miscellaneousOptions: SymbolDisplayMiscellaneousOptions.ExpandNullable);

  /// <summary>
  /// Like <see cref="Compilation.IsSymbolAccessibleWithin(ISymbol, ISymbol, ITypeSymbol?)" /> but doesn't throw
  /// See https://github.com/dotnet/roslyn/blob/2d6546bd2057aed95e6c3feeff0daca2272fee50/src/Compilers/Core/Portable/Compilation/Compilation.cs#L1659
  /// </summary>
  public static bool IsSymbolAccessible(this Compilation self, ISymbol symbol, ITypeSymbol? throughType = null)
  {
    try {
      return self.IsSymbolAccessibleWithin(symbol, self.Assembly, throughType);
    }
    catch {
      return false;
    }
  }

  public static string ToAssemblyNamespace(this INamespaceSymbol self)
    => self.ContainingAssembly.Name + "." + self.ToDisplayString(_fullNameFormat);

  public static string ToFullName(this ISymbol self, Compilation compilation)
  {
    var fullName = self.ToDisplayString(_nonGenericFormat);

    if (self is INamedTypeSymbol named && named.IsGenericType) {
      // ToFullName for each generic parameter
      var genericArguments = named.TypeArguments.Select(t => t.ToFullName(compilation));
      fullName = GenericName(fullName).WithTypeArgumentList(
          TypeArgumentList(SeparatedList<TypeSyntax>(genericArguments.Select(IdentifierName))))
        .ToString();
    }

    if (compilation.GetMetadataReference(self.ContainingAssembly) is MetadataReference reference &&
        !reference.Properties.Aliases.IsDefaultOrEmpty) {
      return reference.Properties.Aliases[0] + "::" + fullName;
    }

    return $"global::{fullName}";
  }

  public static string ToFullName(this ISymbol self, NameSyntax name, CancellationToken cancellation = default)
  {
    var fullName = self.ToDisplayString(_fullNameFormat);
    var root = name.SyntaxTree.GetRoot(cancellation);
    var aliases = root.ChildNodes().OfType<ExternAliasDirectiveSyntax>().Select(x => x.Identifier.Text).ToList();

    var candidate = name;
    while (candidate is QualifiedNameSyntax qualified) {
      candidate = qualified.Left;
    }

    if (candidate is IdentifierNameSyntax identifier &&
        aliases.Find(x => string.Equals(x, identifier.Identifier.Text, StringComparison.Ordinal)) is string alias) {
      return $"{alias}:{fullName}";
    }

    return fullName;
  }

  /// <summary>
  /// Checks whether the <paramref name="self"/> type inherits or implements the
  /// <paramref name="baseTypeOrInterface"/> type, even if it's a generic type
  /// </summary>
  public static bool Is(this ITypeSymbol? self, ITypeSymbol? baseTypeOrInterface)
  {
    if (self == null || baseTypeOrInterface == null)
      return false;

    if (self.Equals(baseTypeOrInterface, SymbolEqualityComparer.Default)) {
      return true;
    }

    if (baseTypeOrInterface is INamedTypeSymbol namedExpected &&
        self is INamedTypeSymbol namedActual &&
        namedActual.IsGenericType &&
        (namedActual.ConstructedFrom.Equals(namedExpected, SymbolEqualityComparer.Default) ||
         namedActual.ConstructedFrom.Equals(namedExpected.OriginalDefinition, SymbolEqualityComparer.Default))) {
      return true;
    }

    foreach (var iface in self.AllInterfaces) {
      if (iface.Is(baseTypeOrInterface)) {
        return true;
      }
    }

    if (self.BaseType?.Name.Equals("object", StringComparison.OrdinalIgnoreCase) == true) {
      return false;
    }

    return Is(self.BaseType, baseTypeOrInterface);
  }

  public static bool SatisfiesConstraints(this ITypeSymbol self, ITypeParameterSymbol typeParameter)
  {
    // check reference type constraint
    if (typeParameter.HasReferenceTypeConstraint && !self.IsReferenceType)
      return false;

    // check value type constraint
    if (typeParameter.HasValueTypeConstraint && !self.IsValueType)
      return false;

    // check base class and interface constraints
    foreach (var constraint in typeParameter.ConstraintTypes) {
      if (constraint.TypeKind == TypeKind.Class) {
        if (!self.GetBaseTypes().Any(baseType => SymbolEqualityComparer.Default.Equals(baseType, constraint)))
          return false;
      }
      else if (constraint.TypeKind == TypeKind.Interface) {
        if (!self.AllInterfaces.Any(interfaceSymbol =>
              SymbolEqualityComparer.Default.Equals(interfaceSymbol, constraint))) {
          return false;
        }
      }
    }

    // constructor constraint (optional, not typically needed here)
    if (typeParameter.HasConstructorConstraint) {
      // Check for parameterless constructor (simplified)
      var hasParameterlessConstructor = self.GetMembers(".ctor")
        .OfType<IMethodSymbol>()
        .Any(ctor => ctor.Parameters.Length == 0);
      if (!hasParameterlessConstructor)
        return false;
    }

    return true;
  }

  static IEnumerable<ITypeSymbol> GetBaseTypes(this ITypeSymbol typeSymbol)
  {
    var currentType = typeSymbol.BaseType;
    while (currentType != null && currentType.SpecialType != SpecialType.System_Object) {
      yield return currentType;
      currentType = currentType.BaseType;
    }
  }
}

# DependencyInjectionAttributes

[![License](https://img.shields.io/github/license/vchirikov/DependencyInjectionAttributes.svg)](https://raw.githubusercontent.com/vchirikov/DependencyInjectionAttributes/master/LICENSE)
[![NuGetVersion](https://img.shields.io/nuget/v/DependencyInjectionAttributes.svg)](https://www.nuget.org/packages/DependencyInjectionAttributes)
![NuGetDownloads](https://img.shields.io/nuget/dt/DependencyInjectionAttributes.svg)
![Build](https://github.com/vchirikov/DependencyInjectionAttributes/workflows/Publish/badge.svg)


Source-generated compile-time service registrations via attributes for `Microsoft.Extensions.DependencyInjection` with no runtime dependencies.


```xml
<Project>
  <PropertyGroup>
    <!-- Use AddServiceAttribute to generate `ServiceAttribute` (e.g. in a shared/platform/utils project) -->
    <AddServiceAttribute>true</AddServiceAttribute>
    <!-- Use AddServicesExtension to generate `AddServices` extensions methods (e.g. in an app project) -->
    <AddServicesExtension>true</AddServicesExtension>
  </PropertyGroup>
</Project>
```

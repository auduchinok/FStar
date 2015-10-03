namespace System
open System.Reflection

[<assembly: AssemblyTitleAttribute("fstar")>]
[<assembly: AssemblyProductAttribute("FStar")>]
[<assembly: AssemblyDescriptionAttribute("An ML-like language with a type system for program verification")>]
[<assembly: AssemblyVersionAttribute("1.0")>]
[<assembly: AssemblyFileVersionAttribute("1.0")>]
do ()

module internal AssemblyVersionInformation =
    let [<Literal>] Version = "1.0"

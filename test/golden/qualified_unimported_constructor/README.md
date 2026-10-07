# qualified_unimported_constructor

`user` references `palette:red` but never imports `palette`. The constructor
is exported by `palette`, so the defect is the missing import: `YCHR-20014`
(`ModuleNotImported`), not the false "does not export" of `YCHR-20010`
(`NonExportedConstructor`) that a program-wide constructor provider map
would otherwise emit. The function analogue is pinned by
`qualified_module_not_imported`.

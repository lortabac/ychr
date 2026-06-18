# qualified_module_not_imported

`modc` writes the qualified reference `moda:aa(X)` but only imports `modb`,
never `moda`. `moda` plainly exports `aa/1`, so the failure is "module not
imported", reported as `YCHR-20014` (`ModuleNotImported`) — *not* the
misleading "does not export" of `YCHR-20009`.

Regression test for the `dev-docs/BUGS.md` entry on `YCHR-20009` overreach.

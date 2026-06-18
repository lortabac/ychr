# qualified_unknown_module

`main` references `zzz:foo(X)`, but no module named `zzz` exists anywhere in
the program. Reported as `YCHR-20015` (`UnknownModule`) rather than the
misleading "Module 'zzz' does not export ..." of `YCHR-20009`.

Regression test for the `dev-docs/BUGS.md` entry on `YCHR-20009` overreach.

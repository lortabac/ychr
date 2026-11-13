"""Golden tests for the Scheme backend.

Each test directory under test/golden/ contains one or more .chr files
(compiled together) plus one or more <case>.goal/<case>.expected pairs.
For each case, this harness compiles the program to Scheme, generates a
driver script for the case's goal, runs it with Guile 3, and compares
the output against <case>.expected.

Negative tests are skipped — the Scheme harness only validates positive
output. A case is negative when its ``.goal`` is paired with an
``.error`` instead of an ``.expected`` (in a directory of its own or
mixed with positive cases); ``discover_cases`` keys on the
``.expected``, so those goals are simply not collected.
"""

import glob
import os
import shutil
import subprocess

import pytest

GOLDEN_DIR = os.path.join(os.path.dirname(__file__), "..", "golden")

# Test directories whose tests exercise Haskell-only meta-programming
# primitives and therefore cannot run on the Scheme backend.
HASKELL_ONLY = {
    # `host:'-'(3)` is a host call at an arity no primitive provides.
    # The Haskell registry is keyed by name alone, so it reaches the
    # binary primitive and reports that primitive's arity error; the
    # Scheme prelude table is keyed by (name, arity) and reports
    # `is: functor is not evaluable: host:-/1`. The directory holds only
    # a .goal/.error pair, so the harness would not collect it today;
    # the entry keeps it out if an .expected is ever added, and records
    # the divergence (dev-docs/SCHEME_BACKEND_GAPS.md). The evaluable
    # counterpart, `is_evaluable_host_term`, runs on both backends.
    "host_term_wrong_arity",
}

# Specific (test_dir, case_name) pairs to skip on Scheme. Used when only
# some cases in a directory diverge.
HASKELL_ONLY_CASES: set[tuple[str, str]] = set()

# Test directories where the .chr program or goal deliberately uses
# bare atoms whose constructor the renamer cannot resolve — the warning
# is part of what the test exercises (cross-module visibility,
# canonicalization fallbacks), or the test uses bare sentinel atoms as
# RHS of `=` (where `quote/1` no longer strips, per the spec).
# `--Werror` is omitted for these.
#
# Mirrors `expectsWarnings` in test/YCHR/GoldenTest.hs, with one
# difference by construction: this harness runs only *positive* cases, so
# a directory whose warning belongs to a negative case needs no entry
# here (`typecheck_goal_ctor_arity`).
WERROR_EXEMPT = {
    "arity_overload",
    # The `= …` right-hand sides are undeclared sentinel atoms, so every
    # rule emits YCHR-20101; the cases pin how those atoms print.
    "atom_quoting",
    "nonexhaustive_color",
    "nonexhaustive_nested",
    "bare_atom_canonicalization",
    "bare_vs_qualified",
    "bare_vs_qualified_swapped",
    "comments_and_whitespace",
    "comparisons",
    "copy_term_sharing",
    "cross_module_function_leak",
    "false_guard",
    "function_reference_dispatch",
    "graph_test",
    "hnf_compound_head",
    "hnf_list_head",
    "hnf_literal_in_head",
    "hnf_repeated_var_across_partners",
    "hnf_repeated_var_within_head",
    "hnf_wildcard_in_head",
    "lambda_curried_adder",
    "quoted_constraint_name",
    "short_alias_collision",
    "term_variables",
    "type_export_constructor_allowlist",
    "type_export_constructor_empty",
    "type_import_constructor_narrowing",
    "type_predicates",
    # Bare `foo` names a constructor of a module that is not imported,
    # so it is undeclared here (YCHR-20101).
    "typecheck_invisible_constructor",
    "typecheck_polymorphic_constraint",
    "typecheck_qualified_in_head",
    # These pin the inaccessible-branch warning (YCHR-20104): a guard
    # whose typing fact contradicts a known type marks a rule or
    # equation that can never fire — dead code, not a type error.
    "refining_user_dead_rule",
    "typecheck_evidence_bool_rule",
    "typecheck_evidence_dead_rule",
    "typecheck_list_pattern_dead",
    "typecheck_open_function_dead_equation",
    "typecheck_qualified_in_head_dead",
    "typecheck_shared_var_dead",
    "unicode_atoms_strings",
    "unifiable",
    # The goal hands over undeclared constructors (`f`, `hello`) so the
    # pinned `write_term_to_string` output keeps their unqualified
    # spelling; a declared one would print as `write_term_test:f`.
    "write_term_test",
}


def discover_cases():
    """Return sorted list of (test_dir, case_name) for all positive cases."""
    cases = []
    for entry in sorted(os.listdir(GOLDEN_DIR)):
        dir_path = os.path.join(GOLDEN_DIR, entry)
        if not os.path.isdir(dir_path):
            continue
        # A positive case is a .goal paired with a .expected. Keying on
        # the .expected is what makes mixed-mode directories work: a
        # .goal paired with a .error instead is a goal-negative case,
        # which this harness does not run, and a directory of bare
        # .error files has no .goal files to find. Skipping any
        # directory that merely *contains* a .error would drop the
        # positive cases of a mixed directory along with them.
        for goal in sorted(glob.glob(os.path.join(dir_path, "*.goal"))):
            case_name = os.path.splitext(os.path.basename(goal))[0]
            if not os.path.exists(os.path.join(dir_path, case_name + ".expected")):
                continue
            cases.append((entry, case_name))
    return cases


@pytest.mark.parametrize("test_dir,case_name", discover_cases())
def test_scheme_golden(
    test_dir,
    case_name,
    ychr_bin,
    guile_bin,
    scheme_lib_dir,
    scheme_compile_cache,
    project_root,
    tmp_path,
):
    if test_dir in HASKELL_ONLY:
        pytest.skip(f"{test_dir} uses Haskell-only meta primitives")
    if (test_dir, case_name) in HASKELL_ONLY_CASES:
        pytest.skip(f"{test_dir}-{case_name} diverges on the Scheme backend")

    dir_path = os.path.join(GOLDEN_DIR, test_dir)
    chr_files = sorted(glob.glob(os.path.join(dir_path, "*.chr")))
    assert chr_files, f"No .chr files in {dir_path}"
    goal_file = os.path.join(dir_path, f"{case_name}.goal")
    expected_file = os.path.join(dir_path, f"{case_name}.expected")

    with open(goal_file) as f:
        query = f.read().strip()
    with open(expected_file) as f:
        expected = f.read()

    werror_flags = [] if test_dir in WERROR_EXEMPT else ["--Werror"]

    # 1. Compile to Scheme. Every case in a directory compiles the same
    # files, so the library is built once per directory and reused; the
    # cached result (success or failure) is replayed for each case.
    lib_dir, result = scheme_compile_cache.compile(
        test_dir, chr_files, werror_flags, ychr_bin, project_root
    )
    assert result.returncode == 0, f"compile failed:\n{result.stdout}\n{result.stderr}"

    # 2. Generate driver. The compile step above already type-checked the
    # same files, so `--no-check` only skips a redundant second pass:
    # type errors still fail step 1, and compile- and goal-level warnings
    # are still reported and still gated by `--Werror`.
    result = subprocess.run(
        [ychr_bin, "gen-driver", "--no-check", *werror_flags, "-g", query, *chr_files],
        capture_output=True,
        text=True,
        cwd=project_root,
    )
    assert result.returncode == 0, f"gen-driver failed:\n{result.stdout}\n{result.stderr}"

    driver_path = tmp_path / "driver.sps"
    driver_path.write_text(result.stdout)

    # 3. Run with Guile, importing the cached library.
    result = subprocess.run(
        [
            guile_bin,
            "--r6rs",
            "--no-auto-compile",
            "-L", scheme_lib_dir,
            "-L", str(lib_dir),
            str(driver_path),
        ],
        capture_output=True,
        text=True,
        cwd=project_root,
    )
    assert result.returncode == 0, f"guile failed:\n{result.stdout}\n{result.stderr}"

    # 4. Compare output
    assert result.stdout == expected


def test_gen_driver_over_arity_goal(ychr_bin, project_root, tmp_path):
    """`gen-driver` resolves its goal through the shared resolver, so an
    over-arity `$call` in the goal is rejected with YCHR-16022 there too,
    rather than generated into a driver."""
    program = tmp_path / "gd.chr"
    program.write_text(
        ":- module(gd, [go/1]).\n"
        ":- use_module(library(prelude)).\n"
        ":- chr_constraint go(any).\n"
    )
    goal = (
        "go('$call'(fun(A, B, C, D, E, F, G, H, I, J, K) -> A end,"
        " 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11))"
    )
    result = subprocess.run(
        [ychr_bin, "gen-driver", "-g", goal, str(program)],
        capture_output=True,
        text=True,
        cwd=project_root,
    )
    assert result.returncode != 0
    assert "YCHR-16022" in result.stdout + result.stderr


def test_gen_driver_host_call_mapping(ychr_bin, project_root, tmp_path):
    """A `host:` call in a goal argument must lower to the runtime
    procedure the compiled library would use — not to a `host__*`
    identifier, which no Scheme module defines — with the session
    threaded for session host calls.

    This pins the driver text without Guile, so the mapping stays shared
    with `Scheme.compileHostCall` even when the golden suite is skipped.
    """
    program = tmp_path / "gdhc.chr"
    program.write_text(
        ":- module(gdhc, [go/2]).\n"
        ":- use_module(library(prelude)).\n"
        ":- chr_constraint go(any, any).\n"
    )

    def driver(goal):
        result = subprocess.run(
            [ychr_bin, "gen-driver", "-g", goal, str(program)],
            capture_output=True,
            text=True,
            cwd=project_root,
        )
        assert result.returncode == 0, result.stdout + result.stderr
        return result.stdout

    arith = driver("gdhc:go(host:'+'(1, 2), R)")
    assert "host__" not in arith
    assert "(%add 1 2)" in arith

    # A variable argument is dereferenced; a literal or a call that
    # returns a number is not.
    nested = driver("gdhc:go(host:'+'(R, host:'+'(1, 2)), R)")
    assert "(%add (deref R) (%add 1 2))" in nested

    # `copy_term` needs the session threaded as the procedure's first
    # argument; without it the driver calls `%copy-term` at arity 1.
    session = driver("gdhc:go(host:copy_term(1), R)")
    assert "(%copy-term %s 1)" in session

    # `write_term_to_string` is mapped but needs no session — the
    # reference primitive only renders — so it must *not* thread `%s`.
    writer = driver("gdhc:go(host:write_term_to_string(1), R)")
    assert "(%write-term-to-string 1)" in writer

    # `print_store` and `write_store_to_list` have no user-visible
    # argument but read the store, so they thread the session like
    # `copy_term`.
    store_printer = driver("gdhc:go(host:print_store(), R)")
    assert "(%print-store %s)" in store_printer
    store_list = driver("gdhc:go(host:write_store_to_list(), R)")
    assert "(%write-store-to-list %s)" in store_list

    # An unmapped name passes through verbatim, exactly as the compiled
    # library emits it.
    unmapped = driver("gdhc:go(host:my_add(1, 2), R)")
    assert "(my_add 1 2)" in unmapped


def test_meta_print_end_to_end(ychr_bin, guile_bin, scheme_lib_dir, project_root, tmp_path):
    """`library(meta)`'s `print/1` must pretty-print on the Scheme
    backend, matching the Haskell interpreter's `print` host call: each
    argument is rendered in surface syntax on its own line.

    Pinned end to end (compile -> gen-driver -> Guile) because the
    golden harness cannot: the Haskell runner compares variable
    bindings only, while this harness compares all of stdout, so a
    program that prints has no shared `.expected` form.
    """
    program = tmp_path / "mp.chr"
    program.write_text(
        ":- module(mp, [go/1]).\n"
        ":- use_module(library(prelude)).\n"
        ":- use_module(library(meta)).\n"
        ":- chr_constraint go(any).\n"
        'go(X) <=> print([1, X]), print("hi"), print(42).\n'
    )

    result = subprocess.run(
        [ychr_bin, "compile", "-t", "scheme", "-d", str(tmp_path), str(program)],
        capture_output=True,
        text=True,
        cwd=project_root,
    )
    assert result.returncode == 0, result.stdout + result.stderr

    result = subprocess.run(
        [ychr_bin, "gen-driver", "-g", "mp:go(R)", str(program)],
        capture_output=True,
        text=True,
        cwd=project_root,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    driver_path = tmp_path / "driver.sps"
    driver_path.write_text(result.stdout)

    result = subprocess.run(
        [
            guile_bin,
            "--r6rs",
            "--no-auto-compile",
            "-L",
            scheme_lib_dir,
            "-L",
            str(tmp_path),
            str(driver_path),
        ],
        capture_output=True,
        text=True,
        cwd=project_root,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    # Each argument on its own line, in surface syntax; then the
    # driver's bindings. `X` is unbound, so it renders as `_`.
    assert result.stdout == '[1, _]\n"hi"\n42\nR = _\n'


def test_meta_print_store_end_to_end(
    ychr_bin, guile_bin, scheme_lib_dir, project_root, tmp_path
):
    """`library(meta)`'s `print_store/0` and `write_store_to_list/0` must
    read the store on the Scheme backend, matching the Haskell
    interpreter: every alive constraint, module-qualified, type index
    ascending — and the same constraints as a list from
    `write_store_to_list/0`.

    Pinned end to end (compile -> gen-driver -> Guile) because the golden
    harness cannot carry a shared case: the Haskell runner compares
    variable bindings only, while this harness compares all of stdout, so
    a program that prints has no shared `.expected` form. The
    `write_store_to_list_test` golden directory covers the no-printing
    half on both backends.
    """
    program = tmp_path / "mps.chr"
    program.write_text(
        ":- module(mps, [go/1]).\n"
        ":- use_module(library(prelude)).\n"
        ":- use_module(library(meta)).\n"
        ":- chr_constraint go(any).\n"
        ":- chr_constraint c/1.\n"
        ":- chr_constraint d/2.\n"
        "go(R) <=> c(1), d(2, 3), print_store(), R is write_store_to_list().\n"
    )

    result = subprocess.run(
        [ychr_bin, "compile", "-t", "scheme", "-d", str(tmp_path), str(program)],
        capture_output=True,
        text=True,
        cwd=project_root,
    )
    assert result.returncode == 0, result.stdout + result.stderr

    result = subprocess.run(
        [ychr_bin, "gen-driver", "-g", "mps:go(R)", str(program)],
        capture_output=True,
        text=True,
        cwd=project_root,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    driver_path = tmp_path / "driver.sps"
    driver_path.write_text(result.stdout)

    result = subprocess.run(
        [
            guile_bin,
            "--r6rs",
            "--no-auto-compile",
            "-L",
            scheme_lib_dir,
            "-L",
            str(tmp_path),
            str(driver_path),
        ],
        capture_output=True,
        text=True,
        cwd=project_root,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    # One module-qualified line per alive constraint, in type index
    # order, then the driver's binding for the same store as a list.
    assert result.stdout == (
        "mps:c(1)\n"
        "mps:d(2, 3)\n"
        "R = [mps:c(1), mps:d(2, 3)]\n"
    )


def test_meta_module_host_calls_are_bound(ychr_bin, project_root, tmp_path):
    """A module importing `library(meta)` defines *every* meta function,
    whether or not the Scheme runtime implements it (only
    `run_chr_session` is still a stub). Each call must lower to a bound
    runtime procedure, not to a bare identifier: a bare identifier makes
    the whole generated library fail to load on a strict R6RS
    implementation (Chez reports `attempt to reference unbound
    identifier run_chr_session`), so a program that only uses `print/1`
    could not be loaded at all.

    Pinned on the generated text so it holds regardless of which Scheme
    runs the suite (the harness itself is Guile-only).
    """
    program = tmp_path / "metab.chr"
    program.write_text(
        ":- module(metab, [go/1]).\n"
        ":- use_module(library(prelude)).\n"
        ":- use_module(library(meta)).\n"
        ":- chr_constraint go(any).\n"
        "go(X) <=> print(X).\n"
    )
    result = subprocess.run(
        [ychr_bin, "compile", "-t", "scheme", "-d", str(tmp_path), str(program)],
        capture_output=True,
        text=True,
        cwd=project_root,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    generated = (tmp_path / "ychr" / "generated" / "program.sls").read_text()

    for stub in (
        "%write-term-to-string",
        "%write-store-to-list",
        "%print-store",
        "%run-chr-session",
        "%run-chr-session-ep",
        "%read-term-from-string",
    ):
        assert stub in generated, f"{stub} missing from the generated library"
    # No bare, unbound call to any meta function may survive. The
    # `register-evaluable!` tables spell the same names as
    # `meta__print_store`, so match the call shape at both arities:
    # `(name)` for the nullary ones and `(name ` for the unary ones.
    for bare in (
        "print_store",
        "write_term_to_string",
        "write_store_to_list",
        "run_chr_session",
        "run_chr_session_ep",
        "read_term_from_string",
    ):
        for call in (f"({bare})", f"({bare} "):
            assert call not in generated, f"bare {call}... in generated library"


def test_search_module_host_calls_are_bound(ychr_bin, project_root, tmp_path):
    """The `library(search)` counterpart of
    `test_meta_module_host_calls_are_bound`: each driver call must lower
    to a bound runtime procedure so that a program importing the library
    (directly, or through `library(state)`) still loads on Chez.
    """
    program = tmp_path / "searchb.chr"
    program.write_text(
        ":- module(searchb, [go/1]).\n"
        ":- use_module(library(state)).\n"
        ":- chr_type key ---> k.\n"
        ":- state(k, int).\n"
        ":- chr_constraint go(any).\n"
        "go(R) <=> new_k(1), get_k(R).\n"
    )
    result = subprocess.run(
        [ychr_bin, "compile", "-t", "scheme", "-d", str(tmp_path), str(program)],
        capture_output=True,
        text=True,
        cwd=project_root,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    generated = (tmp_path / "ychr" / "generated" / "program.sls").read_text()

    for stub in ("%solve", "%fail", "%findall", "%fold-solutions"):
        assert stub in generated, f"{stub} missing from the generated library"
    for bare in ("solve", "fail", "findall", "fold_solutions"):
        for call in (f"({bare})", f"({bare} "):
            assert call not in generated, f"bare {call}... in generated library"


def test_gen_driver_dynamic_call_mapping(ychr_bin, project_root, tmp_path):
    """A `'$call'` in a goal must lower to the runtime's `%apply-closure`
    — which resolves the closure through the session's callables table —
    not to a `call_N` identifier that no generated library defines any
    more.

    The callee here is a goal variable. A function reference *as the
    callee* does not resolve today (`fun double/1` under `'$call'` is
    reported as an unknown name), a separate, pre-existing gap in the
    query renamer; the reachable function-reference path — one passed to
    a declared function — is pinned end to end by the `driver_funref`
    golden case. This test pins the driver text without Guile.
    """
    program = tmp_path / "gdc.chr"
    program.write_text(
        ":- module(gdc, [go/2]).\n"
        ":- use_module(library(prelude)).\n"
        ":- chr_constraint go(any, any).\n"
    )
    result = subprocess.run(
        [
            ychr_bin,
            "gen-driver",
            "-g",
            "gdc:go('$call'(F, 1), R)",
            str(program),
        ],
        capture_output=True,
        text=True,
        cwd=project_root,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    driver_text = result.stdout
    assert "call_" not in driver_text
    assert "(%apply-closure %s F 1)" in driver_text


def test_gen_driver_nested_goal_var_declaration(ychr_bin, project_root, tmp_path):
    """A variable nested inside a goal argument must be bound in the
    driver's `let*`, not only the ones appearing at the top level.

    The driver once collected variables with a comprehension over the
    *top-level* arguments, so a nested variable (then spelled
    `p(1, X)`, today `quote(p(1, X))`) reached the constraint as a free
    identifier and Guile rejected the whole script with
    `Unbound variable: X`. This pins the recursive collection that
    closed the `type_predicates-grd_no` gap without needing Guile.
    """
    program = tmp_path / "gdn.chr"
    program.write_text(
        ":- module(gdn, [go/2]).\n"
        ":- use_module(library(prelude)).\n"
        ":- chr_constraint go(any, any).\n"
    )

    def driver(goal):
        result = subprocess.run(
            [ychr_bin, "gen-driver", "-g", goal, str(program)],
            capture_output=True,
            text=True,
            cwd=project_root,
        )
        assert result.returncode == 0, result.stdout + result.stderr
        return result.stdout

    # `X` is nested in the compound argument and `R` is top-level; both
    # must be declared, referenced, and printed.
    quoted = driver("gdn:go(quote(p(1, X)), R)")
    assert "(X (make-var %s))" in quoted
    assert "(R (make-var %s))" in quoted
    assert "(make-compound2 (quote p) 1 X)" in quoted
    assert "(cons (quote X) X)" in quoted

    # A host-call argument takes a different branch of the variable
    # collection, so pin that shape too.
    host_call = driver("gdn:go(host:'+'(X, 1), R)")
    assert "(X (make-var %s))" in host_call
    assert "(R (make-var %s))" in host_call


# `--import`: a `host:` call to a name the runtime doesn't define is a
# plain Scheme call, so it needs a library to bind it. Chez checks free
# names when it loads the library, so it is the backend this matters on.
IMPORT_PROGRAM = """\
:- module(h, [type(symbol/0), c/2]).
:- opaque_type symbol.
:- chr_constraint c(symbol, any).

:- function arrow_name() -> symbol.
arrow_name() -> host:arrow_name().

c(N, R) <=> N == arrow_name() | R = 1.
c(_, R) <=> R = 0.
"""

IMPORT_HOSTS = """\
(library (vhc hosts)
  (export arrow_name)
  (import (rnrs))
  (define the-arrow (string->symbol "ghc-prim:GHC.Types:tc:->"))
  (define (arrow_name) the-arrow))
"""

IMPORT_USE = """\
(import (rnrs) (ychr) (ychr generated h))
(define s (open-session h))
(define (ask name)
  (let ([r (make-var s)])
    (h:c/2 s name r)
    (write (deref r))
    (newline)))
(ask (string->symbol "ghc-prim:GHC.Types:tc:->"))
(ask 'other)
"""


def write_import_fixture(tmp_path):
    program = tmp_path / "h.chr"
    program.write_text(IMPORT_PROGRAM)
    out = tmp_path / "out"
    (out / "vhc").mkdir(parents=True)
    (out / "vhc" / "hosts.sls").write_text(IMPORT_HOSTS)
    return program, out


def ychr_run(ychr_bin, project_root, *args):
    return subprocess.run(
        [ychr_bin, *args], capture_output=True, text=True, cwd=project_root
    )


def test_import_host_library_chez(ychr_bin, scheme_lib_dir, project_root, tmp_path):
    chez = os.environ.get("YCHR_SCHEME", "scheme")
    if shutil.which(chez) is None:
        pytest.skip(f"no Chez Scheme executable found (tried {chez})")
    program, out = write_import_fixture(tmp_path)
    use = tmp_path / "use.sps"
    use.write_text(IMPORT_USE)

    def compile_and_run(*extra):
        r = ychr_run(
            ychr_bin, project_root,
            "compile", "-t", "scheme", "-n", "h", "-d", str(out), *extra,
            str(program), "--Werror",
        )
        assert r.returncode == 0, r.stdout + r.stderr
        return subprocess.run(
            [chez, "--libdirs", f"{scheme_lib_dir}:{out}", "--libexts", ".sls",
             "--program", str(use)],
            capture_output=True, text=True, timeout=300,
        )

    without = compile_and_run()
    assert without.returncode != 0
    assert "arrow_name" in without.stdout + without.stderr

    with_import = compile_and_run("--import", "(vhc hosts)")
    assert with_import.returncode == 0, with_import.stdout + with_import.stderr
    assert with_import.stdout == "1\n0\n"


def test_import_option_checks(ychr_bin, project_root, tmp_path):
    program, out = write_import_fixture(tmp_path)

    r = ychr_run(ychr_bin, project_root, "compile", "-t", "vm", "-d", str(out),
                 "--import", "(vhc hosts)", str(program))
    assert r.returncode != 0
    assert "only applies to -t scheme" in r.stderr

    for bad in ["vhc hosts", "(a", "(a) (b)", "(a \")\""]:
        r = ychr_run(ychr_bin, project_root, "compile", "-t", "scheme",
                     "-d", str(out), "--import", bad, str(program))
        assert r.returncode != 0, bad
        assert "is not an import spec" in r.stderr, bad

    # A paren inside a string doesn't count.
    r = ychr_run(ychr_bin, project_root, "compile", "-t", "scheme",
                 "-d", str(out), "--import", '(a ")")', str(program))
    assert r.returncode == 0, r.stdout + r.stderr

    r = ychr_run(ychr_bin, project_root, "gen-driver", "--import", "(a",
                 "-g", "h:c(host:arrow_name(), R)", str(program))
    assert r.returncode != 0
    assert "is not an import spec" in r.stderr

    r = ychr_run(ychr_bin, project_root, "gen-driver",
                 "--import", "(vhc hosts)", "--import", "(only (x y) z)",
                 "-g", "h:c(host:arrow_name(), R)", str(program))
    assert r.returncode == 0, r.stdout + r.stderr
    assert "(ychr generated program) (vhc hosts) (only (x y) z))" in r.stdout
    assert "(arrow_name)" in r.stdout

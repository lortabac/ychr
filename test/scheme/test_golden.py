"""Golden tests for the Scheme backend.

Each test directory under test/golden/ contains one or more .chr files
(compiled together) plus one or more <case>.goal/<case>.expected pairs.
For each case, this harness compiles the program to Scheme, generates a
driver script for the case's goal, runs it with guile3.0, and compares
the output against <case>.expected.

Negative tests (directories containing .error files) are skipped — the
Scheme harness only validates positive output.
"""

import glob
import os
import subprocess

import pytest

GOLDEN_DIR = os.path.join(os.path.dirname(__file__), "..", "golden")

# Test directories whose tests exercise Haskell-only meta-programming
# primitives and therefore cannot run on the Scheme backend.
HASKELL_ONLY = {
    # read_term_from_string is a stub on the Scheme runtime.
    "read_term_test",
    # write_store_to_list is a Haskell-only meta host call; no Scheme
    # implementation exists yet (parallels print_store).
    "write_store_to_list_test",
    # Variable-alias printing (A = B, B = A) is implemented in the
    # Haskell runtime only; the Scheme runtime still renders aliased
    # logical variables as `_`.
    "alias_print",
}

# Specific (test_dir, case_name) pairs to skip on Scheme. Used when only
# some cases in a directory diverge.
HASKELL_ONLY_CASES = {
    # `ground/1` reports a different answer for a partially-unbound
    # term in the Scheme backend.
    ("type_predicates", "grd_no"),
    # Scheme prints quoted atoms without quotes for non-ASCII content.
    ("unicode_atoms_strings", "quoted_with_space"),
    ("unicode_atoms_strings", "quoted_unicode"),
    ("unicode_atoms_strings", "quoted_chinese"),
    # Same quoting gap as above: '£foo' is an atom whose first char
    # ('£') is not alphanumeric, so Haskell quotes it; the Scheme
    # pretty-printer has no needsQuoting equivalent yet and prints
    # the bare form. The escape decoding the test exercises is shared
    # with the four passing siblings in the same directory.
    ("qualified_unicode_ctor", "pound_foo"),
}

# Test directories where the .chr program or goal deliberately uses
# bare atoms whose constructor the renamer cannot resolve — the warning
# is part of what the test exercises (cross-module visibility,
# canonicalization fallbacks), or the test uses bare sentinel atoms as
# RHS of `=` (where `term/1` no longer strips, per the spec). Mirrors
# `expectsWarnings` in test/YCHR/GoldenTest.hs. `--Werror` is omitted
# for these.
WERROR_EXEMPT = {
    "arity_overload",
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
    "typecheck_polymorphic_constraint",
    "typecheck_qualified_in_head",
    "unicode_atoms_strings",
    "unifiable",
}


def discover_cases():
    """Return sorted list of (test_dir, case_name) for all positive cases."""
    cases = []
    for entry in sorted(os.listdir(GOLDEN_DIR)):
        dir_path = os.path.join(GOLDEN_DIR, entry)
        if not os.path.isdir(dir_path):
            continue
        # Skip negative-test directories.
        if glob.glob(os.path.join(dir_path, "*.error")):
            continue
        for goal in sorted(glob.glob(os.path.join(dir_path, "*.goal"))):
            case_name = os.path.splitext(os.path.basename(goal))[0]
            cases.append((entry, case_name))
    return cases


@pytest.mark.parametrize("test_dir,case_name", discover_cases())
def test_scheme_golden(test_dir, case_name, ychr_bin, guile_bin, scheme_lib_dir, project_root, tmp_path):
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

    # 1. Compile to Scheme
    result = subprocess.run(
        [ychr_bin, "compile", *werror_flags, "-t", "scheme", "-d", str(tmp_path), *chr_files],
        capture_output=True,
        text=True,
        cwd=project_root,
    )
    assert result.returncode == 0, f"compile failed:\n{result.stdout}\n{result.stderr}"

    # 2. Generate driver
    result = subprocess.run(
        [ychr_bin, "gen-driver", *werror_flags, "-g", query, *chr_files],
        capture_output=True,
        text=True,
        cwd=project_root,
    )
    assert result.returncode == 0, f"gen-driver failed:\n{result.stdout}\n{result.stderr}"

    driver_path = tmp_path / "driver.sps"
    driver_path.write_text(result.stdout)

    # 3. Run with Guile
    result = subprocess.run(
        [
            guile_bin,
            "--r6rs",
            "--no-auto-compile",
            "-L", scheme_lib_dir,
            "-L", str(tmp_path),
            str(driver_path),
        ],
        capture_output=True,
        text=True,
        cwd=project_root,
    )
    assert result.returncode == 0, f"guile failed:\n{result.stdout}\n{result.stderr}"

    # 4. Compare output
    assert result.stdout == expected

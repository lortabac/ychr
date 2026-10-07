"""Verify type-checking behavior from the CLI: the checker's own source,
`--Werror` promotion, and the `--no-check` opt-out."""

import glob
import os

import pytest

# Golden directories whose programs compile and run, but whose type
# check reports an inaccessible branch (YCHR-20104). The golden harness
# only asserts the goal's bindings and merely *allows* the warning
# (`expectsWarnings` in test/YCHR/GoldenTest.hs), so without these cases
# the directories would still pass if the warning disappeared. Each
# entry pins the rendered message body; the source location is
# deliberately not asserted.
DEAD_CODE_GOLDENS = [
    (
        "refining_user_dead_rule",
        "a guard requires 'prelude:list(_)' where the type is"
        " 'refining_user_dead_rule:color'",
    ),
    (
        "typecheck_evidence_bool_rule",
        "a guard requires 'prelude:bool' where the type is"
        " 'typecheck_evidence_bool_rule:color'",
    ),
    (
        "typecheck_evidence_dead_rule",
        "a guard requires 'int' where the type is"
        " 'typecheck_evidence_dead_rule:color'",
    ),
    (
        "typecheck_list_pattern_dead",
        "a guard requires 'prelude:list(_)' where the type is 'int'",
    ),
    (
        "typecheck_open_function_dead_equation",
        "a guard requires 'int' where the type is 'string'",
    ),
    (
        "typecheck_qualified_in_head_dead",
        "a guard requires 'prelude:bool' where the type is 'int'",
    ),
    (
        "typecheck_shared_var_dead",
        "a guard requires 'int' where the type is 'string'",
    ),
]


# The type-checker checking itself. Its modules are compiled together
# as one program, so they are checked together too, and they must be
# fully annotated and warning-free: the embedded copy is compiled but
# never type-checked by the compile path, so this is the only thing
# holding the checker to its own type system.
def test_typecheck_typechecker(ychr_bin, project_root):
    import subprocess

    directory = os.path.join(project_root, "typechecker")
    files = sorted(glob.glob(os.path.join(directory, "*.chr")))
    assert files, "no typechecker sources found"
    result = subprocess.run(
        [ychr_bin, "check", "--Werror", *files],
        capture_output=True,
        text=True,
        cwd=project_root,
    )
    assert result.returncode == 0, (
        f"typechecker type check failed:\n"
        f"stdout:\n{result.stdout}\n"
        f"stderr:\n{result.stderr}"
    )


@pytest.mark.parametrize("test_dir,message", DEAD_CODE_GOLDENS)
def test_werror_inaccessible_branch(ychr_bin, project_root, test_dir, message):
    """`--Werror` promotes the inaccessible-branch warning to an error."""
    import subprocess

    directory = os.path.join(project_root, "test", "golden", test_dir)
    programs = sorted(glob.glob(os.path.join(directory, "*.chr")))
    assert programs, f"no .chr files in {directory}"

    plain = subprocess.run(
        [ychr_bin, "check", *programs],
        capture_output=True,
        text=True,
        cwd=project_root,
    )
    output = plain.stdout + plain.stderr
    assert plain.returncode == 0, f"expected a clean check:\n{output}"
    assert "YCHR-20104" in output, output
    assert message in output, output

    werror = subprocess.run(
        [ychr_bin, "check", "--Werror", *programs],
        capture_output=True,
        text=True,
        cwd=project_root,
    )
    assert werror.returncode != 0, "expected --Werror to fail the check"
    assert "YCHR-20104" in werror.stdout + werror.stderr


def test_dead_equation_attributed_to_extension(ychr_bin, project_root):
    """An `:- extend_function` equation's diagnostic points at the module
    that wrote it, not at the owning declaration's first equation.

    `owner:classify` is declared in `a_owner.chr`; the dead equation is
    the `:- extend_function classify("oops") -> 1.` directive in
    `b_extender.chr`. The warning must name `b_extender.chr`, echo that
    equation, and never mention `a_owner.chr`.
    """
    import subprocess

    directory = os.path.join(
        project_root, "test", "golden", "typecheck_open_function_dead_equation"
    )
    programs = sorted(glob.glob(os.path.join(directory, "*.chr")))
    assert programs, f"no .chr files in {directory}"

    result = subprocess.run(
        [ychr_bin, "check", *programs],
        capture_output=True,
        text=True,
        cwd=project_root,
    )
    output = result.stdout + result.stderr
    assert result.returncode == 0, f"expected a clean check:\n{output}"
    assert "YCHR-20104" in output, output

    # Exactly one warning, whose location line names the extension site.
    location_lines = [line for line in output.splitlines() if "YCHR-20104" in line]
    assert len(location_lines) == 1, output
    assert "b_extender.chr:14" in location_lines[0], output

    # The echoed source is the extension equation, not the owner's.
    assert 'classify("oops")' in output, output
    assert "a_owner.chr" not in output, output


def test_compile_error_attributed_to_extension(ychr_bin, tmp_path):
    """A *compile*-phase diagnostic from an `:- extend_function` equation
    is anchored at the extension site too, not only the type checker's.

    The extension equation `classify(X) -> Y` has an unbound `Y`, which
    the compiler reports as YCHR-40002. Before per-equation annotations
    were threaded into `Compile`, that error borrowed the owning
    declaration's source info and pointed at `a_owner.chr`'s
    `classify(0) -> 100`.
    """
    import subprocess

    owner = tmp_path / "a_owner.chr"
    owner.write_text(
        ":- module(owner, [classify/1]).\n"
        ":- open_function (classify(int) -> int).\n"
        "\n"
        "classify(0) -> 100.\n"
    )
    extender = tmp_path / "b_ext.chr"
    extender.write_text(
        ":- module(ext, [go/1]).\n"
        ":- use_module(owner, [classify/1]).\n"
        "\n"
        ":- chr_constraint go/1.\n"
        "\n"
        ":- extend_function classify(X) -> Y.\n"
        "\n"
        "go(R) <=> R is owner:classify(0).\n"
    )

    result = subprocess.run(
        [ychr_bin, "check", str(owner), str(extender)],
        capture_output=True,
        text=True,
        cwd=tmp_path,
    )
    output = result.stdout + result.stderr
    assert result.returncode != 0, output
    assert "YCHR-40002" in output, output

    location_lines = [line for line in output.splitlines() if "YCHR-40002" in line]
    assert len(location_lines) == 1, output
    assert "b_ext.chr" in location_lines[0], output

    # The echoed equation is the extension's, and the owner is not named.
    assert "classify(X) -> Y" in output, output
    assert "a_owner.chr" not in output, output


def test_duplicate_module_name_anchored_at_second_file(ychr_bin, tmp_path):
    """A header-less module's duplicate is reported against its real file.

    Header-less inputs are named `<basename>` and carry `dummyLoc`, so
    the diagnostic used to read `<generated>:1:1` with no file names.
    The input paths are now threaded to the duplicate check, which
    anchors at the second input and lists both. Header-less files with
    distinct basenames still combine.
    """
    import subprocess

    first = tmp_path / "d1"
    second = tmp_path / "d2"
    first.mkdir()
    second.mkdir()
    (first / "m.chr").write_text(":- function f/1.\nf(1) -> 1.\n")
    (second / "m.chr").write_text(":- function f/1.\nf(2) -> 2.\n")

    result = subprocess.run(
        [ychr_bin, "check", str(first / "m.chr"), str(second / "m.chr")],
        capture_output=True,
        text=True,
        cwd=tmp_path,
    )
    output = result.stdout + result.stderr
    assert result.returncode != 0, output
    assert "YCHR-10004" in output, output

    location_lines = [line for line in output.splitlines() if "YCHR-10004" in line]
    assert len(location_lines) == 1, output
    assert "d2" in location_lines[0] and "m.chr" in location_lines[0], output
    assert "generated" not in location_lines[0], output
    assert str(first / "m.chr") in output, output
    assert str(second / "m.chr") in output, output

    # Control: header-less files with distinct basenames still combine.
    (second / "n.chr").write_text(":- function g/1.\ng(1) -> 1.\n")
    combined = subprocess.run(
        [ychr_bin, "check", str(first / "m.chr"), str(second / "n.chr")],
        capture_output=True,
        text=True,
        cwd=tmp_path,
    )
    assert combined.returncode == 0, combined.stdout + combined.stderr


def test_werror_at_run(ychr_bin, project_root):
    """`--Werror` also gates `ychr run`, not just `ychr check`."""
    import subprocess

    program = os.path.join(
        project_root,
        "test",
        "golden",
        "typecheck_evidence_dead_rule",
        "typecheck_evidence_dead_rule.chr",
    )
    goal_file = os.path.join(
        project_root,
        "test",
        "golden",
        "typecheck_evidence_dead_rule",
        "typecheck_evidence_dead_rule.goal",
    )
    with open(goal_file) as handle:
        goal = handle.read().strip()

    plain = subprocess.run(
        [ychr_bin, "run", "-g", goal, program],
        capture_output=True,
        text=True,
        cwd=project_root,
    )
    assert plain.returncode == 0, f"expected the goal to run:\n{plain.stderr}"

    werror = subprocess.run(
        [ychr_bin, "run", "--Werror", "-g", goal, program],
        capture_output=True,
        text=True,
        cwd=project_root,
    )
    assert werror.returncode != 0, "expected --Werror to fail the run"
    assert "YCHR-20104" in werror.stdout + werror.stderr


# Every library in one invocation, `prelude` included. Each library is
# then present twice -- once as the source file on the command line, once
# as the embedded copy another library's `use_module(library(...))` pulls
# into the closure -- so this also pins the module deduplication in
# YCHR.Internal.Compile.Pipeline.finalizeCompilation. Without it every
# reference to a library's own exports is ambiguous (YCHR-20012).
def test_typecheck_stdlib(ychr_bin, project_root):
    import subprocess

    libraries = os.path.join(project_root, "libraries")
    files = sorted(glob.glob(os.path.join(libraries, "*.chr")))
    assert files, "no stdlib sources found"
    result = subprocess.run(
        [ychr_bin, "check", "--Werror", *files],
        capture_output=True,
        text=True,
        cwd=project_root,
    )
    assert result.returncode == 0, (
        f"stdlib type check failed:\n"
        f"stdout:\n{result.stdout}\n"
        f"stderr:\n{result.stderr}"
    )


# ---------------------------------------------------------------------------
# --no-check: skip the type checker entirely (program and goal checks)
# ---------------------------------------------------------------------------


def _run(ychr_bin, project_root, *args, stdin=None):
    """Run the CLI under the project root and return the completed process."""
    import subprocess

    return subprocess.run(
        [ychr_bin, *args],
        capture_output=True,
        text=True,
        cwd=project_root,
        input=stdin,
    )


def test_no_check_skips_program_check(ychr_bin, project_root, tmp_path):
    """`--no-check` runs, compiles and gen-drives an ill-typed program.

    `float_type_error` has a type error in a rule body (`int + float`),
    which the whole-program check reports as YCHR-60006. The flag skips
    that check, so the program goes through compile/run/gen-driver as if
    it were well-typed.
    """
    program = os.path.join(
        project_root,
        "test",
        "golden",
        "float_type_error",
        "float_type_error.chr",
    )
    goal = "result(1, 2)"

    plain_run = _run(ychr_bin, project_root, "run", "-g", goal, program)
    assert plain_run.returncode != 0, "expected the ill-typed program to fail"
    assert "YCHR-60006" in plain_run.stdout + plain_run.stderr

    checked_run = _run(ychr_bin, project_root, "run", "--no-check", "-g", goal, program)
    assert checked_run.returncode == 0, checked_run.stdout + checked_run.stderr

    plain_compile = _run(ychr_bin, project_root, "compile", "-d", str(tmp_path), program)
    assert plain_compile.returncode != 0, "expected the ill-typed program to fail"
    assert "YCHR-60006" in plain_compile.stdout + plain_compile.stderr

    out_dir = tmp_path / "out"
    out_dir.mkdir()
    checked_compile = _run(
        ychr_bin, project_root, "compile", "--no-check", "-d", str(out_dir), program
    )
    assert checked_compile.returncode == 0, checked_compile.stdout + checked_compile.stderr
    assert (out_dir / "program.vm").is_file()

    plain_driver = _run(ychr_bin, project_root, "gen-driver", "-g", goal, program)
    assert plain_driver.returncode != 0, "expected the ill-typed program to fail"
    assert "YCHR-60006" in plain_driver.stdout + plain_driver.stderr

    checked_driver = _run(ychr_bin, project_root, "gen-driver", "--no-check", "-g", goal, program)
    assert checked_driver.returncode == 0, checked_driver.stdout + checked_driver.stderr
    assert checked_driver.stdout.strip(), "expected a generated driver on stdout"


GOAL_CHECK_CASES = [
    ("typecheck_goal_arg_type", "tg:paint(42)", "YCHR-60001"),
    ("typecheck_goal_ctor_arity", "tgc:store(pair(1, 2, 3))", "YCHR-60008"),
]


@pytest.mark.parametrize("test_dir,goal,code", GOAL_CHECK_CASES)
def test_no_check_skips_goal_check(ychr_bin, project_root, test_dir, goal, code):
    """`--no-check` runs a goal the goal-level check would reject.

    Both programs are well-typed; only the goal is not. The rule behind
    it fires, so with the goal check skipped the run succeeds.
    """
    program = os.path.join(project_root, "test", "golden", test_dir, f"{test_dir}.chr")

    plain = _run(ychr_bin, project_root, "run", "-g", goal, program)
    assert plain.returncode != 0, "expected the goal check to reject the goal"
    assert code in plain.stdout + plain.stderr

    unchecked = _run(ychr_bin, project_root, "run", "--no-check", "-g", goal, program)
    assert unchecked.returncode == 0, unchecked.stdout + unchecked.stderr
    assert code not in unchecked.stdout + unchecked.stderr


def test_no_check_drops_type_warnings(ychr_bin, project_root):
    """Skipped checks produce no type warnings, so `--Werror` is appeased.

    `typecheck_evidence_dead_rule` is warning-only: `--Werror` fails the
    run. `--no-check` skips the warning too, so the same run passes.
    """
    directory = os.path.join(project_root, "test", "golden", "typecheck_evidence_dead_rule")
    program = os.path.join(directory, "typecheck_evidence_dead_rule.chr")
    with open(os.path.join(directory, "typecheck_evidence_dead_rule.goal")) as handle:
        goal = handle.read().strip()

    plain = _run(ychr_bin, project_root, "run", "--Werror", "-g", goal, program)
    assert plain.returncode != 0, "expected --Werror to reject the type warning"
    assert "YCHR-20104" in plain.stdout + plain.stderr

    unchecked = _run(ychr_bin, project_root, "run", "--no-check", "--Werror", "-g", goal, program)
    assert unchecked.returncode == 0, unchecked.stdout + unchecked.stderr
    assert "YCHR-20104" not in unchecked.stdout + unchecked.stderr


def test_no_check_in_repl(ychr_bin, project_root):
    """`repl --no-check` drops the load report and runs queries unchecked."""
    program = os.path.join(
        project_root,
        "test",
        "golden",
        "typecheck_goal_arg_type",
        "typecheck_goal_arg_type.chr",
    )
    stdin = "tg:paint(42).\n:quit\n"

    plain = _run(ychr_bin, project_root, "repl", "--quiet", program, stdin=stdin)
    assert plain.returncode == 0, plain.stdout + plain.stderr
    assert "YCHR-60001" in plain.stdout + plain.stderr

    unchecked = _run(
        ychr_bin, project_root, "repl", "--quiet", "--no-check", program, stdin=stdin
    )
    assert unchecked.returncode == 0, unchecked.stdout + unchecked.stderr
    assert "YCHR-60001" not in unchecked.stdout + unchecked.stderr

    ill_typed = os.path.join(
        project_root, "test", "golden", "float_type_error", "float_type_error.chr"
    )
    report = _run(ychr_bin, project_root, "repl", ill_typed, stdin=":quit\n")
    assert "YCHR-60006" in report.stdout + report.stderr

    no_report = _run(ychr_bin, project_root, "repl", "--no-check", ill_typed, stdin=":quit\n")
    assert "YCHR-60006" not in no_report.stdout + no_report.stderr


def test_no_check_only_on_auto_checking_commands(ychr_bin, project_root):
    """`check` keeps checking: it is the one command without `--no-check`."""
    program = os.path.join(project_root, "test", "golden", "leq", "leq.chr")
    rejected = _run(ychr_bin, project_root, "check", "--no-check", program)
    assert rejected.returncode != 0, "expected `check --no-check` to be rejected"

    for command in ("run", "compile", "gen-driver", "repl"):
        help_output = _run(ychr_bin, project_root, command, "--help")
        assert "--no-check" in help_output.stdout + help_output.stderr

    check_help = _run(ychr_bin, project_root, "check", "--help")
    assert "--no-check" not in check_help.stdout + check_help.stderr


def test_no_check_is_not_a_compile_escape_hatch(ychr_bin, project_root, tmp_path):
    """`--no-check` skips the checker only: compilation errors still fail."""
    program = os.path.join(
        project_root,
        "test",
        "golden",
        "constraint_has_equations",
        "constraint_has_equations.chr",
    )
    result = _run(ychr_bin, project_root, "compile", "--no-check", "-d", str(tmp_path), program)
    assert result.returncode != 0, "expected the compile error to survive --no-check"
    assert "YCHR-16001" in result.stdout + result.stderr

"""Verify that the type checker CHR program itself is well-typed."""

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

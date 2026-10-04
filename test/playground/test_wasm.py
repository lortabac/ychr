"""The playground bridge, exercised through the WASM module.

``playground/test/smoke.cjs`` loads ``playground/build/ychr-pg.js`` in
Node, calls the same exported functions the page calls, and prints one
JSON object per step. The assertions here are the shared ones from
:mod:`expectations`, so the browser bridge and the native bridge
(``test_native.py``) are held to the same responses.

The module must be built first::

    make playground-emsdk   # once
    make playground-wasm

The UTF-8 case in the shared scenario is the one that pins this
marshalling layer: ``newCString``/``peekCString`` are MicroHs's UTF-8
pair, and the 8-bit ``…AString`` pair would silently truncate any
character the compiler generates outside Latin-1.

When the module has not been built — the usual case, since that needs the
emscripten SDK — the test skips rather than failing.
"""

import json
import os
import shutil
import subprocess

import expectations
import pytest

BUILD_DIR = os.path.join(expectations.PROJECT_ROOT, "playground", "build")
MODULE = os.path.join(BUILD_DIR, "ychr-pg.js")
SMOKE = os.path.join(expectations.PROJECT_ROOT, "playground", "test", "smoke.cjs")

TIMEOUT = 3600


def require_wasm_module():
    if shutil.which("node") is None:
        pytest.skip("node is not available")
    if not os.path.exists(MODULE):
        pytest.skip("playground/build/ychr-pg.js not built (run `make playground-wasm`)")


@pytest.fixture(scope="module")
def steps():
    """Run the smoke script once: the module starts cold (and the first
    type check compiles the checker), so repeating it is expensive."""
    require_wasm_module()
    proc = subprocess.run(
        ["node", SMOKE, expectations.STARTER],
        capture_output=True,
        text=True,
        cwd=expectations.PROJECT_ROOT,
        timeout=TIMEOUT,
    )
    assert proc.returncode == 0, f"smoke.cjs failed:\n{proc.stdout}\n{proc.stderr}"
    collected = {}
    for line in proc.stdout.splitlines():
        line = line.strip()
        if not line.startswith("{"):
            continue
        record = json.loads(line)
        collected[record["step"]] = (record["status"], record["payload"])
    return collected


def test_scenario_in_wasm(steps):
    """The shared scenario passes on the WASM bridge."""
    assert "init" in steps, "the module never reported an init step"
    status, payload = steps["init"]
    assert status == "ok", payload
    expectations.check(steps)

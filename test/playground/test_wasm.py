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
import re
import shutil
import subprocess

import expectations
import pytest

BUILD_DIR = os.path.join(expectations.PROJECT_ROOT, "playground", "build")
MODULE = os.path.join(BUILD_DIR, "ychr-pg.js")
SMOKE = os.path.join(expectations.PROJECT_ROOT, "playground", "test", "smoke.cjs")
INDEX = os.path.join(expectations.PROJECT_ROOT, "playground", "index.html")

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
    """The shared scenario passes on the WASM bridge.

    That includes the four presets the page's dropdown offers: ``smoke.cjs``
    compiles each of them from its copy in the bundle.
    """
    assert "init" in steps, "the module never reported an init step"
    status, payload = steps["init"]
    assert status == "ok", payload
    expectations.check(steps)


def test_presets_are_bundled():
    """Each preset is in the bundle, byte-identical to its source.

    The page fetches ``build/<name>``; the copy step in ``make playground-wasm``
    is the only thing that puts it there, so this is what notices a bundled
    copy that stops matching the example it names.
    """
    require_wasm_module()
    for preset in expectations.PRESETS:
        bundled = os.path.join(BUILD_DIR, preset)
        assert os.path.exists(bundled), f"{preset} is not bundled; rebuild the module"
        with open(bundled, "rb") as f:
            bundled_bytes = f.read()
        assert os.path.exists(expectations.preset_path(preset))
        with open(expectations.preset_path(preset), "rb") as f:
            source_bytes = f.read()
        assert bundled_bytes == source_bytes, f"{preset} differs from examples/{preset}"


def test_menu_matches_presets():
    """The page's Examples menu lists exactly the presets the tests expect.

    Nothing else ties the options in ``index.html`` to ``PLAYGROUND_PRESETS`` in
    the Makefile and to :data:`expectations.PRESETS`: an option added to the
    page but not to the Makefile would 404 at runtime, and an option dropped
    from the page would leave a preset untested. Reading the markup is a blunt
    instrument, but it is the file the browser actually loads, and it needs no
    build.
    """
    with open(INDEX, encoding="utf-8") as f:
        markup = f.read()
    menu = re.search(
        r'<select id="preset".*?</select>',
        markup,
        re.DOTALL,
    )
    assert menu, "index.html has no preset select"
    listed = re.findall(r'<option value="([^"]*)"', menu.group(0))
    assert listed == [""] + expectations.PRESETS, listed

"""The scenario both playground front ends must answer identically.

The web playground has two ways in: the native harness
(``playground/Main.hs``) and the WASM module (``playground/build/ychr-pg.js``,
driven by ``playground/test/smoke.cjs``). Both go through the same engine,
``YCHR.Playground``, and this module is the single place the responses are
asserted — so a divergence between them is a test failure rather than
something only a browser would notice.

``SCENARIO`` is the ordered list of steps. Each step names the operation
the runner performs, not the command: the native runner turns it into
harness commands, the WASM runner into exported-function calls.
"""

import os

PROJECT_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))

#: The example the scenario reloads: the scenario also serves as a smoke
#: test for the playground's starter program, which is a copy of it.
STARTER = os.path.join(PROJECT_ROOT, "examples", "leq.chr")

#: A program that cannot compile. The point is that the previously loaded
#: program survives it.
BROKEN_SOURCE = "this is not a CHR program."

#: The example programs the page's preset dropdown offers, by file name under
#: ``examples/``, each with the reload summary its declarations produce. The
#: page is served from ``playground/`` alone, so ``make playground-wasm``
#: copies these five into ``playground/build/`` and the page fetches
#: ``build/<name>``: both the copies and the compile are asserted (here and in
#: ``test_wasm.py``), which is what keeps the copied files from drifting away
#: from their source in ``examples/``.
PRESET_SUMMARIES = {
    "bakery.chr": "Loaded 6 constraints: bake/0 cake/0 egg/0 flour/0 milk/0 sugar/0",
    "leq.chr": "Loaded 1 constraint: leq/2",
    "fib_memo.chr": "Loaded 2 constraints: fib/2 memo/2",
    "gcd.chr": "Loaded 1 constraint: gcd/1",
    "shortest_path.chr": "Loaded 3 constraints: edge/3 path/4 shortest_path/4",
}

PRESETS = list(PRESET_SUMMARIES)

#: The ordered scenario. ``op`` is one of:
#:
#: * ``compile-starter`` — compile ``examples/leq.chr`` (the page's starter)
#: * ``query``           — run one REPL line, given by ``arg``
#: * ``compile-broken``  — compile :data:`BROKEN_SOURCE`
#: * ``check``           — type-check the loaded program
#: * ``compile-preset``  — compile ``examples/<preset>``, given by ``preset``
SCENARIO = [
    {"label": "compile-starter", "op": "compile-starter"},
    {"label": "query-ground", "op": "query", "arg": "leq(1, 1)"},
    {"label": "query-bindings", "op": "query", "arg": "leq(X, 2)"},
    {"label": "query-list-modules", "op": "query", "arg": ":list_modules"},
    {"label": "query-info", "op": "query", "arg": ":info leq/2"},
    {"label": "query-unknown", "op": "query", "arg": "nope(1)"},
    # Non-ASCII text has to survive the C-string boundary in both
    # directions; the two front ends marshal it by different means (the
    # WASM bridge through UTF-8 C strings, the harness through GHC's
    # stdout encoding), so this is exactly the case worth pinning in the
    # shared table.
    {"label": "query-utf8", "op": "query", "arg": 'X = "café ☕"'},
    {"label": "compile-broken", "op": "compile-broken"},
    {"label": "query-after-failed-reload", "op": "query", "arg": "leq(1, 1)"},
    {"label": "check", "op": "check"},
    # Every preset the page offers compiles. These come last so that the
    # partial-order queries above still run against the program loaded at
    # startup.
] + [
    {"label": "preset-" + preset, "op": "compile-preset", "preset": preset}
    for preset in PRESETS
]


def preset_path(name):
    """The source of a preset, under ``examples/``."""
    return os.path.join(PROJECT_ROOT, "examples", name)


LABELS = [step["label"] for step in SCENARIO]


def native_commands():
    """The harness command lines that replay :data:`SCENARIO`.

    ``:load`` reads a file and @:text@ takes program text until a lone
    ``.``; everything else is one line.
    """
    commands = []
    for step in SCENARIO:
        if step["op"] == "compile-starter":
            commands.append(f":load {STARTER}")
        elif step["op"] == "compile-broken":
            commands.append(":text")
            commands.extend(BROKEN_SOURCE.splitlines())
            commands.append(".")
        elif step["op"] == "compile-preset":
            commands.append(f":load {preset_path(step['preset'])}")
        elif step["op"] == "query":
            commands.append(f":query {step['arg']}")
        elif step["op"] == "check":
            commands.append(":check")
        else:  # pragma: no cover - a typo in SCENARIO
            raise AssertionError(f"unknown op {step['op']!r}")
    return commands


def check(results):
    """Assert every response in :data:`SCENARIO`.

    ``results`` maps a label to a ``(status, payload)`` pair. Both runners
    produce that shape, so the assertions below are what pins the two front
    ends together. Extra entries are allowed: the WASM runner reports an
    ``init`` step that the harness does at startup.
    """

    missing = [label for label in LABELS if label not in results]
    assert not missing, f"missing steps: {missing}"

    def status(label):
        return results[label][0]

    def payload(label):
        return results[label][1]

    # A reload of the starter program reports the constraint it declares.
    assert status("compile-starter") == "ok", payload("compile-starter")
    assert "Loaded 1 constraint: leq/2" in payload("compile-starter"), payload(
        "compile-starter"
    )

    # A ground goal succeeds with no bindings; a goal with a free variable
    # prints it.
    assert status("query-ground") == "ok", payload("query-ground")
    assert status("query-bindings") == "ok", payload("query-bindings")
    assert "X =" in payload("query-bindings"), payload("query-bindings")

    # The colon commands are the terminal REPL's, rendered by the same code.
    assert status("query-list-modules") == "ok"
    assert "order" in payload("query-list-modules"), payload("query-list-modules")
    assert status("query-info") == "ok"
    # `:info` prints the qualified name and the declaration form.
    assert "order:leq" in payload("query-info"), payload("query-info")
    assert "chr_constraint leq" in payload("query-info"), payload("query-info")

    # An unknown constraint is a diagnostic, not a crash.
    assert status("query-unknown") == "error", payload("query-unknown")
    assert "Unknown name" in payload("query-unknown"), payload("query-unknown")

    # Non-ASCII text survives both marshalling layers.
    assert status("query-utf8") == "ok", payload("query-utf8")
    assert "café" in payload("query-utf8"), payload("query-utf8")
    assert "☕" in payload("query-utf8"), payload("query-utf8")

    # A reload that fails is reported, and leaves the previous program in
    # place — the REPL's `:recompile` policy.
    assert status("compile-broken") == "error", payload("compile-broken")
    assert status("query-after-failed-reload") == "ok", payload(
        "query-after-failed-reload"
    )

    # Type checking the (untyped) starter program finds nothing to report.
    assert status("check") == "ok", payload("check")

    # Every program the preset dropdown offers compiles, and reports the
    # constraint declarations the example under `examples/` has. The WASM
    # runner additionally checks that the bundled copies of these files are
    # byte-identical to their source (`test_wasm.py`), so a preset the page
    # offers cannot silently differ from the example it names.
    for preset, summary in PRESET_SUMMARIES.items():
        label = "preset-" + preset
        assert status(label) == "ok", payload(label)
        assert summary in payload(label), payload(label)

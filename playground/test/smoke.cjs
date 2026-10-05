/* Headless driver for the built WASM module.
 *
 * Loads playground/build/ychr-pg.js in Node, brings the MicroHs runtime
 * up with mhs_init(), and replays the operations the page performs,
 * printing one JSON object per step:
 *
 *     {"step": "query-bindings", "status": "ok", "payload": "X = 1.\n"}
 *
 * Exits non-zero when the module cannot be loaded, an export is missing,
 * or a response is not a well-formed envelope — the mechanical failures.
 * What the payloads *say* is asserted by test/playground/test_wasm.py,
 * which parses this output through the same expectation table the native
 * harness is checked against, so the two front ends stay in step: that
 * includes the four presets the page's dropdown offers, which have to
 * compile from the copies `make playground-wasm` puts in the bundle.
 *
 * Usage: node smoke.cjs <program-file>
 */

"use strict";

const fs = require("fs");
const path = require("path");

const BUILD_DIR = path.join(__dirname, "..", "build");
const MODULE_PATH = path.join(BUILD_DIR, "ychr-pg.js");

function emit(step, status, payload) {
  process.stdout.write(JSON.stringify({ step, status, payload }) + "\n");
}

function fail(message) {
  process.stderr.write("smoke: " + message + "\n");
  process.exit(1);
}

async function main() {
  if (!fs.existsSync(MODULE_PATH)) {
    fail("missing " + MODULE_PATH + " (run `make playground-wasm`)");
  }
  const programPath = process.argv[2];
  if (!programPath) {
    fail("usage: node smoke.cjs <program-file>");
  }

  const createYchr = require(MODULE_PATH);
  const Module = await createYchr({
    locateFile: (file) => path.join(BUILD_DIR, file),
  });

  Module._mhs_init();

  function invoke(name, arg) {
    if (typeof Module[name] !== "function") {
      fail("export " + name + " is missing from the module");
    }
    let inPtr = 0;
    let outPtr = 0;
    try {
      if (arg !== undefined) {
        inPtr = Module.stringToNewUTF8(arg);
      }
      outPtr = Module[name](inPtr);
      return Module.UTF8ToString(outPtr);
    } finally {
      if (outPtr) Module._ychr_pg_free(outPtr);
      if (inPtr) Module._free(inPtr);
    }
  }

  function step(label, name, arg) {
    const response = invoke(name, arg);
    const split = response.indexOf("\n\n");
    if (split < 0) {
      fail(label + ": response is not an envelope: " + JSON.stringify(response));
    }
    const status = response.slice(0, split);
    if (status !== "ok" && status !== "error") {
      fail(label + ": unknown status " + JSON.stringify(status));
    }
    emit(label, status, response.slice(split + 2));
  }

  const starter = fs.readFileSync(programPath, "utf8");

  /* The preset dropdown's programs. The page fetches `build/<name>`, which
     `make playground-wasm` copies from `examples/<name>`; compiling them here
     is what proves the bundle carries usable copies, not just that the copy
     step ran. The list mirrors the menu in index.html. */
  function readPreset(name) {
    const file = path.join(BUILD_DIR, name);
    if (!fs.existsSync(file)) {
      fail("missing preset " + file + " (run `make playground-wasm`)");
    }
    return fs.readFileSync(file, "utf8");
  }

  // The resource root: the preloaded directories are mounted at "/".
  step("init", "_ychr_pg_init", "/");
  step("compile-starter", "_ychr_pg_compile", starter);
  step("query-ground", "_ychr_pg_query", "leq(1, 1)");
  step("query-bindings", "_ychr_pg_query", "leq(X, 2)");
  step("query-list-modules", "_ychr_pg_query", ":list_modules");
  step("query-info", "_ychr_pg_query", ":info leq/2");
  step("query-unknown", "_ychr_pg_query", "nope(1)");
  step("query-utf8", "_ychr_pg_query", 'X = "café ☕"');
  // The loaded program must survive a reload that does not compile.
  step("compile-broken", "_ychr_pg_compile", "this is not a CHR program.");
  step("query-after-failed-reload", "_ychr_pg_query", "leq(1, 1)");
  // Builds the type checker on first call — the slow step.
  step("check", "_ychr_pg_check");
  for (const preset of ["bakery.chr", "leq.chr", "fib_memo.chr", "gcd.chr"]) {
    step("preset-" + preset, "_ychr_pg_compile", readPreset(preset));
  }

  console.log("smoke: ok");
}

main().catch((err) => fail(String(err && err.stack ? err.stack : err)));

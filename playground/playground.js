/* The YCHR playground front end.
 *
 * The whole page is one WASM module (playground/build/ychr-pg.js) built by
 * MicroHs + emscripten, plus the glue below. Five C entry points make up
 * the API; each takes and returns UTF-8 strings and answers with a
 * response envelope:
 *
 *     <status>\n\n<payload>          status is "ok" or "error"
 *
 * The payload is the text the CLI would have printed, colour included:
 * `displayMsg` emits ANSI SGR sequences, which `ansiToHtml` turns into
 * spans. Keeping the payload plain text means the browser and the terminal
 * REPL show byte-for-byte the same diagnostics.
 *
 * Every call blocks the browser for as long as the work takes, so each
 * action paints its status line first and then calls in.
 */

"use strict";

(function () {
  var STORAGE_KEY = "ychr-playground-program";

  var FALLBACK_PROGRAM = [
    "% The canonical CHR example: a less-or-equal solver.",
    ":- module(order, [leq/2]).",
    ":- chr_constraint leq/2.",
    "",
    "reflexivity   @ leq(X, X) <=> true.",
    "antisymmetry  @ leq(X, Y), leq(Y, X) <=> X = Y.",
    "idempotence   @ leq(X, Y) \\ leq(X, Y) <=> true.",
    "transitivity  @ leq(X, Y), leq(Y, Z) ==> leq(X, Z).",
    "",
  ].join("\n");

  var el = {
    program: document.getElementById("program"),
    output: document.getElementById("output"),
    input: document.getElementById("input"),
    form: document.getElementById("query-form"),
    reload: document.getElementById("reload"),
    typecheck: document.getElementById("typecheck"),
    status: document.getElementById("status"),
    bootError: document.getElementById("boot-error"),
  };

  var Module = null;
  var busy = false;
  var history = [];
  var historyIndex = 0;
  var checked = false;

  // -------------------------------------------------------------------------
  // Rendering
  // -------------------------------------------------------------------------

  function escapeHtml(text) {
    return text
      .replace(/&/g, "&amp;")
      .replace(/</g, "&lt;")
      .replace(/>/g, "&gt;");
  }

  var FG = {
    30: "fg-black",
    31: "fg-red",
    32: "fg-green",
    33: "fg-yellow",
    34: "fg-blue",
    35: "fg-magenta",
    36: "fg-cyan",
    37: "fg-white",
    90: "fg-black",
    91: "fg-red",
    92: "fg-green",
    93: "fg-yellow",
    94: "fg-blue",
    95: "fg-magenta",
    96: "fg-cyan",
    97: "fg-white",
  };

  /* Translate the SGR subset ychr emits (see YCHR.Internal.Display) into
     spans. Everything from an unknown escape is dropped; every other escape
     sequence is stripped so a stray one cannot leak into the page. */
  function ansiToHtml(text) {
    var html = "";
    var state = { color: null, bold: false, italic: false };
    var open = false;

    function closeSpan() {
      if (open) {
        html += "</span>";
        open = false;
      }
    }

    function openSpan() {
      var classes = [];
      if (state.color) classes.push(state.color);
      if (state.bold) classes.push("sgr-bold");
      if (state.italic) classes.push("sgr-italic");
      if (classes.length) {
        html += '<span class="' + classes.join(" ") + '">';
        open = true;
      }
    }

    function applySgr(params) {
      closeSpan();
      var codes = params === "" ? [0] : params.split(";").map(Number);
      codes.forEach(function (code) {
        if (code === 0) {
          state.color = null;
          state.bold = false;
          state.italic = false;
        } else if (code === 1) {
          state.bold = true;
        } else if (code === 3) {
          state.italic = true;
        } else if (code === 22) {
          state.bold = false;
        } else if (code === 23) {
          state.italic = false;
        } else if (code === 39) {
          state.color = null;
        } else if (FG[code] !== undefined) {
          state.color = FG[code];
        }
      });
      openSpan();
    }

    var i = 0;
    while (i < text.length) {
      var esc = text.indexOf("\u001b[", i);
      if (esc < 0) {
        html += escapeHtml(text.slice(i));
        break;
      }
      html += escapeHtml(text.slice(i, esc));
      // Only SGR sequences carry meaning here; a stray escape is dropped
      // rather than swallowing the text up to the next "m".
      var end = esc + 2;
      while (
        end < text.length &&
        (text[end] === ";" || (text[end] >= "0" && text[end] <= "9"))
      ) {
        end += 1;
      }
      if (text[end] === "m") {
        applySgr(text.slice(esc + 2, end));
        i = end + 1;
      } else {
        i = esc + 1;
      }
    }
    closeSpan();
    return html;
  }

  function appendBlock(echoText, payload, status) {
    var block = document.createElement("div");
    block.className = "block";
    var html = "";
    if (echoText) {
      html += '<div class="echo">' + escapeHtml(echoText) + "</div>";
    }
    if (payload) {
      html +=
        '<div class="payload ' +
        (status === "error" ? "error" : "") +
        '">' +
        ansiToHtml(payload) +
        "</div>";
    }
    block.innerHTML = html;
    el.output.appendChild(block);

    // Keep the DOM small on long sessions.
    while (el.output.childNodes.length > 400) {
      el.output.removeChild(el.output.firstChild);
    }
    el.output.scrollTop = el.output.scrollHeight;
  }

  function setStatus(text, kind) {
    el.status.textContent = text;
    el.status.className = "status" + (kind ? " " + kind : "");
  }

  function setBusy(value) {
    busy = value;
    el.reload.disabled = value;
    el.typecheck.disabled = value;
  }

  /* Give the browser a chance to paint `setStatus` before the blocking
     call freezes the thread. */
  function paint() {
    return new Promise(function (resolve) {
      requestAnimationFrame(function () {
        setTimeout(resolve, 0);
      });
    });
  }

  function bootError(message) {
    el.bootError.hidden = false;
    el.bootError.textContent = message;
    setStatus("unavailable", "error");
  }

  // -------------------------------------------------------------------------
  // The WASM bridge
  // -------------------------------------------------------------------------

  /* Call one exported function and read its response. `arg` is optional;
     the returned pointer is a malloc'd buffer we own, so it is freed here
     and never handed to the rest of the page. */
  function invoke(name, arg) {
    var inPtr = 0;
    var outPtr = 0;
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

  /* Split a response envelope into its status and payload. */
  function splitResponse(response) {
    var split = response.indexOf("\n\n");
    return split < 0
      ? { status: response, payload: "" }
      : { status: response.slice(0, split), payload: response.slice(split + 2) };
  }

  /* Show a response and reflect its status in the toolbar. */
  function show(echoText, result) {
    appendBlock(echoText, result.payload, result.status);
    var failed = result.status === "error";
    setStatus(failed ? "error" : "ready", failed ? "error" : "ok");
  }

  // -------------------------------------------------------------------------
  // Actions
  // -------------------------------------------------------------------------

  async function reload() {
    if (busy || !Module) return;
    setBusy(true);
    setStatus("compiling…", "busy");
    await paint();
    try {
      show(
        "--- Reload ---",
        splitResponse(invoke("_ychr_pg_compile", el.program.value))
      );
    } catch (err) {
      bootError("Reload failed: " + err);
    } finally {
      setBusy(false);
    }
  }

  /* Typecheck reloads first, so what is checked is always what the editor
     says — never a buffer that has been edited since the last reload. A
     reload that does not compile ends the action: the check would other-
     wise describe the program still loaded from before. */
  async function typecheck() {
    if (busy || !Module) return;
    setBusy(true);
    try {
      setStatus("reloading…", "busy");
      await paint();
      var compiled = splitResponse(invoke("_ychr_pg_compile", el.program.value));
      show("--- Reload ---", compiled);
      if (compiled.status === "error") {
        return;
      }

      setStatus(
        checked ? "type checking…" : "compiling the type checker (first run)…",
        "busy"
      );
      await paint();
      show("--- Typecheck ---", splitResponse(invoke("_ychr_pg_check")));
      checked = true;
    } catch (err) {
      bootError("Typecheck failed: " + err);
    } finally {
      setBusy(false);
    }
  }

  async function submit(line) {
    if (busy || !Module) return;
    if (line.trim() === "") return;
    history.push(line);
    historyIndex = history.length;
    setBusy(true);
    setStatus("running…", "busy");
    await paint();
    try {
      show("ychr> " + line, splitResponse(invoke("_ychr_pg_query", line)));
    } catch (err) {
      bootError("Query failed: " + err);
    } finally {
      setBusy(false);
    }
  }

  // -------------------------------------------------------------------------
  // Wiring
  // -------------------------------------------------------------------------

  function restoreProgram() {
    var stored = null;
    try {
      stored = window.localStorage.getItem(STORAGE_KEY);
    } catch (err) {
      // Private mode, or storage disabled: fall back to the bundled example.
    }
    if (stored) {
      el.program.value = stored;
      return;
    }
    fetch("./build/starter.chr")
      .then(function (response) {
        if (!response.ok) throw new Error("no starter");
        return response.text();
      })
      .then(function (text) {
        el.program.value = text;
      })
      .catch(function () {
        el.program.value = FALLBACK_PROGRAM;
      });
  }

  function persistProgram() {
    try {
      window.localStorage.setItem(STORAGE_KEY, el.program.value);
    } catch (err) {
      // Ignore: persistence is a convenience, not a requirement.
    }
  }

  el.form.addEventListener("submit", function (event) {
    event.preventDefault();
    var line = el.input.value;
    el.input.value = "";
    submit(line);
  });

  el.input.addEventListener("keydown", function (event) {
    if (event.key === "ArrowUp") {
      if (historyIndex > 0) {
        historyIndex -= 1;
        el.input.value = history[historyIndex];
        event.preventDefault();
      }
    } else if (event.key === "ArrowDown") {
      if (historyIndex < history.length - 1) {
        historyIndex += 1;
        el.input.value = history[historyIndex];
      } else {
        historyIndex = history.length;
        el.input.value = "";
      }
      event.preventDefault();
    }
  });

  el.reload.addEventListener("click", reload);
  el.typecheck.addEventListener("click", typecheck);
  el.program.addEventListener("input", persistProgram);
  el.program.addEventListener("keydown", function (event) {
    // Tab indents instead of leaving the editor: CHR programs are small,
    // and the browser's default focus change is never what you want here.
    if (event.key === "Tab") {
      event.preventDefault();
      var start = el.program.selectionStart;
      var end = el.program.selectionEnd;
      el.program.value =
        el.program.value.slice(0, start) + "  " + el.program.value.slice(end);
      el.program.selectionStart = el.program.selectionEnd = start + 2;
    }
  });

  restoreProgram();

  (async function boot() {
    if (typeof createYchr === "undefined") {
      bootError(
        "build/ychr-pg.js not found. Run `make playground-wasm`, then serve " +
          "this directory (`make playground-serve`) and reload."
      );
      return;
    }
    try {
      Module = await createYchr({
        locateFile: function (file) {
          return "./build/" + file;
        },
      });
      Module._mhs_init();
      show("--- init ---", splitResponse(invoke("_ychr_pg_init", "/")));
      setStatus("ready", "ok");
      el.input.focus();
    } catch (err) {
      bootError("Could not start the YCHR module: " + err);
    }
  })();
})();

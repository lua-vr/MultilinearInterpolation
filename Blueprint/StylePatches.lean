import VersoManual
import VersoBlueprint.PreviewManifest
import Blueprint.Index

open Verso Doc Output
open Verso.Genre Manual

open Verso.Output.Html in
def fontHead : Array Html := #[
  {{
    <style>
      "
      @font-face {
        font-family: 'JuliaMono';
        src: url('https://cdn.jsdelivr.net/gh/cormullion/juliamono/webfonts/JuliaMono-Regular.woff2') format('woff2');
        font-weight: normal;
        font-style: normal;
        font-display: swap;
      }
      @font-face {
        font-family: 'JuliaMono';
        src: url('https://cdn.jsdelivr.net/gh/cormullion/juliamono/webfonts/JuliaMono-Bold.woff2') format('woff2');
        font-weight: bold;
        font-style: normal;
        font-display: swap;
      }
      @font-face {
        font-family: 'JuliaMono';
        src: url('https://cdn.jsdelivr.net/gh/cormullion/juliamono/webfonts/JuliaMono-RegularItalic.woff2') format('woff2');
        font-weight: normal;
        font-style: italic;
        font-display: swap;
      }
      :root {
        --verso-code-font-family: 'JuliaMono', monospace;
        font-family: var(--verso-text-font-family);
      }
      "
    </style>
  }}
]

/--
Restyle blueprint statement blocks (theorem/lemma/definition/...) to match the
look of the Verso manual's `.namedocs` docstring boxes: a rounded `#98B2C0`
box with the kind + number heading at the top left and a rule above the body.
Scoped to the default "blueprint" style so the style switcher's "modern" and
"bold" options are unaffected. Pure CSS: the emitted block HTML is unchanged.
-/
def manualBoxCss : String := r##"
html:not([data-bp-style]) .bp_wrapper[class*="bp_kind_"],
html[data-bp-style="blueprint"] .bp_wrapper[class*="bp_kind_"] {
  position: relative;
  border: 1px solid #98B2C0;
  border-radius: 0.5rem;
  background: var(--bp-color-surface, #fff);
  padding: 0.5rem 0 0;
  margin-top: var(--verso--box-vertical-margin, 1.5rem);
  margin-bottom: var(--verso--box-vertical-margin, 1.5rem);
  box-shadow: none;
}

/* Keep the statement box visually attached to its code panel. */
html:not([data-bp-style]) .bp_wrapper[class*="bp_kind_"]:has(+ .bp_code_panel_wrapper),
html[data-bp-style="blueprint"] .bp_wrapper[class*="bp_kind_"]:has(+ .bp_code_panel_wrapper) {
  margin-bottom: 0.5rem;
}

/* Kind and number separated by a plain word space, not the upstream 11ch
   alignment column. */
html:not([data-bp-style]) .bp_heading_title_row_statement,
html[data-bp-style="blueprint"] .bp_heading_title_row_statement {
  display: inline-flex;
  align-items: baseline;
  column-gap: 0.3em;
}

/* Likewise in the "Lean code for ... [number]" panel summaries, where the
   label additionally carries the generic 0.5rem left margin. */
html:not([data-bp-style]) .bp_code_panel summary .bp_heading_title_row,
html[data-bp-style="blueprint"] .bp_code_panel summary .bp_heading_title_row {
  gap: 0.3em;
}

html:not([data-bp-style]) .bp_code_panel summary .bp_code_summary_label,
html[data-bp-style="blueprint"] .bp_code_panel summary .bp_code_summary_label {
  margin-left: 0;
}

/* No rule or extra gap under headings (also covers code-panel summaries). */
html:not([data-bp-style]) .bp_heading,
html[data-bp-style="blueprint"] .bp_heading {
  border-bottom: none;
  padding-bottom: 0;
}

/* Header strip: title at the left, extras at the right, all in flow. */
html:not([data-bp-style]) .bp_wrapper[class*="bp_kind_"] > .bp_heading,
html[data-bp-style="blueprint"] .bp_wrapper[class*="bp_kind_"] > .bp_heading {
  border-bottom: none;
  padding: 0 var(--verso--box-padding, 1rem) 0.5rem;
}

/* Body: separated by a rule, like `.namedocs .text`. */
html:not([data-bp-style]) .bp_wrapper[class*="bp_kind_"] > .bp_content,
html[data-bp-style="blueprint"] .bp_wrapper[class*="bp_kind_"] > .bp_content {
  display: flow-root;
  border-top: 1px solid #98B2C0;
  border-left: 0;
  margin-top: 0;
  padding: 0 var(--verso--box-padding, 1rem);
}

html:not([data-bp-style]) .bp_wrapper[class*="bp_kind_"] > .bp_content > :first-child,
html[data-bp-style="blueprint"] .bp_wrapper[class*="bp_kind_"] > .bp_content > :first-child {
  margin-top: var(--verso--box-padding, 1rem);
}

html:not([data-bp-style]) .bp_wrapper[class*="bp_kind_"] > .bp_content > :last-child,
html[data-bp-style="blueprint"] .bp_wrapper[class*="bp_kind_"] > .bp_content > :last-child {
  margin-bottom: var(--verso--box-padding, 1rem);
}

/* Match the code panel's chrome to the statement box. */
html:not([data-bp-style]) .bp_wrapper.bp_code_panel_wrapper,
html[data-bp-style="blueprint"] .bp_wrapper.bp_code_panel_wrapper {
  border-color: #98B2C0;
  border-radius: 0.5rem;
}

/* No accent left border on rendered declarations: make it match the other
   sides (this also overrides the 0.12rem narrow-screen variant). */
.bp_external_decl_rendered .declaration {
  border-left: var(--bp-box-border-width, 1px) solid
    var(--bp-box-border-color, var(--bp-color-border-soft));
}

/* ---- Flatten the verso-blueprint chrome: no gradients, no drop shadows. ----
   Functional box-shadow rings (focus outlines, :target highlights) are kept. */

:root {
  --bp-shadow-sm: none;
  --bp-shadow-md: none;
  --bp-shadow-lg: none;
  --bp-shadow-modern: none;
  --bp-shadow-bold: none;
  --bp-shadow-bold-lg: none;
}

.bp_code_hover,
.bp_external_status_icon,
.bp_relation_axis_badge,
.bp_graft_side_by_side_boxed > * {
  box-shadow: none;
}

/* Hide the "●" glyph verso-blueprint renders inside the status badge circle;
   the circle's background color already conveys the status. */
.bp_external_status_icon {
  font-size: 0;
}

.bp_code_progress {
  background: var(--bp-color-surface-muted);
  box-shadow: none;
}

.bp_code_summary_preview_header,
.bp_relation_panel_header,
.bp_relation_preview_header {
  background: var(--bp-color-surface-muted);
}

.bp_external_badge {
  background: var(--bp-color-surface);
}

.bp_decl_target_block {
  background: var(--bp-color-selection-surface-soft);
}

.bp_code_panel .bp_external_decl_rendered .declaration {
  --bp-box-header-background: var(--bp-color-surface-muted);
  --bp-box-shadow: none;
}

html[data-bp-style="modern"] .bp_wrapper,
html[data-bp-style="bold"] .bp_wrapper {
  background: var(--bp-color-surface);
  box-shadow: none;
}
"##

/--
Fold the "Lean code for ..." panels by default.

Upstream, `verso.blueprint.foldCodeBlocks` has no effect on the graft render
path: `PreviewManifest/BlockRender.lean`'s `renderCodePanel` calls
`Informal.mkCodePanel` without its `folded` argument, so the panels are always
emitted with `open="open"`. Until that is fixed upstream, strip the attribute
client-side on load. A panel containing the URL's `#target` is left open, and
the CSS guard below avoids a flash of open panels while the page parses.
-/
def foldCodePanelsJs : String := r##"(function () {
  document.documentElement.classList.add("bp-fold-code-init");
  document.addEventListener("DOMContentLoaded", function () {
    var target = null;
    if (location.hash) {
      try {
        target = document.getElementById(decodeURIComponent(location.hash.slice(1)));
      } catch (_err) {}
    }
    document.querySelectorAll("details.bp_code_panel[open]").forEach(function (panel) {
      if (target && panel.contains(target)) return;
      panel.removeAttribute("open");
    });
    document.documentElement.classList.remove("bp-fold-code-init");
  });
})();
"##

def foldCodePanelsCss : String := r##"
html.bp-fold-code-init details.bp_code_panel[open] > :not(summary) {
  display: none;
}
"##

/--
Show the Lean declaration name(s) in each statement block's heading pill.

The heading emitted by verso-blueprint only carries the kind and number
("Definition 2.1"); the Lean names are only present inside the adjacent
"Lean code for ..." panel, on the rendered declarations' `data-decl`
attributes. Since the block HTML comes from the upstream package, copy the
names into the heading client-side on load. The span is inserted after the
title row (not inside it: the statement title row is a fixed two-column
grid), so the heading's flex layout places it right of "Definition 2.1".
-/
def declNamesInHeadingJs : String := r##"(function () {
  document.addEventListener("DOMContentLoaded", function () {
    document.querySelectorAll('.bp_wrapper[class*="bp_kind_"]').forEach(function (block) {
      var panel = block.nextElementSibling;
      if (!panel || !panel.classList.contains("bp_code_panel_wrapper")) return;
      var heading = block.querySelector(":scope > .bp_heading");
      var row = heading && heading.querySelector(":scope > .bp_heading_title_row");
      if (!row || heading.querySelector(".bp_heading_decl_name")) return;
      var seen = {};
      var anchor = row;
      panel.querySelectorAll("[data-decl]").forEach(function (decl) {
        var name = decl.getAttribute("data-decl");
        if (!name || seen[name]) return;
        seen[name] = true;
        var span = document.createElement("span");
        span.className = "bp_heading_decl_name";
        span.textContent = name;
        anchor.insertAdjacentElement("afterend", span);
        anchor = span;
      });
    });
  });
})();
"##

def declNamesInHeadingCss : String := r##"
.bp_heading_decl_name {
  font-family: var(--verso-code-font-family, monospace);
  font-size: 0.85em;
  font-weight: normal;
  color: var(--bp-color-text-muted, #555);
}
"##

open Verso.Output.Html in
def manualBoxHead : Array Html := #[
  {{ <style> {{ Verso.Output.Html.text false manualBoxCss }} </style> }},
  {{ <style> {{ Verso.Output.Html.text false foldCodePanelsCss }} </style> }},
  {{ <script> {{ Verso.Output.Html.text false foldCodePanelsJs }} </script> }},
  {{ <style> {{ Verso.Output.Html.text false declNamesInHeadingCss }} </style> }},
  {{ <script> {{ Verso.Output.Html.text false declNamesInHeadingJs }} </script> }}
]

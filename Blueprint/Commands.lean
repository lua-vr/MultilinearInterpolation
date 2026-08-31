import VersoManual
import VersoBlueprint

/-!
Project-local Verso block commands for the blueprint.
-/

open Lean
open Verso Doc Elab ArgParse

namespace Blueprint

/-- Per-node rendering options shared by the batch graft commands. -/
structure NodeRenderOptions where
  facet : Option String := none
  compact : Bool := false
  showHeader : Bool := true

structure BlueprintNodesConfig extends NodeRenderOptions where
  labelPrefix : String

structure BlueprintNodesInConfig extends NodeRenderOptions where
  «namespace» : Name

meta def nodeRenderOptionsFromArgs : ArgParse DocElabM NodeRenderOptions :=
  NodeRenderOptions.mk <$>
    .named `facet .string true <*>
    .flag `compact false <*>
    .flag `header true

meta instance : FromArgs BlueprintNodesConfig DocElabM where
  fromArgs :=
    (fun labelPrefix opts => { opts with labelPrefix }) <$>
      .positional `prefix .string <*>
      nodeRenderOptionsFromArgs

meta instance : FromArgs BlueprintNodesInConfig DocElabM where
  fromArgs :=
    (fun ns opts => { opts with «namespace» := ns }) <$>
      .positional `namespace .name <*>
      nodeRenderOptionsFromArgs

/--
Position of each attribute-owned label as (module import order, position within
module), so grafted nodes can follow their source order.
-/
private meta def attributeLabelPositions (env : Environment)
    (state : Informal.Environment.State) : Lean.NameMap (Nat × Nat) := Id.run do
  let moduleIdx : Lean.NameMap Nat :=
    env.header.moduleNames.zipIdx.foldl (init := {}) fun acc (name, idx) =>
      acc.insert name idx
  let mut positions : Lean.NameMap (Nat × Nat) := {}
  for (moduleName, labels) in state.blueprintAttributeLabelsByModule do
    let modPos := moduleIdx.getD moduleName env.header.moduleNames.size
    for (label, pos) in labels.zipIdx do
      positions := positions.insert label (modPos, pos)
  return positions

/--
Graft every Blueprint node selected by {lit}`pred`, in source order.
{lit}`selectionDescription` is used for the empty-selection warning.
-/
meta def graftSelectedNodes (opts : NodeRenderOptions)
    (selectionDescription : String)
    (pred : String → Informal.Data.Node → Bool) : DocElabM Term := do
  let env ← getEnv
  let state := Informal.Environment.informalExt.getState env
  let positions := attributeLabelPositions env state
  let sortKey (label : Name) (labelStr : String) (node : Informal.Data.Node) :
      Nat × Nat × Nat × String :=
    match positions.get? label with
    | some (modPos, pos) => (modPos, pos, node.count, labelStr)
    | none => (env.header.moduleNames.size + 1, 0, node.count, labelStr)
  let matching := state.data.toArray.filterMap fun (label, node) =>
    match label with
    | .str .anonymous s =>
      if pred s node then some (s, sortKey label s node) else none
    | _ => none
  let keyLt : Nat × Nat × Nat × String → Nat × Nat × Nat × String → Bool :=
    fun (a1, a2, a3, a4) (b1, b2, b3, b4) =>
      a1 < b1 || (a1 == b1 &&
        (a2 < b2 || (a2 == b2 &&
          (a3 < b3 || (a3 == b3 && a4 < b4)))))
  let matching := matching.qsort fun a b => keyLt a.2 b.2
  if matching.isEmpty then
    logWarning m!"No Blueprint nodes matching {selectionDescription}"
  let blocks ← matching.mapM fun (label, _) =>
    Informal.Graft.blueprintNodeBlock {
      label
      facet := opts.facet
      compact := opts.compact
      showHeader := opts.showHeader
    }
  ``(Verso.Doc.Block.concat #[$blocks,*])

end Blueprint

namespace Blueprint

-- Inline note: its contents are rendered in red.
inline_extension Inline.note where
  usePackages := ["xcolor"]
  traverse _id _data _contents := pure none
  toTeX :=
    open Verso.Output.TeX in
    some <| fun go _id _data content => do
      let content ← content.mapM go
      pure <| .seq (#[.raw "\\textcolor{red}{"] ++ content ++ #[.raw "}"])
  toHtml :=
    open Verso.Output.Html in
    some <| fun go _id _data content => do
      pure {{ <span class="bp_note">{{← content.mapM go}}</span> }}
  extraCss := [
    r#"
.bp_note {
  color: var(--bp-note-color, #c62828);
}

.bp_note::before {
  content: "note: ";
}
"#
  ]

end Blueprint

open Blueprint in
/--
Inline note rendered in red: {lit}`{note}[needs a better bound]`.
-/
@[role]
meta def note : RoleExpanderOf Unit
  | (), contents => do
    ``(Verso.Doc.Inline.other Inline.note #[$[$(← contents.mapM elabInline)],*])

open Blueprint in
/--
Render every Blueprint node whose label starts with the given prefix, in
source order: {lit}`{blueprint_nodes "quasinorm-"}`.

Accepts the same {lit}`facet`, {lit}`compact` and {lit}`header` options as
{lit}`blueprint_node`, applied to each matched node.
-/
@[block_command]
meta def blueprint_nodes : BlockCommandOf BlueprintNodesConfig
  | cfg =>
    graftSelectedNodes cfg.toNodeRenderOptions s!"label prefix '{cfg.labelPrefix}'"
      fun label _node => label.startsWith cfg.labelPrefix

open Blueprint in
/--
Render every Blueprint node one of whose associated Lean declarations lives in
the given namespace, in source order: {lit}`{blueprint_nodes_in EQuasinorm}`.

Accepts the same {lit}`facet`, {lit}`compact` and {lit}`header` options as
{lit}`blueprint_node`, applied to each matched node.
-/
@[block_command]
meta def blueprint_nodes_in : BlockCommandOf BlueprintNodesInConfig
  | cfg =>
    graftSelectedNodes cfg.toNodeRenderOptions s!"namespace '{cfg.namespace}'"
      fun _label node => node.leanDecls.any fun decl => cfg.namespace.isPrefixOf decl

namespace Blueprint

/-- Options for {lit}`blueprint_decl`: like {lit}`blueprint_node`, but selecting the node by
declaration name rather than by label. -/
structure BlueprintDeclConfig extends NodeRenderOptions where
  decl : Name
  displayLabel : Option String := none
  siteBase : Option String := none

meta instance : FromArgs BlueprintDeclConfig DocElabM where
  fromArgs :=
    (fun decl displayLabel siteBase opts => { opts with decl, displayLabel, siteBase }) <$>
      .positional `decl .resolvedName <*>
      .named `displayLabel .string true <*>
      .named `siteBase .string true <*>
      nodeRenderOptionsFromArgs

/--
The label of the Blueprint node attached to {lit}`decl`.

Labels are always {name}`Lean.Name.mkSimple`-style single components, so the
match below recovers their string spelling.
-/
meta def labelForDecl (decl : Name) : DocElabM String := do
  match ← Informal.Environment.labelsForLeanDecl decl.eraseMacroScopes with
  | #[.str .anonymous label] => return label
  | #[] =>
    throwError "No Blueprint node is attached to '{decl}'; is the '@[blueprint]' attribute missing?"
  | labels =>
    throwError "'{decl}' takes part in several Blueprint nodes: \
      {labels}; select one with 'blueprint_node'"

end Blueprint

open Blueprint in
/--
Render a Blueprint node selected by the Lean declaration it documents:
{lit}`{blueprint_decl EQuasinorm.aokiRolewicz}`.

The identifier is resolved against the ambient {lit}`open` declarations and the
current namespace, and it is an error if no such declaration exists or if it has
no Blueprint node.

Accepts the same {lit}`facet`, {lit}`displayLabel`, {lit}`compact`,
{lit}`header` and {lit}`siteBase` options as {lit}`blueprint_node`.
-/
@[block_command]
meta def blueprint_decl : BlockCommandOf BlueprintDeclConfig
  | cfg => do
    Informal.Graft.blueprintNodeBlock {
      label := ← labelForDecl cfg.decl
      facet := cfg.facet
      displayLabel := cfg.displayLabel
      compact := cfg.compact
      showHeader := cfg.showHeader
      siteBase := cfg.siteBase
    }

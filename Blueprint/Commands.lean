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

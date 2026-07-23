import Lean
import VersoBlueprint

/-!
{lit}`@[blueprint_]` is like {lit}`@[blueprint "label"]`, except that the label
is the name of the declaration it is attached to.
-/

open Lean

namespace Informal

syntax (name := blueprint_) "blueprint_" (ppSpace blueprintAttrOption)* : attr

initialize
  registerBuiltinAttribute {
    name := `blueprint_
    ref := by exact decl_name%
    applicationTime := .afterCompilation
    add := fun decl stx kind => do
      let label := Syntax.mkStrLit decl.eraseMacroScopes.toString
      let stx ←
        match stx with
        | `(attr| blueprint_ $[$opts:blueprintAttrOption]*) =>
          `(attr| blueprint $label:str $[$opts:blueprintAttrOption]*)
        | _ => throwError "invalid syntax for '[blueprint_]' attribute"
      Attribute.add decl `blueprint stx kind
    descr := "Like '[blueprint]', with the declaration name as the node label"
  }

end Informal

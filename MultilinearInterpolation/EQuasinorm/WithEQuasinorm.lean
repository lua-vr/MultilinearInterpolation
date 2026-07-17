/-
Copyright (c) 2025 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/

import MultilinearInterpolation.EQuasinorm.Basic
import Carleson.ToMathlib.RealInterpolation.Misc
import VersoBlueprint

/-!
In this file, we define `WithEQuasinorm α A` for attaching instances related to
the `A : EQuasinorm α` to the type `α`.

I think we eventually want to upstream this as some API around `EQuasinorm`s for
Mathlib, so spaces like `Lp` would get an instance without `[Fact (1 ≤ p)]` as
well.
-/

def WithEQuasinorm (α : Type*) [AddMonoid α] (_ : EQuasinorm α) := α
  deriving AddMonoid

namespace WithEQuasinorm

instance {α} [AddMonoid α] {A} : ENorm (WithEQuasinorm α A) := A.enorm

instance {α} [AddGroup α] {A} : AddGroup (WithEQuasinorm α A) := inferInstanceAs (AddGroup α)


/- Topology. -/

noncomputable section Topology

variable {α : Type*} [AddGroup α] {A : EQuasinorm α}

instance : AddGroup (WithEQuasinorm α A) := inferInstanceAs (AddGroup α)

/- FIXME: here we want the group structure to be compatible in that ‖- x‖ = ‖x‖.
Otherwise there is no uniform structure. -/

instance : UniformSpace (WithEQuasinorm α A) :=
  .ofEdist A.C A.C_lt.ne (fun x y ↦ ‖x - y‖ₑ) (by simp)
    sorry
    sorry

end Topology


end WithEQuasinorm

/-
Copyright (c) 2025 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/

import MultilinearInterpolation.EQuasinorm.Basic
import VersoBlueprint

/-! In this file, we define the {lit}`finiteLocus` of an {name}`EQuasinorm`,
which is the submonoid of its finite elements. It is equipped with a seminorm,
and therefore has a sensible uniform structure and topology.
-/

open scoped ENNReal

namespace EQuasinorm

variable {α : Type*} [AddMonoid α] (A : EQuasinorm α)

/-- the submonoid of finite elements -/
def finiteLocus (A : EQuasinorm α) : AddSubmonoid α where
  carrier := { x | ‖x‖ₑ[A] < ∞ }
  zero_mem' := by simp
  add_mem' {x y} hx hy := by
    calc
      ‖x + y‖ₑ[A] ≤ A.C * (‖x‖ₑ[A] + ‖y‖ₑ[A]) := by apply enorm_add_le_mul
      _ < ∞ := by finiteness

namespace finiteLocus

instance : Norm A.finiteLocus := ⟨(‖·‖ₑ[A].toReal)⟩

/- FIXME: here we want the group structure to be compatible in that ‖- x‖ = ‖x‖.
Otherwise there is no group or uniform structure. -/

/- Topology. -/

noncomputable section Topology

variable {α : Type*} [AddGroup α] {A : EQuasinorm α}

-- instance : AddGroup (WithEQuasinorm α A) := inferInstanceAs (AddGroup α)

/- FIXME: here we want the group structure to be compatible in that ‖- x‖ = ‖x‖.
Otherwise there is no uniform structure. -/

-- instance : UniformSpace (WithEQuasinorm α A) :=
--   .ofEdist A.C A.C_lt.ne (fun x y ↦ ‖x - y‖ₑ) (by simp)
--     sorry
--     sorry

end Topology

end finiteLocus

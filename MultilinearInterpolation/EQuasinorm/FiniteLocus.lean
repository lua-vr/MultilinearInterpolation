/-
Copyright (c) 2026 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/

module

public import MultilinearInterpolation.EQuasinorm.Basic
import VersoBlueprint
meta import VersoBlueprint

/-! The {lit}`finiteLocus` of an {name}`EQuasinorm` is the submonoid of its finite elements. -/

@[expose] public section

open scoped ENNReal

namespace EQuasinorm

variable {α : Type*} [AddCommMonoid α] (A : EQuasinorm α)

/-- the submonoid of finite elements -/
def finiteLocus (A : EQuasinorm α) : AddSubmonoid α where
  carrier := { x | ‖x‖ₑ[A] < ∞ }
  zero_mem' := by simp
  add_mem' {x y} hx hy := by
    calc
      ‖x + y‖ₑ[A] ≤ A.C * (‖x‖ₑ[A] + ‖y‖ₑ[A]) := by apply enorm_add_le_mul
      _ < ∞ := by finiteness

namespace FiniteLocus

instance : Norm A.finiteLocus := ⟨(‖·‖ₑ[A].toReal)⟩

/- Let's not talk about topology.

But could define some uniformity by defining `dist a b` as the infimum of
`‖v‖ₑ + ‖w‖ₑ` such that `a + v = b + w`.
-/

end FiniteLocus

end EQuasinorm

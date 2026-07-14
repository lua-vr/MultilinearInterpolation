/-
Copyright (c) 2025 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/

import MultilinearInterpolation.Defs.EQuasinorm
import Carleson.ToMathlib.RealInterpolation.Misc
import VersoBlueprint

set_option verso.blueprint.autoDeps true

noncomputable section

open EQuasinorm
open scoped ENNReal NNReal

variable {ι : Type*} [Fintype ι] {M₁ : ι → Type*} [∀ i, AddMonoid (M₁ i)] {M₂ : Type*}
  [AddGroup M₂] [Lattice M₂]

/- I think it deserves this structure like `MultilinearMap`.
We may want to define API for operations on multisubadditive maps.
-/
variable (M₁ M₂) in
open Function in
structure MultisubadditiveMap where
  toFun : (∀ i, M₁ i) → M₂
  subadditive :
    ∀ [DecidableEq ι] (f : ∀ i, M₁ i) (i : ι) (x y : M₁ i),
    |toFun (update f i (x + y))| ≤ |toFun (update f i x)| + |toFun (update f i y)|

namespace MultisubadditiveMap

instance : FunLike (MultisubadditiveMap M₁ M₂) (∀ i, M₁ i) M₂ where
  coe f := f.toFun
  coe_injective f g h := by cases f; cases g; cases h; rfl

def IsBoundedFor (T : MultisubadditiveMap M₁ M₂)
    (e₁ : (i : ι) → EQuasinorm (M₁ i)) (e₂ : EQuasinorm M₂) (C : ℝ≥0) : Prop :=
  ∀ x, ‖T x‖ₑ[e₂] ≤ C * ∏ i, ‖x i‖ₑ[e₁ i]

end MultisubadditiveMap

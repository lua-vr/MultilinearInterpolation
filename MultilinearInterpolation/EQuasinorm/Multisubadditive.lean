/-
Copyright (c) 2025 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/

import MultilinearInterpolation.EQuasinorm.FiniteLocus
import Carleson.ToMathlib.RealInterpolation.Misc
import VersoBlueprint
import Verso
import VersoManual

/-!
Defines {lit}`MultiSubadditiveMap`s.
-/

open Verso.Genre Manual Informal InlineLean

noncomputable section

open EQuasinorm
open scoped ENNReal NNReal

variable {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, AddMonoid (α i)] {β : Type*} [AddMonoid β]

class Abs β where
  toFun : β → β

notation "|" e "|ₑ" => Abs.toFun e

variable [Abs β] [Preorder β]

/- I think it deserves this structure like `MultilinearMap`.
We may want to define API for operations on multisubadditive maps.
-/
variable (α β) in
open Function in
/-- A map $`f \colon ∏_i  α_i → β` that is subadditive in the sense that forall $`i \in ι`,
$$`|f(a_1, \dots, a_i + b_i, \dots, a_k)| ≤
|f(a_1, \dots, a_i, \dots, a_k)| + |f(a_1, \dots, b_i, \dots, a_k)|.`

For a function-valued $`f`, this should be the pointwise absolute value, not
the norm of the function, and the inequality above lives in $`β`. -/
@[blueprint "multisubadditivemap"]
structure MultisubadditiveMap where
  toFun : (∀ i, α i) → β
  subadditive :
    ∀ [DecidableEq ι] (f : ∀ i, α i) (i : ι) (x y : α i),
    |toFun (update f i (x + y))|ₑ ≤ |toFun (update f i x)|ₑ + |toFun (update f i y)|ₑ

namespace MultisubadditiveMap

instance : FunLike (MultisubadditiveMap α β) (∀ i, α i) β where
  coe f := f.toFun
  coe_injective f g h := by cases f; cases g; cases h; rfl

variable (T : MultisubadditiveMap α β) (A : (i : ι) → EQuasinorm (α i)) (B : EQuasinorm β)
  (C : ℝ≥0∞)

@[blueprint "IsBoundedFor"]
def IsBoundedFor : Prop :=
  C < ∞ ∧ ∀ x, ‖T x‖ₑ[B] ≤ C * ∏ i, ‖x i‖ₑ[A i]

/- Continuity-/

class SolidAbs (B : EQuasinorm β) : Prop where
  lt_top_iff {x : β} : ‖x‖ₑ[B] < ∞ ↔ ‖|x|ₑ‖ₑ[B] < ∞
  solid {x y : β} : |x|ₑ ≤ |y|ₑ → ‖x‖ₑ[B] ≤ ‖y‖ₑ[B]

instance (B : EQuasinorm β) [SolidAbs B] : Abs B.finiteLocus :=
  ⟨fun x ↦ ⟨|x.val|ₑ, SolidAbs.lt_top_iff.mp x.prop⟩⟩

namespace IsBoundedFor

variable [SolidAbs B] (C : ℝ≥0∞) (hT : T.IsBoundedFor A B C)

include hT in
def toFiniteLocus : MultisubadditiveMap (fun i ↦ (A i).finiteLocus) B.finiteLocus where
  toFun x := by
    use T (x · |>.val)
    apply hT.right (x · |>.val) |>.trans_lt
    apply ENNReal.mul_lt_top hT.left (ENNReal.prod_lt_top _)
    intro i _
    exact (x i).prop
  subadditive := sorry

-- lemma uniformContinuous (hT₂ : ContinuousAt hT.toFiniteLocus 0) :
--     UniformContinuous hT.toFiniteLocus :=
--   sorry

end IsBoundedFor

end MultisubadditiveMap

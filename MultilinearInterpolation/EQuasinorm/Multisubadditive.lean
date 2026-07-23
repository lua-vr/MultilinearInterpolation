/-
Copyright (c) 2025 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/

import MultilinearInterpolation.EQuasinorm.WithEQuasinorm
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

variable {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, AddMonoid (α i)] {β : Type*}
  [AddGroup β] [Lattice β]

/- I think it deserves this structure like `MultilinearMap`.
We may want to define API for operations on multisubadditive maps.
-/
variable (α β) in
open Function in
/-- A map $`f \colon ∏_i  α_i → β` that is subadditive in the sense that forall $`i \in ι`,
$$`|f(a_1, \dots, a_i + b_i, \dots, a_k)| ≤
|f(a_1, \dots, a_i, \dots, a_k)| + |f(a_1, \dots, b_i, \dots, a_k)|.`

For a function-valued $`f`, this should be the pointwise absolute value, not
the norm of the function, and the inequality above lives in $`β`. To make sense
of $`|·|`, we assume $`β` is a lattice and an additive group. -/
@[blueprint "multisubadditivemap"]
structure MultisubadditiveMap where
  toFun : (∀ i, α i) → β
  subadditive :
    ∀ [DecidableEq ι] (f : ∀ i, α i) (i : ι) (x y : α i),
    |toFun (update f i (x + y))| ≤ |toFun (update f i x)| + |toFun (update f i y)|

namespace MultisubadditiveMap

instance : FunLike (MultisubadditiveMap α β) (∀ i, α i) β where
  coe f := f.toFun
  coe_injective f g h := by cases f; cases g; cases h; rfl

variable (T : MultisubadditiveMap α β) (A : (i : ι) → EQuasinorm (α i)) (B : EQuasinorm β)
  (C : ℝ≥0∞)

@[blueprint "IsBoundedFor"]
def IsBoundedFor : Prop :=
  C ≠ ⊤ ∧ ∀ x, ‖T x‖ₑ[B] ≤ C * ∏ i, ‖x i‖ₑ[A i]

def withEQuasinorm :
    MultisubadditiveMap (fun i ↦ WithEQuasinorm (α i) (A i)) (WithEQuasinorm β B) :=
  T

namespace IsBoundedFor

variable {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, AddGroup (α i)] {β : Type*}
  [AddGroup β] [Lattice β]

variable (T : MultisubadditiveMap α β) (A : (i : ι) → EQuasinorm (α i)) (B : EQuasinorm β)
  (C : ℝ≥0∞)

lemma uniformContinuous (T : MultisubadditiveMap α β) (hT : T.IsBoundedFor A B C)
    (hT₂ : ContinuousAt (T.withEQuasinorm A B) 0) :
    UniformContinuous (T.withEQuasinorm A B) :=
  sorry

end IsBoundedFor

end MultisubadditiveMap

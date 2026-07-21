/-
Copyright (c) 2025 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/

import MultilinearInterpolation.EQuasinorm.WithEQuasinorm
import Carleson.ToMathlib.RealInterpolation.Misc
import VersoBlueprint

set_option verso.blueprint.autoDeps true

noncomputable section

open EQuasinorm
open scoped ENNReal NNReal

variable {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, AddGroup (α i)] {β : Type*}
  [AddGroup β] [Lattice β]

/- I think it deserves this structure like `MultilinearMap`.
We may want to define API for operations on multisubadditive maps.
-/
variable (α β) in
open Function in
structure MultisubadditiveMap where
  toFun : (∀ i, α i) → β
  subadditive :
    ∀ [DecidableEq ι] (f : ∀ i, α i) (i : ι) (x y : α i),
    |toFun (update f i (x + y))| ≤ |toFun (update f i x)| + |toFun (update f i y)|

namespace MultisubadditiveMap

instance : FunLike (MultisubadditiveMap α β) (∀ i, α i) β where
  coe f := f.toFun
  coe_injective f g h := by cases f; cases g; cases h; rfl

def IsBoundedFor (T : MultisubadditiveMap α β)
    (A : (i : ι) → EQuasinorm (α i)) (B : EQuasinorm β) (C : ℝ≥0∞) : Prop :=
  C ≠ ⊤ ∧ ∀ x, ‖T x‖ₑ[B] ≤ C * ∏ i, ‖x i‖ₑ[A i]

variable (T : MultisubadditiveMap α β) (A : (i : ι) → EQuasinorm (α i)) (B : EQuasinorm β)
  (C : ℝ≥0∞)

def withEQuasinorm :
    MultisubadditiveMap (fun i ↦ WithEQuasinorm (α i) (A i)) (WithEQuasinorm β B) :=
  T

namespace IsBoundedFor

lemma uniformContinuous (T : MultisubadditiveMap α β) (hT : T.IsBoundedFor A B C)
    (hT₂ : ContinuousAt (T.withEQuasinorm A B) 0) :
    UniformContinuous (T.withEQuasinorm A B) :=
  sorry

end IsBoundedFor

end MultisubadditiveMap

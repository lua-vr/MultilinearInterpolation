/-
Copyright (c) 2026 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/

module

public import MultilinearInterpolation.EQuasinorm.FiniteLocus
public import MultilinearInterpolation.Modulus

/-!
# Definition of {lit}`MultiSubadditiveMap`s.
-/

open Verso.Genre Manual Informal InlineLean

@[expose] public noncomputable section

open EQuasinorm
open scoped ENNReal NNReal

variable {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, AddCommMonoid (α i)] {β : Type*}
  [AddCommMonoid β]

variable {M : Type*} [AddCommMonoid M] [Preorder M] [Modulus β M]

/- I think it deserves this structure like `MultilinearMap`.
We may want to define API for operations on multisubadditive maps.
-/
variable (α β) in
open Function in
/-- A map $`f \colon ∏_i  α_i → β` that is subadditive in the sense that forall $`i \in ι`,
$$`|f(a_1, \dots, a_i + b_i, \dots, a_k)| ≤
|f(a_1, \dots, a_i, \dots, a_k)| + |f(a_1, \dots, b_i, \dots, a_k)|.`

Here $`|\cdot| \colon β → M` is the modulus; for a function-valued $`f` it is pointwise, not
the norm of the function, and the inequality above lives in $`M`. -/
@[blueprint]
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

section Solid

variable [Modulus.IsDecomposable β M] [DecidableEq ι] [B.IsSolid] (Bₛ : ESeminorm β)
  [Bₛ.toEQuasinorm.IsSolid] (f : ∀ i, α i) (i : ι) (x y : α i)

omit [Fintype ι]

open Function in
/-- {lit}`EQuasinorm.IsSolid.enorm_le_mul_of_modulus_le` applied to {lit}`subadditive`. -/
@[blueprint]
lemma enorm_update_add_le_mul :
    ‖T (update f i (x + y))‖ₑ[B] ≤
      B.C * (‖T (update f i x)‖ₑ[B] + ‖T (update f i y)‖ₑ[B]) :=
  IsSolid.enorm_le_mul_of_modulus_le (T.subadditive f i x y)

open Function in
/-- {lit}`enorm_update_add_le_mul` for an {lit}`ESeminorm`. -/
@[blueprint]
lemma enorm_update_add_le :
    ‖T (update f i (x + y))‖ₑ[Bₛ] ≤ ‖T (update f i x)‖ₑ[Bₛ] + ‖T (update f i y)‖ₑ[Bₛ] :=
  ESeminorm.enorm_le_of_modulus_le (T.subadditive f i x y)

end Solid

/-- A multisubadditive operator is bounded for quasinorms $`A_i`, $`B` and a finite constant $`C` on
a predicate $`P` if for all $`x = (x_i)_{i ∈ ι}` with $`P_i(x_i)` for all $`i`,
$$`\|T x\|_{B} ≤ C ∏_{i∈ ι} \|x_i\|_{A_i}.`
Since $`0 · ∞ = 0` in $`[0,∞]`, one usually wants $`P_i` to imply $`\|x_i\|_{A_i} < ∞`. -/
@[blueprint]
def IsBoundedForOn (P : ∀ i, α i → Prop) : Prop :=
  C < ∞ ∧ ∀ x, (∀ i, P i (x i)) → ‖T x‖ₑ[B] ≤ C * ∏ i, ‖x i‖ₑ[A i]

/-- The operator $`T` is bounded if, and only if, it is bounded between the
same quasinorms raised to a common power. -/
@[blueprint]
lemma isBoundedForOn_iff_isBoundedForOn_pow {p : ℝ} (hp : 0 < p) (P : ∀ i, α i → Prop) :
    T.IsBoundedForOn A B C P ↔ T.IsBoundedForOn (fun i ↦ (A i).pow hp) (B.pow hp) C P :=
  sorry

end MultisubadditiveMap

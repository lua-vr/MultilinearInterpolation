/-
Copyright (c) 2025 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jim Potergies, Michael Rothgang, Lua Viana Reis
-/

import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.WithDensity
import Blueprint.BlueprintAttr
import VersoBlueprint

/-!
Following
 *Interpolation Spaces, An Introduction* by  Jöran Bergh , Jörgen Löfström.
-/

noncomputable section

open ENNReal Set

variable {α : Type*} [AddMonoid α] {β : Type*} [AddMonoid β]

variable (α) in
/-- A quasinorm on a monoid $`α` is a function $`α → [0,∞]` and a finite constant
$`C` that sends $`0 : α` to zero and is $`C`-subadditive. -/
@[blueprint_]
structure EQuasinorm where
  /-- The raw {name}`enorm` associated to the quasinorm. -/
  protected enorm : ENorm α
  /-- The subadditivity constant. -/
  protected C : ℝ≥0∞
  /-- The subadditivity constant is finite. -/
  protected C_lt : C < ∞ := by finiteness
  /-- The enorm of zero is zero. -/
  protected enorm_zero : ‖(0 : α)‖ₑ = 0
  /-- The quasinorm is {lit}`C`-subadditive. -/
  enorm_add_le_mul : ∀ x y : α, ‖x + y‖ₑ ≤ C * (‖x‖ₑ + ‖y‖ₑ)

namespace EQuasinorm

attribute [simp] EQuasinorm.enorm_zero
attribute [aesop (rule_sets := [finiteness]) safe] EQuasinorm.C_lt max_lt

set_option quotPrecheck false in
notation "‖" e "‖ₑ[" A "]" => @enorm _ (A).enorm e

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Delaborate {lit}`@enorm _ A.enorm e` back to the notation {lit}`‖e‖ₑ[A]`. -/
@[app_delab enorm]
def delabEQuasinormEnorm : Delab := do
  let e ← getExpr
  guard <| e.isAppOfArity ``enorm 3
  guard <| e.appFn!.appArg!.isAppOfArity ``EQuasinorm.enorm 3
  let A ← withAppFn <| withAppArg <| withAppArg delab
  let x ← withAppArg delab
  `(‖$x‖ₑ[$A])

-- todo: make constant explicit
instance : LE (EQuasinorm α) :=
  ⟨fun A₀ A₁ => ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ x, ‖x‖ₑ[A₁] ≤ C * ‖x‖ₑ[A₀]⟩

instance : Preorder (EQuasinorm α) where
  le_refl A := ⟨1, by simp⟩
  le_trans A₀ A₁ A₂ := by
    intro ⟨C, h1C, h2C⟩ ⟨D, h1D, h2D⟩
    refine ⟨D * C, mul_lt_top h1D h1C, fun x ↦ ?_⟩
    calc ‖x‖ₑ[A₂] ≤ D * ‖x‖ₑ[A₁] := h2D x
      _ ≤ D * C * ‖x‖ₑ[A₀] := by
        rw [mul_assoc]
        gcongr
        apply h2C

-- the equivalence relation stating that two norms are equivalent
instance : Setoid (EQuasinorm α) := AntisymmRel.setoid _ (· ≤ ·)

-- Feel free to assume `θ ∈ Icc 0 1`, `1 ≤ q` and `q < ∞ → θ ∈ Ioo 0 1` whenever needed
variable {A A₀ A₁ A' A₀' A₁' : EQuasinorm α} {t s : ℝ≥0∞} {x y z : α} {θ : ℝ} {q : ℝ≥0∞}
  {B B₀ B₁ B' B₀' B₁' : EQuasinorm β} {C D : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞}

section Pow

@[blueprint_]
def pow (A : EQuasinorm α) (p : ℝ) : EQuasinorm α where
  enorm := ⟨fun x ↦ ‖x‖ₑ[A] ^ p⟩
  C := sorry
  C_lt := sorry
  enorm_zero := sorry
  enorm_add_le_mul x y := sorry

end Pow

/-- $`J(t,x)` in Section 3.2. For $`t = 1` this is the norm of $`A₀ ⊓ A₁`. -/
@[blueprint_]
def minNorm (A₀ A₁ : EQuasinorm α) (t : ℝ≥0∞) (x : α) : ℝ≥0∞ :=
  max ‖x‖ₑ[A₀] (t * ‖x‖ₑ[A₁])

/-- The minimum $`A₀ ⊓ A₁` equipped with the norm $`J(t,-)`. -/
@[simps, blueprint_]
def skewedMin (A₀ A₁ : EQuasinorm α) (t : ℝ≥0∞) : EQuasinorm α where
  enorm := ⟨minNorm A₀ A₁ t⟩
  C := max A₀.C A₁.C
  enorm_zero := by simp_rw [minNorm, EQuasinorm.enorm_zero, mul_zero, max_self]
  enorm_add_le_mul x y :=
    calc
      max ‖x + y‖ₑ[A₀] (t * ‖x + y‖ₑ[A₁]) ≤
        max (A₀.C * (‖x‖ₑ[A₀] + ‖y‖ₑ[A₀])) (A₁.C * (t * ‖x‖ₑ[A₁] + t * ‖y‖ₑ[A₁])) := by
          rw [← mul_add t, mul_left_comm A₁.C t]
          gcongr <;> apply enorm_add_le_mul
      _ ≤ max A₀.C A₁.C * max (‖x‖ₑ[A₀] + ‖y‖ₑ[A₀]) (t * ‖x‖ₑ[A₁] + t * ‖y‖ₑ[A₁]) :=
          max_mul_mul_le_max_mul_max'
      _ ≤ max A₀.C A₁.C * (minNorm A₀ A₁ t x + minNorm A₀ A₁ t y) := by
          gcongr
          exact max_add_add_le_max_add_max

instance : Min (EQuasinorm α) :=
  ⟨fun A₀ A₁ ↦ A₀.skewedMin A₁ 1⟩

lemma inf_mono (h₀ : A₀ ≤ A₀') (h₁ : A₁ ≤ A₁') : A₀ ⊓ A₁ ≤ A₀' ⊓ A₁' := by
  sorry

lemma inf_equiv_inf (h₀ : A₀ ≈ A₀') (h₁ : A₁ ≈ A₁') : A₀ ⊓ A₁ ≈ A₀' ⊓ A₁' :=
  ⟨inf_mono h₀.le h₁.le, inf_mono h₀.ge h₁.ge⟩

/-- $`K(t,x)` in Section 3.1. For $`t = 1` this is the norm of $`A₀ ⊔ A₁`. -/
@[blueprint_]
def maxNorm (A₀ A₁ : EQuasinorm α) (t : ℝ≥0∞) (x : α) : ℝ≥0∞ :=
  ⨅ (a : α × α) (_h : x = a.fst + a.snd), ‖a.fst‖ₑ[A₀] + t * ‖a.snd‖ₑ[A₁]

section MaxNorm

lemma maxNorm_le_of_decomp {x x₀ x₁ : α} (h : x = x₀ + x₁) (t : ℝ≥0∞) :
    A₀.maxNorm A₁ t x ≤ ‖x₀‖ₑ[A₀] + t * ‖x₁‖ₑ[A₁] :=
  iInf₂_le (x₀, x₁) h

lemma exists_decomp_lt_of_lt_maxNorm {x : α} {b : ℝ≥0∞} (h : A₀.maxNorm A₁ t x < b) :
    ∃ x₀ x₁, x = x₀ + x₁ ∧ ‖x₀‖ₑ[A₀] + t * ‖x₁‖ₑ[A₁] < b := by
  simpa [maxNorm, iInf_lt_iff] using h

@[simp, blueprint_]
lemma maxNorm_zero (t : ℝ≥0∞) : A₀.maxNorm A₁ t 0 = 0 := by
  simpa using maxNorm_le_of_decomp (add_zero (0 : α)).symm t

@[simp, blueprint_]
lemma maxNorm_add_le_mul (t : ℝ≥0∞) (x y : α) :
    A₀.maxNorm A₁ t (x + y) ≤ max A₀.C A₁.C * (A₀.maxNorm A₁ t x + A₀.maxNorm A₁ t y) := by
  suffices h : ∀ x₀ x₁, x = x₀ + x₁ → ∀ y₀ y₁, y = y₀ + y₁ →
      A₀.maxNorm A₁ t (x + y) ≤ max A₀.C A₁.C * ((‖x₀‖ₑ[A₀] + t * ‖x₁‖ₑ[A₁]) + (‖y₀‖ₑ[A₀] + t * ‖y₁‖ₑ[A₁])) by
    sorry
    -- apply ENNReal.le_iInf₂_add_iInf₂
    -- simpa only [Prod.forall] using h
  intro x₀ x₁ hx y₀ y₁ hy
  rw [add_add_add_comm, ← mul_add]
  trans ‖x₀ + x₁‖ₑ[A₀] + t * ‖x₁ + y₁‖ₑ[A₁]
  · sorry
  · sorry

end MaxNorm

/-- The addition `A₀ + A₁` equipped with the norm `K(t,-)` -/
@[blueprint_]
def skewedAdd (A₀ A₁ : EQuasinorm α) (t : ℝ≥0∞) : EQuasinorm α where
  enorm := ⟨maxNorm A₀ A₁ t⟩
  C := A₀.C + A₁.C -- maybe
  enorm_zero := by
    simp_rw [← nonpos_iff_eq_zero]
    apply iInf_le_of_le 0
    simp
  enorm_add_le_mul x y := by
    sorry

lemma skewedAdd_mono (h₀ : A₀ ≤ A₀') (h₁ : A₁ ≤ A₁') :
    skewedAdd A₀ A₁ t ≤ skewedAdd A₀' A₁' t := by
  sorry

lemma skewedAdd_equiv_skewedAdd (h₀ : A₀ ≈ A₀') (h₁ : A₁ ≈ A₁') :
    skewedAdd A₀ A₁ t ≈ skewedAdd A₀' A₁' t :=
  ⟨skewedAdd_mono h₀.le h₁.le, skewedAdd_mono h₀.ge h₁.ge⟩

instance : Max (EQuasinorm α) :=
  ⟨fun A₀ A₁ ↦ A₀.skewedAdd A₁ 1⟩

lemma max_mono (h₀ : A₀ ≤ A₀') (h₁ : A₁ ≤ A₁') : A₀ ⊔ A₁ ≤ A₀' ⊔ A₁' :=
  skewedAdd_mono h₀ h₁

lemma add_equiv_add (h₀ : A₀ ≈ A₀') (h₁ : A₁ ≈ A₁') : A₀ ⊔ A₁ ≈ A₀' ⊔ A₁' :=
  skewedAdd_equiv_skewedAdd h₀ h₁

-- Part of Lemma 3.1.1
-- assume t ≠ ∞ if needed
lemma monotone_addNorm (hx : ‖x‖ₑ[A₀ ⊔ A₁] < ∞) : Monotone (maxNorm A₀ A₁ · x) := by
  sorry

-- Part of Lemma 3.1.1 (if convenient: make the scalar ring `ℝ≥0`)
-- assume t ≠ ∞ if needed
lemma concave_addNorm (hx : ‖x‖ₑ[A₀ ⊔ A₁] < ∞) : ConcaveOn ℝ≥0∞ univ (maxNorm A₀ A₁ · x) := by
  sorry

-- Part of Lemma 3.1.1
-- assume s ≠ 0, s ≠ ∞, t ≠ ∞ if needed
-- probably this is more useful if reformulated without division
lemma addNorm_le_mul (hx : ‖x‖ₑ[A₀ ⊔ A₁] < ∞) :
    maxNorm A₀ A₁ t x ≤ max 1 (t / s) * maxNorm A₀ A₁ s x := by
  sorry

structure IsIntermediateSpace (A A₀ A₁ : EQuasinorm α) : Prop where
  inf_le : A₀ ⊓ A₁ ≤ A
  le_sup : A ≤ A₀ ⊔ A₁

namespace IsIntermediateSpace

protected lemma equiv (hI : IsIntermediateSpace A A₀ A₁) (h : A ≈ A') (h₀ : A₀ ≈ A₀') (h₁ : A₁ ≈ A₁') :
  IsIntermediateSpace A' A₀' A₁' where
    inf_le := inf_equiv_inf h₀ h₁ |>.ge.trans hI.inf_le |>.trans h.le
    le_sup := h.ge.trans hI.le_sup |>.trans <| add_equiv_add h₀ h₁ |>.le

end IsIntermediateSpace

-- Todo: find better name?
-- question: how do we get real interpolation with a.e.-subadditivity:
-- probably this works if we apply it to L^p-spaces (i.e. quotients of functions)
structure IsSubadditiveOn (T : α → β) (A : EQuasinorm α) (B : EQuasinorm β) (C D : ℝ≥0∞) :
    Prop where
  bounded : ∀ x, ‖T x‖ₑ[B] ≤ C * ‖x‖ₑ[A]
  subadditive : ∀ x y, ‖T (x + y)‖ₑ[B] ≤ D * (‖T x‖ₑ[B] + ‖T y‖ₑ[B])

-- `C = ‖T‖_{A, B}`
-- perhaps we don't have to let `C` and `D` depend on all other parameters.
structure AreInterpolationSpaces (A A₀ A₁ : EQuasinorm α) (B B₀ B₁ : EQuasinorm β)
    (C D : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞) : Prop where
  isIntermediateSpace_fst : IsIntermediateSpace A A₀ A₁
  isIntermediateSpace_snd : IsIntermediateSpace B B₀ B₁
  prop : ∀ C₀ D₀ C₁ D₁ (T : α → β), IsSubadditiveOn T A₀ B₀ C₀ D₀ → IsSubadditiveOn T A₁ B₁ C₁ D₁ →
    IsSubadditiveOn T A B (C C₀ D₀ C₁ D₁) (D C₀ D₀ C₁ D₁)

/-- `T` is of exponent `θ` w.r.t. constant `E` if `C ≤ E * C₀ ^ (1 - θ) * C₁ ^ θ` -/
def IsOfExponent (C : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞) (θ : ℝ) (E : ℝ≥0∞) : Prop :=
  ∀ C₀ D₀ C₁ D₁, C C₀ D₀ C₁ D₁ ≤ E * C₀ ^ (1 - θ) * C₁ ^ θ

/-- `T` is exact of exponent `θ` -/
def IsExactOfExponent (C : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞) (θ : ℝ) : Prop :=
  IsOfExponent C θ 1

/-- `T` is exact -/
def IsExact (C : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞) : Prop :=
  ∀ C₀ D₀ C₁ D₁, C C₀ D₀ C₁ D₁ ≤ max C₀ C₁


namespace AreInterpolationSpaces

protected lemma equiv (hI : AreInterpolationSpaces A A₀ A₁ B B₀ B₁ C D)
    (h : A ≈ A') (h₀ : A₀ ≈ A₀') (h₁ : A₁ ≈ A₁') (h' : B ≈ B') (h₀' : B₀ ≈ B₀') (h₁' : B₁ ≈ B₁') :
  AreInterpolationSpaces A' A₀' A₁' B' B₀' B₁' C D where
    isIntermediateSpace_fst := hI.isIntermediateSpace_fst.equiv h h₀ h₁
    isIntermediateSpace_snd := hI.isIntermediateSpace_snd.equiv h' h₀' h₁'
    prop := sorry

end AreInterpolationSpaces

variable (α) in
structure Couple where
  protected fst : EQuasinorm α
  protected snd : EQuasinorm α

namespace Couple

variable (A : Couple α)

abbrev J := minNorm A.fst A.snd

abbrev min := A.fst ⊓ A.snd

abbrev K := maxNorm A.fst A.snd

abbrev max := A.fst ⊔ A.snd

end Couple

end EQuasinorm

/-
Copyright (c) 2025 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jim Potergies, Michael Rothgang, Lua Viana Reis
-/

import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.WithDensity
import MultilinearInterpolation.ToMathlib.Topology.UniformSpace.OfFun

/-!
Following
 *Interpolation Spaces, An Introduction* by  Jöran Bergh , Jörgen Löfström.
-/

noncomputable section

open ENNReal Set

variable {𝓐 : Type*} [AddMonoid 𝓐] {𝓑 : Type*} [AddMonoid 𝓑]

variable (𝓐) in
structure EQuasinorm where
  protected enorm : ENorm 𝓐
  protected C : ℝ≥0∞
  protected C_lt : C < ∞ := by finiteness
  protected enorm_zero : ‖(0 : 𝓐)‖ₑ = 0
  enorm_add_le_mul : ∀ x y : 𝓐, ‖x + y‖ₑ ≤ C * (‖x‖ₑ + ‖y‖ₑ)

namespace EQuasinorm

attribute [simp] EQuasinorm.enorm_zero
attribute [aesop (rule_sets := [finiteness]) safe] EQuasinorm.C_lt max_lt

-- Todo: we need a delaborator for this.

set_option quotPrecheck false in
notation "‖" e "‖ₑ[" A "]" => @enorm _ (A).enorm e

-- todo: make constant explicit
instance : LE (EQuasinorm 𝓐) :=
  ⟨fun A₀ A₁ => ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ x, ‖x‖ₑ[A₁] ≤ C * ‖x‖ₑ[A₀]⟩

instance : Preorder (EQuasinorm 𝓐) where
  le_refl A := ⟨1, by simp⟩
  le_trans A₀ A₁ A₂ := by
    intro ⟨C, h1C, h2C⟩ ⟨D, h1D, h2D⟩
    refine ⟨D * C, mul_ne_top h1D h1C, fun x ↦ ?_⟩
    calc ‖x‖ₑ[A₂] ≤ D * ‖x‖ₑ[A₁] := h2D x
      _ ≤ D * C * ‖x‖ₑ[A₀] := by
        rw [mul_assoc]
        gcongr
        apply h2C

-- the equivalence relation stating that two norms are equivalent
instance : Setoid (EQuasinorm 𝓐) := AntisymmRel.setoid _ (· ≤ ·)

-- Feel free to assume `θ ∈ Icc 0 1`, `1 ≤ q` and `q < ∞ → θ ∈ Ioo 0 1` whenever needed
variable {A A₀ A₁ A' A₀' A₁' : EQuasinorm 𝓐} {t s : ℝ≥0∞} {x y z : 𝓐} {θ : ℝ} {q : ℝ≥0∞}
  {B B₀ B₁ B' B₀' B₁' : EQuasinorm 𝓑} {C D : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞}

-- variable [AddCommGroup 𝓐] in
-- abbrev topology (A : EQuasinorm 𝓐) : UniformSpace 𝓐 :=
--   .ofDist (fun x y ↦ ‖x - y‖ₑ[A]) dist_self dist_comm dist_triangle

/-- the submonoid of finite elements -/
def finiteElements (A : EQuasinorm 𝓐) : AddSubmonoid 𝓐 where
  carrier := { x | ‖x‖ₑ[A] < ∞ }
  zero_mem' := by simp
  add_mem' {x y} hx hy := by
    calc
      ‖x + y‖ₑ[A] ≤ A.C * (‖x‖ₑ[A] + ‖y‖ₑ[A]) := by apply enorm_add_le_mul
      _ < ∞ := by finiteness

example : ‖x + y‖ₑ[A] ≤ A.C * (‖x‖ₑ[A] + ‖y‖ₑ[A]) :=
  A.enorm_add_le_mul x y

/-- `J(t,x)` in Section 3.2. For `t = 1` this is the norm of `A₀ ⊓ A₁`. -/
def minNorm (A₀ A₁ : EQuasinorm 𝓐) (t : ℝ≥0∞) (x : 𝓐) : ℝ≥0∞ :=
  max ‖x‖ₑ[A₀] (t * ‖x‖ₑ[A₁])

/-- The minimum `A₀ ⊓ A₁` equipped with the norm `J(t,-)` -/
@[simps]
def skewedMin (A₀ A₁ : EQuasinorm 𝓐) (t : ℝ≥0∞) : EQuasinorm 𝓐 where
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

instance : Min (EQuasinorm 𝓐) :=
  ⟨fun A₀ A₁ ↦ A₀.skewedMin A₁ 1⟩

lemma inf_mono (h₀ : A₀ ≤ A₀') (h₁ : A₁ ≤ A₁') : A₀ ⊓ A₁ ≤ A₀' ⊓ A₁' := by
  sorry

lemma inf_equiv_inf (h₀ : A₀ ≈ A₀') (h₁ : A₁ ≈ A₁') : A₀ ⊓ A₁ ≈ A₀' ⊓ A₁' :=
  ⟨inf_mono h₀.le h₁.le, inf_mono h₀.ge h₁.ge⟩

/-- `K(t,x)` in Section 3.1. For `t = 1` this is the norm of `A₀ + A₁`. -/
def maxNorm (A₀ A₁ : EQuasinorm 𝓐) (t : ℝ≥0∞) (x : 𝓐) : ℝ≥0∞ :=
  ⨅ (a : 𝓐 × 𝓐) (_h : x = a.fst + a.snd), ‖a.fst‖ₑ[A₀] + t * ‖a.snd‖ₑ[A₁]

section MaxNorm

lemma maxNorm_le_of_decomp {x x₀ x₁ : 𝓐} (h : x = x₀ + x₁) (t : ℝ≥0∞) :
    A₀.maxNorm A₁ t x ≤ ‖x₀‖ₑ[A₀] + t * ‖x₁‖ₑ[A₁] :=
  iInf₂_le (x₀, x₁) h

lemma exists_decomp_lt_of_lt_maxNorm {x : 𝓐} {b : ℝ≥0∞} (h : A₀.maxNorm A₁ t x < b) :
    ∃ x₀ x₁, x = x₀ + x₁ ∧ ‖x₀‖ₑ[A₀] + t * ‖x₁‖ₑ[A₁] < b := by
  simpa [maxNorm, iInf_lt_iff] using h

@[simp]
lemma maxNorm_zero (t : ℝ≥0∞) : A₀.maxNorm A₁ t 0 = 0 := by
  simpa using maxNorm_le_of_decomp (add_zero (0 : 𝓐)).symm t

lemma maxNorm_add_le_mul (t : ℝ≥0∞) (x y : 𝓐) :
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
def skewedAdd (A₀ A₁ : EQuasinorm 𝓐) (t : ℝ≥0∞) : EQuasinorm 𝓐 where
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

instance : Max (EQuasinorm 𝓐) :=
  ⟨fun A₀ A₁ ↦ A₀.skewedAdd A₁ 1⟩

instance : Add (EQuasinorm 𝓐) :=
  ⟨fun A₀ A₁ ↦ A₀.skewedAdd A₁ 1⟩

lemma add_mono (h₀ : A₀ ≤ A₀') (h₁ : A₁ ≤ A₁') : A₀ + A₁ ≤ A₀' + A₁' :=
  skewedAdd_mono h₀ h₁

lemma add_equiv_add (h₀ : A₀ ≈ A₀') (h₁ : A₁ ≈ A₁') : A₀ + A₁ ≈ A₀' + A₁' :=
  skewedAdd_equiv_skewedAdd h₀ h₁

-- Part of Lemma 3.1.1
-- assume t ≠ ∞ if needed
lemma monotone_addNorm (hx : ‖x‖ₑ[A₀ + A₁] < ∞) : Monotone (maxNorm A₀ A₁ · x) := by
  sorry

-- Part of Lemma 3.1.1 (if convenient: make the scalar ring `ℝ≥0`)
-- assume t ≠ ∞ if needed
lemma concave_addNorm (hx : ‖x‖ₑ[A₀ + A₁] < ∞) : ConcaveOn ℝ≥0∞ univ (maxNorm A₀ A₁ · x) := by
  sorry

-- Part of Lemma 3.1.1
-- assume s ≠ 0, s ≠ ∞, t ≠ ∞ if needed
-- probably this is more useful if reformulated without division
lemma addNorm_le_mul (hx : ‖x‖ₑ[A₀ + A₁] < ∞) :
    maxNorm A₀ A₁ t x ≤ max 1 (t / s) * maxNorm A₀ A₁ s x := by
  sorry

structure IsIntermediateSpace (A A₀ A₁ : EQuasinorm 𝓐) : Prop where
  inf_le : A₀ ⊓ A₁ ≤ A
  le_add : A ≤ A₀ + A₁

namespace IsIntermediateSpace

protected lemma equiv (hI : IsIntermediateSpace A A₀ A₁) (h : A ≈ A') (h₀ : A₀ ≈ A₀') (h₁ : A₁ ≈ A₁') :
  IsIntermediateSpace A' A₀' A₁' where
    inf_le := inf_equiv_inf h₀ h₁ |>.ge.trans hI.inf_le |>.trans h.le
    le_add := h.ge.trans hI.le_add |>.trans <| add_equiv_add h₀ h₁ |>.le

end IsIntermediateSpace

-- Todo: find better name?
-- question: how do we get real interpolation with a.e.-subadditivity:
-- probably this works if we apply it to L^p-spaces (i.e. quotients of functions)
structure IsSubadditiveOn (T : 𝓐 → 𝓑) (A : EQuasinorm 𝓐) (B : EQuasinorm 𝓑) (C D : ℝ≥0∞) :
    Prop where
  bounded : ∀ x, ‖T x‖ₑ[B] ≤ C * ‖x‖ₑ[A]
  subadditive : ∀ x y, ‖T (x + y)‖ₑ[B] ≤ D * (‖T x‖ₑ[B] + ‖T y‖ₑ[B])

-- `C = ‖T‖_{A, B}`
-- perhaps we don't have to let `C` and `D` depend on all other parameters.
structure AreInterpolationSpaces (A A₀ A₁ : EQuasinorm 𝓐) (B B₀ B₁ : EQuasinorm 𝓑)
    (C D : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞) : Prop where
  isIntermediateSpace_fst : IsIntermediateSpace A A₀ A₁
  isIntermediateSpace_snd : IsIntermediateSpace B B₀ B₁
  prop : ∀ C₀ D₀ C₁ D₁ (T : 𝓐 → 𝓑), IsSubadditiveOn T A₀ B₀ C₀ D₀ → IsSubadditiveOn T A₁ B₁ C₁ D₁ →
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

variable (𝓐) in
structure Couple where
  protected fst : EQuasinorm 𝓐
  protected snd : EQuasinorm 𝓐

namespace Couple

variable (A : Couple 𝓐)

abbrev J := minNorm A.fst A.snd

abbrev min := A.fst ⊓ A.snd

abbrev K := maxNorm A.fst A.snd

abbrev max := A.fst ⊔ A.snd

end Couple

end EQuasinorm

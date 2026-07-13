/-
Copyright (c) 2025 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jim Potergies, Michael Rothgang, Lua Viana Reis
-/

import MultilinearInterpolation.Basic
import VersoBlueprint

set_option verso.blueprint.autoDeps true

/-!
Following
 *Interpolation Spaces, An Introduction* by  Jöran Bergh , Jörgen Löfström.
-/

noncomputable section

open ENNReal Set MeasureTheory
open scoped NNReal

variable {𝓐 : Type*} [AddMonoid 𝓐] {𝓑 : Type*} [AddMonoid 𝓑]

-- Feel free to assume `θ ∈ Icc 0 1`, `1 ≤ q` and `q < ∞ → θ ∈ Ioo 0 1` whenever needed
variable {A A₀ A₁ A' A₀' A₁' : QuasiENorm 𝓐} {t s : ℝ≥0∞} {x y z : 𝓐} {θ : ℝ} {q : ℝ≥0∞}
  {B B₀ B₁ B' B₀' B₁' : QuasiENorm 𝓑} {C D : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞}

namespace QuasiENorm

/-- The functional `Φ` in Section 3.1. Todo: better name. Todo: generalize type of `f`?
If we put a σ-algebra + measure on `ℝ≥0∞` we can get rid of the `ofReal`s. -/
def functional (θ : ℝ) (q : ℝ≥0∞) (f : ℝ≥0∞ → ℝ≥0∞) : ℝ≥0∞ :=
  eLpNorm ((Ioi 0).indicator fun t ↦ ENNReal.ofReal t ^ (- θ) * f (ENNReal.ofReal t)) q
    (volume.withDensity fun t ↦ (ENNReal.ofReal t)⁻¹)

/- ‖-‖_{θ, q, K} in Section 3.1. -/
def KNorm (A₀ A₁ : QuasiENorm 𝓐) (θ : ℝ) (q : ℝ≥0∞) (x : 𝓐) : ℝ≥0∞ :=
  functional θ q (maxNorm A₀ A₁ · x)

/-- The space K_{θ,q}(\bar{A}) in Section 3.1.
In the book, this is defined to only be submonoid of the elements with finite norm.
We could do that as well, but actually, since we allow for infinite norms, we can take all elements.
-/
def KMethod (A₀ A₁ : QuasiENorm 𝓐) (θ : ℝ) (q : ℝ≥0∞) : QuasiENorm 𝓐 where
  enorm := ⟨KNorm A₀ A₁ θ q⟩
  C := sorry
  C_lt := sorry
  enorm_zero := sorry
  enorm_add_le_mul := sorry

namespace Couple

variable (A : Couple 𝓐)

def knorm := KNorm A.fst A.snd

def kmethod := KMethod A.fst A.snd

end Couple

/-- The boundedness constant for the K-method. -/
def C_KMethod (θ : ℝ) (q C₀ D₀ C₁ D₁ : ℝ≥0∞) : ℝ≥0∞ := sorry

/-- The subadditivity constant for the K-method. -/
def D_KMethod (θ : ℝ) (q C₀ D₀ C₁ D₁ : ℝ≥0∞) : ℝ≥0∞ := sorry

/-- Theorem 3.1.2: The K-method in an interpolation functor. -/
lemma areInterpolationSpaces_kmethod : AreInterpolationSpaces
    (KMethod A₀ A₁ θ q) A₀ A₁ (KMethod B₀ B₁ θ q) B₀ B₁ (C_KMethod θ q) (D_KMethod θ q) := by
  sorry

/-- Part of Theorem 3.1.2 -/
lemma isExactOfExponent_kmethod : IsExactOfExponent (C_KMethod θ q) θ := by
  sorry

/-- The constant of inequality (6). -/
def γKMethod' (θ : ℝ) (q : ℝ≥0∞) : ℝ≥0∞ := sorry

/-- Part of Theorem 3.1.2 -/
lemma addNorm_le_knorm (hx : ‖x‖ₑ[A₀ + A₁] < ∞) :
    maxNorm A₀ A₁ t x ≤ γKMethod' θ q * t ^ θ * KNorm A₀ A₁ θ q x  := by
  sorry

-- Todo: ⊓, +, IsIntermediateSpace, AreInterpolationSpaces respect ≈

/-- Theorem 3.1.2: If intermediate spaces are equivalent to the ones obtained by the K-method,
then this gives rise to an interpolation space. -/
lemma areInterpolationSpaces_of_le_kmethod
    (hA : A ≈ KMethod A₀ A₁ θ q) (hB : B ≈ KMethod B₀ B₁ θ q) :
    AreInterpolationSpaces A A₀ A₁ B B₀ B₁ (C_KMethod θ q) (D_KMethod θ q) :=
  areInterpolationSpaces_kmethod.equiv hA.symm .rfl .rfl hB.symm .rfl .rfl


section DiscreteMethod

/-- The functional `Φ` in Section 3.1. Todo: better name. -/
def discreteFunctional (θ : ℝ) (q : ℝ≥0∞) (f : ℤ → ℝ≥0∞) : ℝ≥0∞ :=
  eLpNorm (fun (k : ℤ) ↦ 2 ^ (-k * θ) * f k) q Measure.count

/-- ‖-‖_{λ ^ {θ, q}} in Section 3.1. -/
def DiscreteKNorm (A₀ A₁ : QuasiENorm 𝓐) (θ : ℝ) (q : ℝ≥0∞) (x : 𝓐) : ℝ≥0∞ :=
  discreteFunctional θ q (fun k ↦ maxNorm A₀ A₁ (2 ^ k) x)

/-- The space K_{θ,q}(\bar{A}) in Section 3.1.
In the book, this is defined to only be submonoid of the elements with finite norm.
We could do that as well, but actually, since we allow for infinite norms, we can take all elements.
-/
@[blueprint "DiscreteKMethod"]
def DiscreteKMethod (A₀ A₁ : QuasiENorm 𝓐) (θ : ℝ) (q : ℝ≥0∞) : QuasiENorm 𝓐 where
  enorm := ⟨DiscreteKNorm A₀ A₁ θ q⟩
  C := sorry
  C_lt := sorry
  enorm_zero := sorry
  enorm_add_le_mul := sorry

/- Lemma 3.1.3. -/
@[blueprint "DiscreteKMethod_equiv_KMethod"]
lemma DiscreteKMethod_equiv_KMethod : DiscreteKMethod A₀ A₁ θ q ≈ KMethod A₀ A₁ θ q := by
  sorry

end DiscreteMethod

end QuasiENorm

/-
Copyright (c) 2026 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/

import MultilinearInterpolation.EQuasinorm.Basic
import VersoBlueprint

/-!
Following
 *Interpolation Spaces, An Introduction* by  Jöran Bergh , Jörgen Löfström,
 Section 3.1.
-/

noncomputable section

open Set MeasureTheory EQuasinorm
open scoped ENNReal NNReal

variable {α : Type*} [AddMonoid α] {β : Type*} [AddMonoid β]

-- Feel free to assume `θ ∈ Icc 0 1`, `1 ≤ q` and `q < ∞ → θ ∈ Ioo 0 1` whenever needed
variable {A A₀ A₁ A' A₀' A₁' : EQuasinorm α} {t s : ℝ≥0∞} {x y z : α} {θ : ℝ} {q : ℝ≥0∞}
  {B B₀ B₁ B' B₀' B₁' : EQuasinorm β} {C D : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞}

namespace EQuasinorm

namespace KMethod

/-- The functional
$$`Φ_{θ,q}(φ(t)) = ( ∫_0^∞ (t^{-θ} φ(t))^q dt/t )^{1/q}`
in Section 3.1. Todo: better name. Todo: generalize type of `f`?
If we put a σ-algebra + measure on `ℝ≥0∞` we can get rid of the `ofReal`s. -/
@[blueprint_]
def functional (θ : ℝ) (q : ℝ≥0∞) (f : ℝ≥0∞ → ℝ≥0∞) : ℝ≥0∞ :=
  eLpNorm ((Ioi 0).indicator fun t ↦ ENNReal.ofReal t ^ (- θ) * f (ENNReal.ofReal t)) q
    (volume.withDensity fun t ↦ (ENNReal.ofReal t)⁻¹)

/-- The space $`K_{θ,q}(\bar{A})` in Section 3.1.
In the book, this is defined to only be submonoid of the elements with finite norm.
We could do that as well, but actually, since we allow for infinite norms, we can take all elements.
-/
@[blueprint_]
def kmethod (A₀ A₁ : EQuasinorm α) (θ : ℝ) (q : ℝ≥0∞) : EQuasinorm α where
  enorm := ⟨fun x ↦ functional θ q (supNorm A₀ A₁ · x)⟩
  C := sorry
  C_lt := sorry
  enorm_zero := sorry
  enorm_add_le_mul := sorry

/-- The boundedness constant for the K-method. -/
def C_KMethod (θ : ℝ) (q C₀ D₀ C₁ D₁ : ℝ≥0∞) : ℝ≥0∞ := sorry

/-- The subadditivity constant for the K-method. -/
def D_KMethod (θ : ℝ) (q C₀ D₀ C₁ D₁ : ℝ≥0∞) : ℝ≥0∞ := sorry

-- /-- Theorem 3.1.2: The K-method in an interpolation functor. -/
-- lemma areInterpolationSpaces_kmethod : AreInterpolationSpaces
--     (KMethod A₀ A₁ θ q) A₀ A₁ (KMethod B₀ B₁ θ q) B₀ B₁ (C_KMethod θ q) (D_KMethod θ q) := by
--   sorry

-- /-- Part of Theorem 3.1.2 -/
-- lemma isExactOfExponent_kmethod : IsExactOfExponent (C_KMethod θ q) θ := by
--   sorry

/-- The constant of inequality (6). -/
def γKMethod' (θ : ℝ) (q : ℝ≥0∞) : ℝ≥0∞ := sorry

/-- Part of Theorem 3.1.2 -/
lemma addNorm_le_knorm (hx : ‖x‖ₑ[A₀ ⊔ A₁] < ∞) :
    supNorm A₀ A₁ t x ≤ γKMethod' θ q * t ^ θ * ‖x‖ₑ[kmethod A₀ A₁ θ q]  := by
  sorry

-- Todo: ⊓, +, IsIntermediateSpace, AreInterpolationSpaces respect ≈

-- /-- Theorem 3.1.2: If intermediate spaces are equivalent to the ones obtained by the K-method,
-- then this gives rise to an interpolation space. -/
-- lemma areInterpolationSpaces_of_le_kmethod
--     (hA : A ≈ KMethod A₀ A₁ θ q) (hB : B ≈ KMethod B₀ B₁ θ q) :
--     AreInterpolationSpaces A A₀ A₁ B B₀ B₁ (C_KMethod θ q) (D_KMethod θ q) :=
--   areInterpolationSpaces_kmethod.equiv hA.symm .rfl .rfl hB.symm .rfl .rfl


section Discrete

/-- The functional $`Φ` in Section 3.1. Todo: better name. -/
def discreteFunctional (θ : ℝ) (q : ℝ≥0∞) (f : ℤ → ℝ≥0∞) : ℝ≥0∞ :=
  eLpNorm (fun (k : ℤ) ↦ 2 ^ (-k * θ) * f k) q Measure.count

/-- The space $`K_{θ,q}(\bar{A})` in Section 3.1.
In the book, this is defined to only be submonoid of the elements with finite norm.
We could do that as well, but actually, since we allow for infinite norms, we can take all elements.
-/
@[blueprint_]
def discreteKMethod (A₀ A₁ : EQuasinorm α) (θ : ℝ) (q : ℝ≥0∞) : EQuasinorm α where
  enorm := ⟨fun x ↦ discreteFunctional θ q (fun k ↦ supNorm A₀ A₁ (2 ^ k) x)⟩
  C := sorry
  C_lt := sorry
  enorm_zero := sorry
  enorm_add_le_mul := sorry

/- Lemma 3.1.3. -/
@[blueprint_]
lemma discreteKMethod_equiv_kmethod : discreteKMethod A₀ A₁ θ q ≈ kmethod A₀ A₁ θ q := by
  sorry

end Discrete

end KMethod

namespace Couple

variable (A : Couple α)

def kmethod := KMethod.kmethod A.fst A.snd

end Couple

end EQuasinorm

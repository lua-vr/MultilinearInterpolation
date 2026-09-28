/-
Copyright (c) 2026 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jim Potergies, Michael Rothgang, Lua Viana Reis
-/

module

public import MultilinearInterpolation.EQuasinorm.Basic
public import MultilinearInterpolation.EQuasinorm.ESeminorm
import VersoBlueprint
meta import VersoBlueprint

/-!
Following *Interpolation Spaces, An Introduction* by Jöran Bergh and Jörgen Löfström, Section 3.1.
-/

@[expose] public noncomputable section

open Set MeasureTheory EQuasinorm
open scoped ENNReal NNReal

variable {α β : Type*} [AddCommMonoid α] {A₀ A₁ : EQuasinorm α}
  {t s : ℝ≥0∞} {x y z : α} {θ : ℝ} {q : ℝ≥0∞}

namespace EQuasinorm

/-- The functional
$$`Φ_{θ,q}(φ) = \left( ∫_0^∞ (t^{-θ} φ(t))^q dt/t \right)^{1/q}.`
-/
@[blueprint]
def phiFunctional (θ : ℝ) (q : ℝ≥0∞) (f : ℝ≥0∞ → ℝ≥0∞) : ℝ≥0∞ :=
  eLpNorm (fun (t : ℝ) ↦ t.toNNReal ^ (-θ) * f t.toNNReal) q
    (volume.withDensity (·.toNNReal⁻¹) |>.restrict (Ioi 0))

/-- The discrete version of {name}`phiFunctional`, defined as
$$`Φ_{θ,q}(φ) = \left( ∑_{k ∈ ℤ} (2^{-k θ} φ(k))^q \right)^{1/q}.`
-/
@[blueprint]
def discretePhiFunctional (θ : ℝ) (q : ℝ≥0∞) (f : ℤ → ℝ≥0∞) : ℝ≥0∞ :=
  eLpNorm (fun (k : ℤ) ↦ 2 ^ (-k * θ) * f k) q
    Measure.count

/-- The space $`K_{θ,q}(\bar{A})` in Section 3.1. -/
@[blueprint]
def kMethod (A₀ A₁ : EQuasinorm α) (θ : ℝ) (q : ℝ≥0∞) : EQuasinorm α where
  enorm := ⟨fun x ↦ phiFunctional θ q (kNorm A₀ A₁ · x)⟩
  C := sorry
  C_lt_top := sorry
  C_ge_one := sorry
  enorm_zero := sorry
  enorm_add_le_mul := sorry

section Discrete

/-- The discrete version of $`K_{θ,q}(\bar{A})`. -/
@[blueprint]
def discreteKMethod (A₀ A₁ : EQuasinorm α) (θ : ℝ) (q : ℝ≥0∞) : EQuasinorm α where
  enorm := ⟨fun x ↦ discretePhiFunctional θ q (fun k ↦ kNorm A₀ A₁ (2 ^ k) x)⟩
  C := sorry
  C_lt_top := sorry
  C_ge_one := sorry
  enorm_zero := sorry
  enorm_add_le_mul := sorry

/-- Lemma 3.1.3. -/
@[blueprint]
lemma discreteKMethod_equiv_kmethod : discreteKMethod A₀ A₁ θ q ≈ kMethod A₀ A₁ θ q := by
  sorry

end Discrete

namespace Couple

variable (A : Couple α)

abbrev kMethod := EQuasinorm.kMethod A.fst A.snd

abbrev discreteKMethod := EQuasinorm.discreteKMethod A.fst A.snd

end Couple

end EQuasinorm

namespace ESeminorm

/-- The {name}`EQuasinorm.kMethod` as an {name}`ESeminorm`. -/
@[blueprint
  (uses := [EQuasinorm.kMethod])]
def kMethod (A₀ A₁ : ESeminorm α) (θ : ℝ) (q : ℝ≥0∞) : ESeminorm α where
  __ := EQuasinorm.kMethod A₀ A₁ θ q
  C_eq_one := sorry

/-- The {name}`EQuasinorm.discreteKMethod` as an {name}`ESeminorm`. -/
@[blueprint
  (uses := [EQuasinorm.discreteKMethod])]
def discreteKMethod (A₀ A₁ : ESeminorm α) (θ : ℝ) (q : ℝ≥0∞) : ESeminorm α where
  __ := EQuasinorm.discreteKMethod A₀ A₁ θ q
  C_eq_one := sorry

namespace Couple

variable (A : Couple α)

abbrev kMethod := ESeminorm.kMethod A.fstₛ A.sndₛ

abbrev discreteKMethod := ESeminorm.discreteKMethod A.fstₛ A.sndₛ

end Couple

end ESeminorm

/- I don't think those are necessary for Janson's.-/

-- /-- The constant of inequality (6). -/
-- def γKMethod' (θ : ℝ) (q : ℝ≥0∞) : ℝ≥0∞ :=
--   match q with
--   | ∞ => 1 -- `lim_{q → ∞} q ^ (1 / q) * (θ * (1 - θ)) ^ (1 / q) = 1`.
--   | .ofNNReal q => q ^ (1 / q).toReal * (θ.toNNReal * (1 - θ.toNNReal)) ^ (1 / q).toReal

-- /-- Part of Theorem 3.1.2 -/
-- lemma addNorm_le_knorm (hx : ‖x‖ₑ[A₀ ⊔ A₁] < ∞) :
--     kNorm A₀ A₁ t x ≤ γKMethod' θ q * t ^ θ * ‖x‖ₑ[kmethod A₀ A₁ θ q]  := by
--   sorry

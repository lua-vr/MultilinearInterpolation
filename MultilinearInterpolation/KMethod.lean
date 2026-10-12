/-
Copyright (c) 2026 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jim Potergies, Michael Rothgang, Lua Viana Reis
-/

module

public import MultilinearInterpolation.EQuasinorm.Basic
public import MultilinearInterpolation.EQuasinorm.ESeminorm
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import MultilinearInterpolation.Mathlib.MeasureTheory.Function.LpSeminorm.Count
import MultilinearInterpolation.Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import MultilinearInterpolation.Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import MultilinearInterpolation.Mathlib.MeasureTheory.Measure.Count
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

/-- Reflection: $`Φ_θ(ν ↦ 2^ν f(-ν)) = Φ_{1-θ}(f)`. -/
@[blueprint]
lemma discretePhiFunctional_reflect (θ : ℝ) (q : ℝ≥0∞) (f : ℤ → ℝ≥0∞) :
    discretePhiFunctional θ q (fun k ↦ 2 ^ k * f (-k)) = discretePhiFunctional (1 - θ) q f := by
  have h : (fun k : ℤ ↦ (2 : ℝ≥0∞) ^ (-k * θ) * (2 ^ k * f (-k))) =
      (fun k : ℤ ↦ (2 : ℝ≥0∞) ^ (-k * (1 - θ)) * f k) ∘ Neg.neg := by
    ext k
    rw [Function.comp_apply, ← mul_assoc, ← ENNReal.rpow_intCast,
      ← ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top]
    congr 2
    push_cast
    ring
  rw [discretePhiFunctional, discretePhiFunctional, h, eLpNorm_comp_measurePreserving
    .of_discrete (neg_bijective.measurePreserving_count .of_discrete)]

/-- Monotonicity: $`f ≤ g` implies $`Φ_θ(f) ≤ Φ_θ(g)`. -/
@[blueprint]
lemma discretePhiFunctional_mono {f g : ℤ → ℝ≥0∞} (h : f ≤ g) :
    discretePhiFunctional θ q f ≤ discretePhiFunctional θ q g :=
  eLpNorm_mono_enorm .of_discrete fun k ↦ by simp only [enorm_eq_self]; gcongr; exact h k

/-- For $`q ≠ 0` and $`r = \min(q,1)`, $`Φ_θ(f+g)^r ≤ Φ_θ(f)^r + Φ_θ(g)^r`. -/
@[blueprint]
lemma discretePhiFunctional_add_rpow_le (hq : q ≠ 0) (f g : ℤ → ℝ≥0∞) :
    discretePhiFunctional θ q (f + g) ^ (min q 1).toReal ≤
    discretePhiFunctional θ q f ^ (min q 1).toReal +
    discretePhiFunctional θ q g ^ (min q 1).toReal := by
  simp only [discretePhiFunctional, Pi.add_apply, mul_add]
  exact eLpNorm_add_rpow_le hq

/-- Shift: $`Φ_θ(k ↦ f(k+1)) = 2^θ Φ_θ(f)`. -/
@[blueprint]
lemma discretePhiFunctional_shift (f : ℤ → ℝ≥0∞) :
    discretePhiFunctional θ q (fun k ↦ f (k + 1)) = 2 ^ θ * discretePhiFunctional θ q f := by
  have h : (fun k : ℤ ↦ (2 : ℝ≥0∞) ^ (-k * θ) * f (k + 1)) =
      fun k ↦ 2 ^ θ * ((fun k : ℤ ↦ (2 : ℝ≥0∞) ^ (-k * θ) * f k) ∘ (· + 1)) k := by
    ext k
    rw [Function.comp_apply, ← mul_assoc, ← ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top]
    congr 2
    push_cast
    ring
  rw [discretePhiFunctional, discretePhiFunctional, h,
    eLpNorm_const_mul (by finiteness) .of_discrete,
    eLpNorm_comp_measurePreserving .of_discrete
      ((AddGroup.addRight_bijective 1).measurePreserving_count .of_discrete)]

/-- A single term: for $`q ≠ 0`, $`Φ_θ` of the sequence equal to $`c` at $`i` and to $`0`
elsewhere is $`2^{-iθ} c`. -/
@[blueprint]
lemma discretePhiFunctional_single (hq : q ≠ 0) (i : ℤ) (c : ℝ≥0∞) :
    discretePhiFunctional θ q (Pi.single i c) = 2 ^ (-i * θ) * c := by
  have h : (fun k : ℤ ↦ (2 : ℝ≥0∞) ^ (-k * θ) * (Pi.single i c : ℤ → ℝ≥0∞) k) =
      Pi.single i (2 ^ (-i * θ) * c) :=
    funext fun k ↦ (Pi.single_mul_right_apply i k (fun k : ℤ ↦ (2 : ℝ≥0∞) ^ (-k * θ)) c).symm
  rw [discretePhiFunctional, h, eLpNorm_count_single i _ hq, enorm_eq_self]

/-- A window of $`2N` equal terms: for $`θ ≥ 0`,
$$`Φ_θ\bigl(c\,\mathbf 1_{\{-N,\dots,N-1\}}\bigr) ≤ 2^{Nθ} c\,(2N)^{1/q}.` -/
@[blueprint]
lemma discretePhiFunctional_indicator_Ico_le (hθ : 0 ≤ θ) (N : ℕ) (c : ℝ≥0∞) :
    discretePhiFunctional θ q ((Ico (-N : ℤ) N).indicator fun _ ↦ c) ≤
    2 ^ (N * θ) * c * (2 * N : ℝ≥0∞) ^ (1 / q.toReal) := by
  have h := eLpNorm_count_indicator_finset_le (Finset.Ico (-N : ℤ) N) (2 ^ (N * θ) * c) q
  rw [Finset.coe_Ico, Int.card_Ico, enorm_eq_self] at h
  refine (eLpNorm_mono_enorm .of_discrete fun k ↦ ?_).trans (h.trans_eq ?_)
  · simp only [enorm_eq_self]
    by_cases hk : k ∈ Ico (-N : ℤ) N
    · simp only [indicator_of_mem hk]
      have : -(k : ℝ) ≤ N := by have := hk.1; rify at this; linarith
      gcongr
      exact one_le_two
    · simp [indicator_of_notMem hk]
  · congr 3
    norm_cast
    omega

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

/-- Swapping the two quasinorms replaces $`θ` by $`1 - θ`. Stated for the extended norms only,
since the constant of {name}`discreteKMethod` need not be invariant under the swap. -/
@[blueprint]
lemma enorm_discreteKMethod_swap (x : α) :
    ‖x‖ₑ[discreteKMethod A₁ A₀ θ q] = ‖x‖ₑ[discreteKMethod A₀ A₁ (1 - θ) q] := by
  change discretePhiFunctional θ q (fun k ↦ kNorm A₁ A₀ (2 ^ k) x) =
    discretePhiFunctional (1 - θ) q (fun k ↦ kNorm A₀ A₁ (2 ^ k) x)
  rw [← discretePhiFunctional_reflect]
  exact congrArg _ (funext fun k ↦ kNorm_swap_zpow k x)

/-- Lemma 3.1.3. -/
@[blueprint]
lemma discreteKMethod_equiv_kmethod : discreteKMethod A₀ A₁ θ q ≈ kMethod A₀ A₁ θ q := by
  sorry

end Discrete

namespace Couple

variable (A : Couple α)

abbrev kMethod := EQuasinorm.kMethod A.fst A.snd

abbrev discreteKMethod := EQuasinorm.discreteKMethod A.fst A.snd

lemma enorm_discreteKMethod_swap (x : α) :
    ‖x‖ₑ[A.swap.discreteKMethod θ q] = ‖x‖ₑ[A.discreteKMethod (1 - θ) q] :=
  EQuasinorm.enorm_discreteKMethod_swap x

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

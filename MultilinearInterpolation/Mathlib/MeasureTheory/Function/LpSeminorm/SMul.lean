/-
Copyright (c) 2026 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-! # Constant factors in the $`L^p`-seminorm of $`[0,∞]`-valued functions -/

public section

open ENNReal Filter

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- For $`c < ∞` and $`f` with values in $`[0,∞]`, $`\|c f\|_p = c \|f\|_p`. Mathlib's
{name}`MeasureTheory.eLpNorm_const_smul` needs a normed group and a normed division ring. -/
lemma eLpNorm_const_mul {c : ℝ≥0∞} (hc : c ≠ ∞) {f : α → ℝ≥0∞}
    (hf : AEStronglyMeasurable f μ) (p : ℝ≥0∞) :
    eLpNorm (fun x ↦ c * f x) p μ = c * eLpNorm f p μ := by
  rcases eq_or_ne c 0 with rfl | hc0
  · simp
  refine le_antisymm (eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' p
    ((ENNReal.continuous_const_mul hc).comp_aestronglyMeasurable hf)
    (Eventually.of_forall fun _ ↦ le_rfl)) (ENNReal.mul_le_of_le_div' ?_)
  rw [ENNReal.div_eq_inv_mul]
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' p hf (Eventually.of_forall fun x ↦ ?_)
  simp only [enorm_eq_self, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hc, one_mul, le_rfl]

end MeasureTheory

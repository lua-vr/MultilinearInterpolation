/-
Copyright (c) 2026 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! # Subadditivity of `x ↦ x ^ p` scales the constant by {lit}`2 ^ p` -/

@[expose] public section

open scoped ENNReal

namespace ENNReal

/-- Raising to a nonnegative power $`p` turns $`c`-subadditivity into $`(2c)^p`-subadditivity. -/
theorem mul_add_rpow_le_mul_rpow_add_rpow (c a b : ℝ≥0∞) {p : ℝ} (hp : 0 ≤ p) :
    (c * (a + b)) ^ p ≤ (2 * c) ^ p * (a ^ p + b ^ p) :=
  calc (c * (a + b)) ^ p
    _ = c ^ p * (a + b) ^ p := ENNReal.mul_rpow_of_nonneg _ _ hp
    _ ≤ c ^ p * (2 ^ p * (a ^ p + b ^ p)) := by
        grw [ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow a b hp]
    _ = (2 * c) ^ p * (a ^ p + b ^ p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp]
        ring

end ENNReal

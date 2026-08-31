/-
Copyright (c) 2026 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/

import MultilinearInterpolation.EQuasinorm.Basic
import MultilinearInterpolation.EQuasinorm.ESeminorm
import MultilinearInterpolation.EQuasinorm.Multisubadditive

/-!
In this file, we show that a c-{name}`EQuasinorm` is equivalent to an actual
{name}`ESeminorm` raised to a power $`p`, where $`p` is such that $`(2c)^p = 2`. This is
used to extend the results from seminorms to quasi-Banach spaces.

Following *Interpolation Spaces, An Introduction* by Jöran Bergh and Jörgen
 Löfström, lemma 3.10.1.
-/

noncomputable section

open scoped NNReal ENNReal

variable {α : Type*} [AddCommMonoid α] (A : EQuasinorm α) (p : ℝ)

section Pow

/-- The quasinorm raised to a power $`p`, as a quasinorm. -/
@[blueprint]
def pow (A : EQuasinorm α) (p : ℝ) (hp : 0 < p) : EQuasinorm α where
  enorm := ⟨fun x ↦ ‖x‖ₑ[A] ^ p⟩
  C := (2 * A.C) ^ p
  enorm_zero := by simp [hp]
  enorm_add_le_mul x y := by
    push_cast
    grw [A.enorm_add_le_mul x y]
    exact ENNReal.mul_add_rpow_le_mul_rpow_add_rpow _ _ _ hp.le

end Pow

@[blueprint]
def EQuasinorm.aokiRolewicz (hp : (2 * A.C) ^ p = 2) : ESeminorm α where
  enorm := ⟨ fun a ↦ ⨅ (n : ℕ) (a' : Fin n → α) (h : ∑ i, a' i = a), ∑ j, ‖a' j‖ₑ[A] ^ p ⟩
  enorm_zero := sorry
  enorm_add_le_mul := sorry
  C_eq_one := sorry

/-- If $`(2C)^p = 2` then the exponent $`p` is positive. -/
lemma pos_of_rpow_two_mul_C_eq_two {A : EQuasinorm α} {p : ℝ} (hp : (2 * A.C) ^ p = 2) :
    0 < p := by
  by_contra h
  have : (2 * A.C) ^ p ≤ 1 := by bound
  rw [hp] at this
  norm_num at this

variable {A p} in
@[blueprint]
theorem aokiRolewicz_equiv_pow (hp : (2 * A.C) ^ p = 2) :
    (A.aokiRolewicz p hp).toEQuasinorm ≈ A.pow p (EQuasinorm.pos_of_rpow_two_mul_C_eq_two hp) :=
  sorry

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

@[blueprint]
def EQuasinorm.aokiRolewicz (hp : (2 * A.C) ^ p = 2) : ESeminorm α where
  enorm := ⟨ fun a ↦ ⨅ (n : ℕ) (a' : Fin n → α) (h : ∑ i, a' i = a), ∑ j, ‖a' j‖ₑ[A] ^ p ⟩
  enorm_zero := sorry
  enorm_add_le_mul := sorry
  C_eq_one := sorry

variable {A p} in
@[blueprint]
theorem aokiRolewicz_equiv_pow (hp : (2 * A.C) ^ p = 2) :
    (A.aokiRolewicz p hp).toEQuasinorm ≈ A.pow p :=
  sorry

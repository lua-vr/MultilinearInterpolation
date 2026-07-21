/-
Copyright (c) 2025 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/

import MultilinearInterpolation.EQuasinorm.Basic
import MultilinearInterpolation.EQuasinorm.ESeminorm

/-!
In this file, we show that a c-`EQuasinorm` is equivalent to an actual
`ESeminorm` raised to a power `p`, where `p` is such that $`(2c)^p = 2`. This is
used to extend the results from seminorms to quasi-Banach spaces.

Following *Interpolation Spaces, An Introduction* by Jöran Bergh and Jörgen
 Löfström, lemma 3.10.1.
-/

noncomputable section

open scoped NNReal ENNReal

variable [AddCommMonoid α] (A : EQuasinorm α) (p : ℝ)

def EQuasinorm.aokiRolewiczSeminorm : ESeminorm α where
  enorm := ⟨ fun a ↦ ⨅ (n : ℕ) (a' : Fin n → α) (h : ∑ i, a' i = a), ∑ j, ‖a' j‖ₑ[A] ^ p ⟩
  enorm_zero := sorry
  enorm_add_le_mul := sorry
  C_eq_one := sorry

variable {A p} in
lemma aokiRolewiczSeminorm_pow_equiv_self (hp : (2 * A.C) ^ p = 2) :
    (A.aokiRolewiczSeminorm p).pow p ≈ A :=
  sorry

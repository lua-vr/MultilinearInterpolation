/-
Copyright (c) 2025 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jim Potergies, Michael Rothgang, Lua Viana Reis
-/

import MultilinearInterpolation.Defs.EQuasinorm

/-!
Following
 *Interpolation Spaces, An Introduction* by  Jöran Bergh , Jörgen Löfström.
-/

noncomputable section

open scoped ENNReal NNReal

variable {𝓐 : Type*} [AddMonoid 𝓐] {𝓑 : Type*} [AddMonoid 𝓑]

/- This is `ESeminormedAddMonoid` as a structure but we don't fix a topology on 𝓐. -/
variable (𝓐) in
structure ESeminorm extends EQuasinorm 𝓐 where
  protected C_eq_one : C = 1
  protected C := 1

instance : Coe (ESeminorm 𝓐) (EQuasinorm 𝓐) where
  coe A := A.toEQuasinorm

variable {A A₀ A₁ A' A₀' A₁' : ESeminorm 𝓐}

namespace ESeminorm

attribute [simp] ESeminorm.C_eq_one

lemma enorm_add_le : ∀ x y, ‖x + y‖ₑ[A] ≤ ‖x‖ₑ[A] + ‖y‖ₑ[A] := by
  simpa using A.enorm_add_le_mul

/-- The minimum `A₀ ⊓ A₁` equipped with the norm `J(t,-)` -/
def skewedMin (A₀ A₁ : ESeminorm 𝓐) (t : ℝ≥0∞) : ESeminorm 𝓐 where
  __ := A₀.toEQuasinorm.skewedMin A₁ t
  C_eq_one := by simp

instance : Min (ESeminorm 𝓐) :=
  ⟨fun A₀ A₁ ↦ A₀.skewedMin A₁ 1⟩

variable (𝓐) in
structure Couple extends EQuasinorm.Couple 𝓐 where
  protected C_eq_one : fst.C = 1 ∧ snd.C = 1

namespace Couple

variable (A : Couple 𝓐)

def fst' : ESeminorm 𝓐 := ⟨A.fst, A.C_eq_one.1⟩

def snd' : ESeminorm 𝓐 := ⟨A.snd, A.C_eq_one.2⟩

lemma enorm_add_le : ∀ x y, ‖x + y‖ₑ[A.fst] ≤ ‖x‖ₑ[A.fst] + ‖y‖ₑ[A.fst] :=
  A.fst'.enorm_add_le

lemma enorm_add_le' : ∀ x y, ‖x + y‖ₑ[A.snd] ≤ ‖x‖ₑ[A.snd] + ‖y‖ₑ[A.snd] :=
  A.snd'.enorm_add_le

end Couple

end ESeminorm

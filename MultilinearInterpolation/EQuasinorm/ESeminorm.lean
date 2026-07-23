/-
Copyright (c) 2026 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/

import MultilinearInterpolation.EQuasinorm.Basic
import Blueprint.BlueprintAttr

/-!
Following
 *Interpolation Spaces, An Introduction* by  Jöran Bergh , Jörgen Löfström.
-/

noncomputable section

open scoped ENNReal NNReal

variable {α : Type*} [AddMonoid α] {β : Type*} [AddMonoid β]

/- This is `ESeminormedAddMonoid` as a structure but we don't fix a topology on 𝓐. -/
variable (α) in
@[blueprint_]
structure ESeminorm extends EQuasinorm α where
  /-- The constant $`C` equals 1. -/
  protected C_eq_one : C = 1
  protected C := 1

instance : Coe (ESeminorm α) (EQuasinorm α) where
  coe A := A.toEQuasinorm

variable {A : ESeminorm α}

namespace ESeminorm

attribute [simp] ESeminorm.C_eq_one

lemma enorm_add_le : ∀ x y, ‖x + y‖ₑ[A] ≤ ‖x‖ₑ[A] + ‖y‖ₑ[A] := by
  simpa using A.enorm_add_le_mul

/-- The minimum $`A₀ ⊓ A₁` equipped with the norm $`J(t,-)` -/
def skewedInf (A₀ A₁ : ESeminorm α) (t : ℝ≥0∞) : ESeminorm α where
  __ := A₀.toEQuasinorm.skewedInf A₁ t
  C_eq_one := by simp

instance : Min (ESeminorm α) :=
  ⟨fun A₀ A₁ ↦ A₀.skewedInf A₁ 1⟩

variable (α) in
structure Couple extends EQuasinorm.Couple α where
  protected C_eq_one : fst.C = 1 ∧ snd.C = 1

namespace Couple

variable (A : Couple α)

def fst' : ESeminorm α := ⟨A.fst, A.C_eq_one.1⟩

def snd' : ESeminorm α := ⟨A.snd, A.C_eq_one.2⟩

lemma enorm_add_le : ∀ x y, ‖x + y‖ₑ[A.fst] ≤ ‖x‖ₑ[A.fst] + ‖y‖ₑ[A.fst] :=
  A.fst'.enorm_add_le

lemma enorm_add_le' : ∀ x y, ‖x + y‖ₑ[A.snd] ≤ ‖x‖ₑ[A.snd] + ‖y‖ₑ[A.snd] :=
  A.snd'.enorm_add_le

end Couple

end ESeminorm

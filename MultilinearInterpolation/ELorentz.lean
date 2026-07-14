/-
Copyright (c) 2025 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/

import MultilinearInterpolation.KMethod
import VersoBlueprint
import Carleson.ToMathlib.MeasureTheory.Function.LorentzSpace.Basic

set_option verso.blueprint.autoDeps true

/-!
 Defines `eLorentzNorm` as a `QuasiENorm`, then shows it is an interpolation
 space by following *Interpolation Spaces, An Introduction* by Jöran Bergh,
 Jörgen Löfström, Section 5.3.
-/

noncomputable section

namespace QuasiENorm

open MeasureTheory
open scoped ENNReal NNReal

variable {α : Type*} [mα : MeasurableSpace α] (μ : Measure α) {β : Type*} [TopologicalSpace β]

section Lorentz

variable [ESeminormedAddMonoid β] [ContinuousAdd β]

@[simp]
lemma LorentzAddConst_pos {p q} : LorentzAddConst p q ≠ 0 := sorry

open Classical in
variable (β) in
def eLorentz (p q : ℝ≥0∞) : QuasiENorm (α → β) where
  enorm := ⟨fun f ↦ if AEStronglyMeasurable f μ then eLorentzNorm f p q μ else ∞⟩
  C := LorentzAddConst p q
  C_lt := LorentzAddConst_lt_top
  enorm_zero := by simp [eLorentzNorm_zero, aestronglyMeasurable_zero]
  enorm_add_le_mul f g := by
    by_cases h : AEStronglyMeasurable f μ ∧ AEStronglyMeasurable g μ
    · grind [eLorentzNorm_add_le' h.1 h.2, h.1.add h.2]
    rw [not_and_or] at h
    rcases h with h₁ | h₂
    · simp [h₁]
    · simp [h₂]

end Lorentz

section Interpolation

variable [ESeminormedAddMonoid β] [ContinuousAdd β]

variable (β) in
def eLorentzCouple (p₀ p₁ q₀ q₁ : ℝ≥0∞) : Couple (α → β) :=
  ⟨eLorentz μ β p₀ q₀, eLorentz μ β p₁ q₁⟩

/-- BL Theorem 5.3.1. -/
theorem eLorentz_equiv_kMethod_of_neq (p₀ q₀ p₁ q₁ q p : ℝ≥0∞) (hp₀₁ : p₀ ≠ p₁) (t : ℝ≥0)
    (hpos : 0 < p₀ ∧ 0 < p₁ ∧ 0 < q₀ ∧ 0 < q₁ ∧ 0 < q) (hp : p⁻¹ = (1 - t) / p₀ + t / p₁) :
    eLorentz μ β p q ≈ (eLorentzCouple μ β p₀ q₀ p₁ q₁).kmethod t q :=
  sorry

/-- BL Theorem 5.3.1. -/
theorem eLorentz_equiv_kMethod_of_eq (p q₀ q₁ q : ℝ≥0∞) (t : ℝ≥0)
    (hpos : 0 < p ∧ 0 < q₀ ∧ 0 < q₁ ∧ 0 < q) (hq : q⁻¹ = (1 - t) / q₀ + t / q₁) :
    eLorentz μ β p q ≈ (eLorentzCouple μ β p q₀ p q₁).kmethod t q :=
  sorry

end Interpolation

end QuasiENorm

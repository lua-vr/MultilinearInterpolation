/-
Copyright (c) 2026 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/

module

public import MultilinearInterpolation.KMethod
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Tactic.Basify
import VersoBlueprint
meta import VersoBlueprint

/-!
 Defines `eLorentzNorm` as a `QuasiENorm`, then shows it is an interpolation
 space by following *Interpolation Spaces, An Introduction* by Jöran Bergh,
 Jörgen Löfström, Section 5.3.
-/

@[expose] public noncomputable section

namespace EQuasinorm

open MeasureTheory
open scoped ENNReal NNReal

variable {α : Type*} [mα : MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] {β : Type*}
  [TopologicalSpace β]

section Lorentz

variable [ESeminormedAddCommMonoid β] [ContinuousAdd β]

section CarlesonConsts

opaque eLorentzNorm (f : α → β) (p q : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞

noncomputable def LorentzAddConst (p r : ℝ≥0∞) : ℝ≥0∞ :=
  if p = 0 ∨ r ∈ Set.Icc 1 p then 1 else 2 ^ p.toReal⁻¹ * ENNReal.LpAddConst r

lemma eLorentzNorm_zero : eLorentzNorm (0 : α → β) p q μ = 0 := sorry

lemma eLorentzNorm_add_le {f g : α → β} [SigmaFinite μ] :
    eLorentzNorm (f + g) p q μ ≤
    LorentzAddConst p q * (eLorentzNorm f p q μ + eLorentzNorm g p q μ) :=
  sorry

end CarlesonConsts

@[simp]
lemma LorentzAddConst_pos {p q} : LorentzAddConst p q ≠ 0 := sorry

lemma LorentzAddConst_lt_top {p q} : LorentzAddConst p q < ∞ := by
  unfold LorentzAddConst
  split_ifs
  · simp
  · exact ENNReal.mul_lt_top (by finiteness) (ENNReal.LpAddConst_lt_top _)

--  todo: fix upstream
attribute [local basify_op ←] ENNReal.coe_rpow_of_ne_zero

lemma _root_.ENNReal.one_le_LpAddConst (q : ℝ≥0∞) : 1 ≤ q.LpAddConst := by
  unfold ENNReal.LpAddConst
  split_ifs with h
  · rw [Set.mem_Ioo] at h
    basify
    grind [one_le_inv₀, one_le_two, Real.one_le_rpow]
  · rfl

lemma one_le_LorentzAddConst {p q} : 1 ≤ LorentzAddConst p q := by
  unfold LorentzAddConst
  split_ifs with h
  · rfl
  refine one_le_mul ?_ (ENNReal.one_le_LpAddConst q)
  basify
  all_goals exact Real.one_le_rpow one_le_two (by positivity)

open Classical in
variable (β) in
@[blueprint]
def eLorentz (p q : ℝ≥0∞) : EQuasinorm (α → β) where
  enorm := ⟨fun f ↦ eLorentzNorm f p q μ⟩
  C := LorentzAddConst p q
  C_lt_top := LorentzAddConst_lt_top
  C_ge_one := one_le_LorentzAddConst
  enorm_zero := eLorentzNorm_zero ..
  enorm_add_le_mul _ _ := eLorentzNorm_add_le ..

end Lorentz

section Interpolation

variable [ESeminormedAddCommMonoid β] [ContinuousAdd β]

variable (β) in
@[blueprint]
def eLorentzCouple (p₀ p₁ q₀ q₁ : ℝ≥0∞) : Couple (α → β) :=
  ⟨eLorentz μ β p₀ q₀, eLorentz μ β p₁ q₁⟩

/-- For a Banach couple $`A = (A_0,A_1)` given by two Lorentz spaces
$`A_0 = L_{p_0,q_0}` and $`A_1 = L_{p_1,q_1}` where $`p_0,p_1,q_0,q_1 \in (0,\infty]` with
$`p_0 \neq p_1`, for all $`0 < \theta < 1` and $`q \in (0,\infty]`, the real interpolation space
$`(A)_{\theta,q}` is the Lorentz space $`L_{p,q}` where
$`p^{-1} = (1 - \theta) p_0^{-1} + \theta p_1^{-1}`.
-/
@[blueprint]
theorem eLorentz_equiv_kMethod_of_neq (p₀ q₀ p₁ q₁ q p : ℝ≥0∞) (hp₀₁ : p₀ ≠ p₁) (t : ℝ≥0)
    (hpos : 0 < p₀ ∧ 0 < p₁ ∧ 0 < q₀ ∧ 0 < q₁ ∧ 0 < q) (hp : p⁻¹ = (1 - t) / p₀ + t / p₁) :
    eLorentz μ β p q ≈ (eLorentzCouple μ β p₀ q₀ p₁ q₁).kMethod t q :=
  sorry

/-- BL Theorem 5.3.1. -/
theorem eLorentz_equiv_kMethod_of_eq (p q₀ q₁ q : ℝ≥0∞) (t : ℝ≥0)
    (hpos : 0 < p ∧ 0 < q₀ ∧ 0 < q₁ ∧ 0 < q) (hq : q⁻¹ = (1 - t) / q₀ + t / q₁) :
    eLorentz μ β p q ≈ (eLorentzCouple μ β p q₀ p q₁).kMethod t q :=
  sorry

end Interpolation

end EQuasinorm

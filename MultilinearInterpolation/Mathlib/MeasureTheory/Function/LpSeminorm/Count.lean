/-
Copyright (c) 2026 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Count

/-! # $`L^p`-seminorms of single terms and of finite indicators for the counting measure -/

public section

open ENNReal Set

namespace MeasureTheory

variable {α ε : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
  [TopologicalSpace ε] [ESeminormedAddMonoid ε] {p : ℝ≥0∞}

/-- For $`p ≠ 0`, the function equal to $`c` at $`i` and to $`0` elsewhere has
$`L^p`-seminorm $`\|c\|` for the counting measure. -/
lemma eLpNorm_count_single [DecidableEq α] (i : α) (c : ε) (hp : p ≠ 0) :
    eLpNorm (Pi.single i c) p Measure.count = ‖c‖ₑ := by
  rw [← indicator_singleton i (fun _ ↦ c),
    eLpNorm_indicator_const' (measurableSet_singleton i).nullMeasurableSet (by simp) hp]
  simp

/-- For a finite set $`s`, the function equal to $`c` on $`s` and to $`0` elsewhere has
$`L^p`-seminorm at most $`\|c\| \cdot (\#s)^{1/p}` for the counting measure. -/
lemma eLpNorm_count_indicator_finset_le (s : Finset α) (c : ε) (p : ℝ≥0∞) :
    eLpNorm ((s : Set α).indicator fun _ ↦ c) p Measure.count ≤
      ‖c‖ₑ * (s.card : ℝ≥0∞) ^ (1 / p.toReal) := by
  rw [← Measure.count_apply_finset s]
  exact eLpNorm_indicator_const_le c p s.measurableSet.nullMeasurableSet

end MeasureTheory

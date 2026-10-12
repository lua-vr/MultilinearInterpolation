/-
Copyright (c) 2026 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! # Subadditivity of $`\|f\|_p^{\min(p,1)}` -/

public section

open ENNReal

namespace MeasureTheory

variable {α ε : Type*} {m : MeasurableSpace α} [TopologicalSpace ε] [ESeminormedAddMonoid ε]
  [ContinuousAdd ε] {p : ℝ≥0∞} {μ : Measure α} {f g : α → ε}

/-- For $`p ≠ 0` and $`r = \min(p,1)`, $$`\|f+g\|_p^r ≤ \|f\|_p^r + \|g\|_p^r.`
For $`p ≥ 1` this is Minkowski's inequality, for $`p < 1` the subadditivity of $`\|f\|_p^p`.
It is {name}`MeasureTheory.inhmgELpNorm_add_le`. -/
theorem eLpNorm_add_rpow_le (hp : p ≠ 0) :
    eLpNorm (f + g) p μ ^ (min p 1).toReal ≤
      eLpNorm f p μ ^ (min p 1).toReal + eLpNorm g p μ ^ (min p 1).toReal := by
  rcases le_total 1 p with h | h
  · simpa [min_eq_right h, ← inhmgELpNorm_eq_eLpNorm h] using
      inhmgELpNorm_add_le (f := f) (g := g) (p := p) (μ := μ)
  · simpa [min_eq_left h, ← inhmgELpNorm_eq_eLpNorm_pow h hp] using
      inhmgELpNorm_add_le (f := f) (g := g) (p := p) (μ := μ)

end MeasureTheory

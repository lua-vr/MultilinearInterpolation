/-
Copyright (c) 2026 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Positive powers of $`[0,∞]`-valued functions tending to zero -/

public section

open Filter Topology
open scoped ENNReal

/-- The $`[0,∞]` version of {lit}`Filter.Tendsto.rpow_const_nhds_zero`. -/
theorem Filter.Tendsto.ennrpow_const_nhds_zero {α : Type*} {l : Filter α} {f : α → ℝ≥0∞}
    {p : ℝ} (hf : Tendsto f l (𝓝 0)) (hp : 0 < p) :
    Tendsto (fun t ↦ f t ^ p) l (𝓝 0) :=
  ENNReal.zero_rpow_of_pos hp ▸ hf.ennrpow_const p

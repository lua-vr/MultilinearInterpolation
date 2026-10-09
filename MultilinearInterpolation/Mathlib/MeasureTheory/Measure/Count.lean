/-
Copyright (c) 2026 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Measure.Count

/-! # Measurable bijections preserve the counting measure -/

@[expose] public section

namespace Function.Bijective

open MeasureTheory Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {f : α → β}

/-- A measurable bijection maps the counting measure to the counting measure. -/
theorem map_count (hf : f.Bijective) (h2f : Measurable f) : count.map f = count := by
  ext s hs
  rw [map_apply h2f hs, count_apply (hs.preimage h2f), count_apply hs,
    Set.encard_preimage_of_bijective hf]

/-- A measurable bijection preserves the counting measure. -/
theorem measurePreserving_count (hf : f.Bijective) (h2f : Measurable f) :
    MeasurePreserving f count count :=
  ⟨h2f, hf.map_count h2f⟩

end Function.Bijective

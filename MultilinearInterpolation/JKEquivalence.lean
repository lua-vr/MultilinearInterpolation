/-
Copyright (c) 2026 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/

import MultilinearInterpolation.EQuasinorm.ESeminorm
import MultilinearInterpolation.JMethod
import MultilinearInterpolation.KMethod
import Mathlib.Topology.Filter
import VersoBlueprint

/-!
Following *Interpolation Spaces, An Introduction* by Jöran Bergh and Jörgen Löfström, Section 3.3.
-/

noncomputable section

open Set MeasureTheory EQuasinorm Filter
open scoped ENNReal NNReal Topology

variable {α β : Type*} [AddMonoid α] [AddMonoid β]
  {A : Couple α} {t s : ℝ≥0∞} {x y z : α} {θ : ℝ} {q : ℝ≥0∞}

namespace EQuasinorm

/-- *The fundamental lemma of interpolation theory*

Lemma 3.3.2.
-/
theorem exists_representation_of_tendsto_min_mul_kNorm (a : α)
  (hᵢ : Tendsto (fun t ↦ min 1 (1 / t) * A.kNorm t a) (𝓝 ∞) (𝓝 0))
  (h₀ : Tendsto (fun t ↦ min 1 (1 / t) * A.kNorm t a) (𝓝 0) (𝓝 0)) :
  ∃ (u : ℤ → α) := sorry

end EQuasinorm

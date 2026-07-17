/-
Copyright (c) 2025 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/

import MultilinearInterpolation.ELorentz
import VersoBlueprint

set_option verso.blueprint.autoDeps true

noncomputable section

namespace EQuasinorm

open MeasureTheory
open scoped ENNReal NNReal

variable {α : Type*} [mα : MeasurableSpace α] (μ : Measure α) {β : Type*} [TopologicalSpace β]
  [ESeminormedAddMonoid β] [ContinuousAdd β] (m : ℕ)

def εCouple (ε : ℝ≥0∞) := eLorentzCouple μ β ε ∞ ε ∞

def εProd (ε : ℝ≥0∞) : Fin m → Couple (α → β) := fun _ ↦ εCouple μ ε

end EQuasinorm

/-
Copyright (c) 2026 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/

import MultilinearInterpolation.EQuasinorm.Basic
import MultilinearInterpolation.KMethod
import VersoBlueprint

/-!
Following *Interpolation Spaces, An Introduction* by Jöran Bergh and Jörgen Löfström, Section 3.2.
-/

noncomputable section

open Set MeasureTheory EQuasinorm
open scoped ENNReal NNReal

variable {α β : Type*} [AddMonoid α] [AddMonoid β]
  {A₀ A₁ : EQuasinorm α} {t s : ℝ≥0∞} {x y z : α} {θ : ℝ} {q : ℝ≥0∞}

namespace EQuasinorm

namespace JMethod

/-- The space $`J_{θ,q}(\bar{A})` in Section 3.2. -/
@[blueprint_]
def jMethod (A₀ A₁ : EQuasinorm α) (θ : ℝ) (q : ℝ≥0∞) : EQuasinorm α where
  enorm := ⟨fun x ↦ phiFunctional θ q (jNorm A₀ A₁ · x)⟩
  C := sorry
  C_lt := sorry
  enorm_zero := sorry
  enorm_add_le_mul := sorry

section Discrete

/-- The discrete version of $`J_{θ,q}(\bar{A})`. -/
@[blueprint_]
def discreteJMethod (A₀ A₁ : EQuasinorm α) (θ : ℝ) (q : ℝ≥0∞) : EQuasinorm α where
  enorm := ⟨fun x ↦ discretePhiFunctional θ q (fun k ↦ jNorm A₀ A₁ (2 ^ k) x)⟩
  C := sorry
  C_lt := sorry
  enorm_zero := sorry
  enorm_add_le_mul := sorry

/-- Lemma 3.2.3. -/
@[blueprint_]
lemma discreteJMethod_equiv_jmethod : discreteJMethod A₀ A₁ θ q ≈ jMethod A₀ A₁ θ q := by
  sorry

end Discrete

end JMethod

namespace Couple

variable (A : Couple α)

abbrev jMethod := JMethod.jMethod A.fst A.snd

end Couple

end EQuasinorm

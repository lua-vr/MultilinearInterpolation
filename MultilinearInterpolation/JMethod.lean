/-
Copyright (c) 2026 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/

module

public import MultilinearInterpolation.EQuasinorm.Basic
public import MultilinearInterpolation.KMethod
import VersoBlueprint
meta import VersoBlueprint

/-!
Following *Interpolation Spaces, An Introduction* by Jöran Bergh and Jörgen Löfström, Section 3.2.

If we choose to develop the J-method, this section requires some thought: how to define a
"representation" without completeness, stating that the "integral" or the "sum" converge with
respect to the quasinorm? (it's possible, but how feasible?) -/

@[expose] public noncomputable section

open Set MeasureTheory EQuasinorm Filter
open scoped ENNReal NNReal

variable {α β : Type*} [AddCommGroup α]
  {A₀ A₁ : EQuasinorm α} {t s : ℝ≥0∞} {x y z : α} {θ : ℝ} {q : ℝ≥0∞}

namespace EQuasinorm

namespace JMethod

/-- The space $`J_{θ,q}(\bar{A})` in Section 3.2. Since {name}`jNorm` is a norm
on the intersection, it is defined as an infimum over all representations of $`a`,
which are functions $`u : ℝ≥0 → Δ(A)` with $`‖a - ∫ u(t)/t dt‖ₑ = 0`. -/
def jMethod (A₀ A₁ : EQuasinorm α) (θ : ℝ) (q : ℝ≥0∞) : EQuasinorm α where
  enorm := sorry
  C := sorry
  C_lt_top := sorry
  C_ge_one := sorry
  enorm_zero := sorry
  enorm_add_le_mul := sorry

section Discrete

/-- The discrete version of $`J_{θ,q}(\bar{A})`. Since {name}`jNorm` is a norm
on the intersection, it is defined as an infimum over all representations of $`a`,
which are sequences $`(uₙ)ₙ` with $`\|a - ∑ₙ uₙ\|ₑ = 0`, of
$$`Φ_{θ,q}(φ) = \left( ∑_{k ∈ ℤ} (2^{-k θ} J(2^k, u_k))^q \right)^{1/q}.`

We don't assume $`uₙ ∈ Δ(A)` here as it will (likely) be unecessary. -/
@[blueprint]
def discreteJMethod (A₀ A₁ : EQuasinorm α) (θ : ℝ) (q : ℝ≥0∞) : EQuasinorm α where
  enorm := ⟨fun a ↦ ⨅ (u : ℤ → α) (hu : Tendsto (fun s : Finset ℤ ↦ ∑ k ∈ s, u k) atTop sorry),
    discretePhiFunctional θ q (fun k ↦ jNorm A₀ A₁ (2 ^ k) (u k))⟩
  C := sorry
  C_lt_top := sorry
  C_ge_one := sorry
  enorm_zero := sorry
  enorm_add_le_mul := sorry

/-- Lemma 3.2.3. -/
lemma discreteJMethod_equiv_jmethod : discreteJMethod A₀ A₁ θ q ≈ jMethod A₀ A₁ θ q := by
  sorry

end Discrete

end JMethod

namespace Couple

variable (A : Couple α)

abbrev jMethod := JMethod.jMethod A.fst A.snd

end Couple

end EQuasinorm

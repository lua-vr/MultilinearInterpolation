/-
Copyright (c) 2026 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/
module

public import Mathlib.Topology.UniformSpace.Defs
public import Mathlib.Data.ENNReal.Lemmas
public import Mathlib.Data.ENNReal.Inv

@[expose] public section

open Filter Set
open scoped Uniformity

variable {X M : Type*}

namespace UniformSpace

/-- Define a `UniformSpace` using a "distance" function. The function can be, e.g., the
distance in a (usual or extended) metric space or an absolute value on a ring.

This one is more general than `.ofFun` in that it assumes a weaker triangle inequality. -/
@[implicit_reducible]
def ofFun' [AddCommMonoid M] [PartialOrder M]
    (d : X → X → M) (refl : ∀ x, d x x = 0)
    (symm : ∀ x y, d x y = d y x)
    (half : ∀ ε > (0 : M), ∃ δ > (0 : M), ∀ x y z, d x y < δ → d y z < δ → d x z < ε) :
    UniformSpace X :=
  .ofCore
    { uniformity := ⨅ r > 0, 𝓟 { x | d x.1 x.2 < r }
      refl := le_iInf₂ fun r hr => principal_mono.2 <| by simp [Set.subset_def, *]
      symm := tendsto_iInf_iInf fun r => tendsto_iInf_iInf fun _ => tendsto_principal_principal.2
        fun x hx => by rwa [mem_setOf, symm]
      comp := le_iInf₂ fun r hr => let ⟨δ, h0, hδr⟩ := half r hr; le_principal_iff.2 <|
        mem_of_superset
          (mem_lift' <| mem_iInf_of_mem δ <| mem_iInf_of_mem h0 <| mem_principal_self _)
          fun (x, z) ⟨y, h₁, h₂⟩ => hδr _ _ _ h₁ h₂ }

noncomputable section EDist

open scoped ENNReal

@[implicit_reducible]
def ofEdist (C : ℝ≥0∞) (hC : C ≠ ⊤) (d : X → X → ℝ≥0∞) (refl : ∀ x, d x x = 0)
    (symm : ∀ x y, d x y = d y x)
    (quasi : ∀ x y z, d x z ≤ C * (d x y + d y z)) : UniformSpace X :=
  .ofFun' d refl symm fun ε hε ↦ by
    /- llm-filled, unreviewed proof. -/
    refine ⟨ε / (2 * (C + 1)),
      ENNReal.div_pos hε.ne' (fun h => absurd h (by finiteness)), fun x y z h₁ h₂ => ?_⟩
    calc d x z ≤ C * (d x y + d y z) := quasi x y z
      _ ≤ (C + 1) * (d x y + d y z) := by gcongr; exact le_self_add
      _ < (C + 1) * (2 * (ε / (2 * (C + 1)))) := by
          rw [mul_comm (C + 1), mul_comm (C + 1)]
          exact ENNReal.mul_lt_mul_left (a := C + 1) (by simp) (by finiteness)
            (by rw [two_mul]; exact ENNReal.add_lt_add h₁ h₂)
      _ = ε := by
          rw [← mul_assoc, mul_comm (C + 1) 2,
            ENNReal.mul_div_cancel' (by simp) (fun h => absurd h (by finiteness))]

end EDist

end UniformSpace

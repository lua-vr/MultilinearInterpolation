/-
Copyright (c) 2025 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/

import MultilinearInterpolation.Defs.Multisubadditive
import MultilinearInterpolation.Defs.ESeminorm
import MultilinearInterpolation.KMethod
import Carleson.ToMathlib.RealInterpolation.Misc
import VersoBlueprint

set_option verso.blueprint.autoDeps true

noncomputable section

/-!
Following
 *On interpolation of multi-linear operators* by Svante Janson.
-/

noncomputable section

open Set ESeminorm MeasureTheory
open scoped ENNReal NNReal


section JInfNormEquiv

variable {𝓐 : Type*} [AddCommMonoid 𝓐]

variable (A : Couple 𝓐)

/- apparently only the `A.knorm θ q ≤ jInfNorm A θ r q` direction is necessary,
namely in Theorem 2. So instead of constructing a QuasiENorm for `jInfNorm` and
stating equivalence, it should be enough to prove the bound directly. -/

@[blueprint "jInfNorm"]
def jInfNorm (θ : ℝ) (r q : ℝ≥0∞) (x : 𝓐) : ℝ≥0∞ :=
  ⨅ (N : ℕ) (a : Fin (2 * N) → 𝓐) (_ : ∑ n, a n = x),
    eLpNorm (fun k : Fin (2 * N) ↦
      let n : ℝ := k - N
      r ^ (-θ * n) * A.J (r ^ n) (a k)) q Measure.count

/-- Lemma 1. -/
@[blueprint "knorm_le_jInfNorm"]
lemma knorm_le_jInfNorm (θ : ℝ) (hθ : θ ∈ Ioo (0 : ℝ) 1) (r q : ℝ≥0∞) (hr : 0 < r ∧ r ≠ 1 ∧ r < ⊤) :
    ∃ (C : ℝ≥0∞), C ≠ ⊤ ∧ ∀ x, A.knorm θ q x ≤ C * jInfNorm A θ r q x :=
  sorry

end JInfNormEquiv

variable {ι : Type*} [Fintype ι] {M₁ : ι → Type*} [∀ i, AddMonoid (M₁ i)] {M₂ : Type*}
  [AddGroup M₂] [Lattice M₂]

variable (T : MultisubadditiveMap M₁ M₂) (A : (i : ι) → Couple (M₁ i)) (B : Couple M₂)

/- note: I am separating α₀ from the α_{m + 1} since it has a special meaning,
and it avoids the need to write m + 1. -/
variable (α₀ : ℝ) (α : ι → ℝ) (hα : ∀ k, α k ≠ 0)

/- todo: we may need to assume 0 ≤ θ i ≤ 1 in the set. -/
/-- The set Ω in the paper. -/
def Ω : Set (ι → ℝ) :=
  {θ | let θ₀ := α₀ + ∑ i, α i * θ i
    ∃ (q₀ : ℝ≥0∞) (q : ι → ℝ≥0∞),
    0 ≤ α₀ + ∑ i, α i * θ i ∧
    ∃ C, T.IsBoundedFor (fun i ↦ (A i).kmethod (θ i) (q i)) (B.kmethod θ₀ q₀) C}

section Theorem1

/-- Lemma 2, part 1. -/
@[blueprint "mem_Ω_iff"]
lemma mem_Ω_iff : ∀ θ, θ ∈ Ω T A B α₀ α ↔
    let θ₀ := α₀ + ∑ i, α i
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
    ∀ (a : (i : ι) → M₁ i), B.knorm θ₀ ⊤ (T a) ≤
    C * ∏ i, ‖a i‖ₑ[(A i).fst] ^ (1 - θ i : ℝ) * ‖a i‖ₑ[(A i).snd] ^ (θ i : ℝ) := by
  sorry

/-- Lemma 2, part 2. -/
lemma knorm_of_mem_Ω : ∀ θ, θ ∈ Ω T A B α₀ α →
    let θ₀ := α₀ + ∑ i, α i
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
    ∀ (t : ℝ≥0∞),
    ∀ (a : (i : ι) → M₁ i), B.K t (T a) ≤
    C * t ^ α₀ * ∏ i, ‖a i‖ₑ[(A i).fst] ^ (1 - θ i : ℝ) * ‖a i‖ₑ[(A i).snd] ^ (θ i : ℝ) :=
  sorry

/-- Theorem 1. -/
@[blueprint "convex_Ω"
  (proofUses := [mem_Ω_iff])]
theorem convex_Ω : Convex ℝ (Ω T A B α₀ α) := sorry

end Theorem1


section Theorem2

@[blueprint "isBoundedOn_of_mem_Ω"
  (proofUses := [knorm_le_jInfNorm, EQuasinorm.DiscreteKMethod_equiv_KMethod])]
theorem isBoundedOn_of_mem_Ω (θ) (hθ : θ ∈ interior (Ω T c₁ c₂ α₀ α)) :
    let θ₀ := α₀ + ∑ i, α i
    ∀ (q₀ : ℝ≥0∞) (q : ι → ℝ≥0∞) (hq : q₀⁻¹ ≤ ∑ i, (q i)⁻¹),
    ∃ C, T.IsBoundedFor (fun i ↦ (c₁ i).kmethod (θ i) (q i)) (c₂.kmethod θ₀ q₀) C :=
  sorry

end Theorem2

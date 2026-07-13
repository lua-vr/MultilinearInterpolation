/-
Copyright (c) 2025 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/

import MultilinearInterpolation.KMethod
import VersoBlueprint

set_option verso.blueprint.autoDeps true

noncomputable section

/-!
Following
 *On interpolation of multi-linear operators* by Svante Janson.
-/

noncomputable section

open ENNReal Set MeasureTheory
open scoped NNReal

open QuasiENorm


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
      let n := k - N
      r ^ (-θ * n) * A.J (r ^ n) (a k)) q Measure.count

/-- Lemma 1. -/
@[blueprint "knorm_le_jInfNorm"]
lemma knorm_le_jInfNorm (θ : ℝ) (r q : ℝ≥0∞) (hr : 0 < r ∧ r ≠ 1 ∧ r < ⊤) :
    ∃ (C : ℝ≥0∞), C ≠ ⊤ ∧ ∀ x, A.knorm θ q x ≤ C * jInfNorm A θ r q x :=
  sorry

end JInfNormEquiv


section Multilinear

variable {m : ℕ} {𝓐 : Fin m → Type*} [∀ i, AddMonoid (𝓐 i)] {𝓑 : Type*} [AddMonoid 𝓑]

structure IsBoundedOn (T : (∀ i, 𝓐 i) → 𝓑)
    (A : (i : Fin m) → QuasiENorm (𝓐 i)) (B : QuasiENorm 𝓑) : Prop where
  bounded : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ x, ‖T x‖ₑ[B] ≤ C * ∏ i, ‖x i‖ₑ[A i]

variable (T : (∀ i, 𝓐 i) → 𝓑) (A : (i : Fin m) → Couple (𝓐 i)) (B : Couple 𝓑)

/- note: I am separating α₀ from the α_{m + 1} since it has a special meaning,
and it avoids the need to write m + 1. -/
variable (α₀ : ℝ) (α : Fin m → ℝ) (hα : ∀ k, α k ≠ 0)

/- todo: we may need to assume 0 ≤ θ i ≤ 1 in the set! -/
/-- The set Ω in the paper. -/
def Ω : Set (Fin m → ℝ) :=
  {θ | let θ₀ := α₀ + ∑ i, α i
    ∃ (q₀ : ℝ≥0∞) (q : Fin m → ℝ≥0∞),
    0 ≤ α₀ + ∑ i, α i * θ i ∧ IsBoundedOn T (fun i ↦ (A i).kmethod (θ i) (q i)) (B.kmethod θ₀ q₀)}

section Theorem1

/-- Lemma 2, part 1. -/
@[blueprint "mem_Ω_iff"]
lemma mem_Ω_iff : ∀ θ, θ ∈ Ω T A B α₀ α ↔
    let θ₀ := α₀ + ∑ i, α i
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
    ∀ (a : (i : Fin m) → 𝓐 i), B.knorm θ₀ ⊤ (T a) ≤
    C * ∏ i, ‖a i‖ₑ[(A i).fst] ^ (1 - θ i : ℝ) * ‖a i‖ₑ[(A i).snd] ^ (θ i : ℝ) :=
  sorry

/-- Lemma 2, part 2. -/
lemma knorm_of_mem_Ω : ∀ θ, θ ∈ Ω T A B α₀ α →
    let θ₀ := α₀ + ∑ i, α i
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
    ∀ (t : ℝ≥0∞),
    ∀ (a : (i : Fin m) → 𝓐 i), B.K t (T a) ≤
    C * t ^ α₀ * ∏ i, ‖a i‖ₑ[(A i).fst] ^ (1 - θ i : ℝ) * ‖a i‖ₑ[(A i).snd] ^ (θ i : ℝ) :=
  sorry

/-- Theorem 1. -/
@[blueprint "convex_Ω"
  (proofUses := [mem_Ω_iff])]
theorem convex_Ω : Convex ℝ (Ω T A B α₀ α) := sorry

end Theorem1


section Theorem2

@[blueprint "isBoundedOn_of_mem_Ω"
  (proofUses := [knorm_le_jInfNorm, DiscreteKMethod_equiv_KMethod])]
theorem isBoundedOn_of_mem_Ω (θ) (hθ : θ ∈ interior (Ω T A B α₀ α)) :
    let θ₀ := α₀ + ∑ i, α i
    ∀ (q₀ : ℝ≥0∞) (q : Fin m → ℝ≥0∞) (hq : q₀⁻¹ ≤ ∑ i, (q i)⁻¹),
    IsBoundedOn T (fun i ↦ (A i).kmethod (θ i) (q i)) (B.kmethod θ₀ q₀) :=
  sorry

end Theorem2

end Multilinear

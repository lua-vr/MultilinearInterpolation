/-
Copyright (c) 2026 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/

module

public import MultilinearInterpolation.EQuasinorm.Multisubadditive
public import MultilinearInterpolation.EQuasinorm.ESeminorm
public import MultilinearInterpolation.KMethod

/-!
Following
 *On interpolation of multi-linear operators* by Svante Janson.
-/

@[expose] public noncomputable section

open Set EQuasinorm MeasureTheory
open scoped ENNReal NNReal


section Lemma1

variable {α : Type*} [AddCommMonoid α] (A : Couple α)

/-- Let $`x \in \alpha`, $`\delta > 0` and $`\nu \in \mathbb{Z}`. There is a decomposition
$`x = y + z` with $$`\|y\|_0 + 2^\nu \|z\|_1 \le K_\nu(x) + \delta`. -/
@[blueprint]
lemma exists_decomp_le_kNorm_add {δ : ℝ≥0∞} (hδ : δ ≠ 0) (x : α) (ν : ℤ) :
    ∃ y z : α, y + z = x ∧
      ‖y‖ₑ[A.fst] + 2 ^ ν * ‖z‖ₑ[A.snd] ≤ A.kNorm (2 ^ ν) x + δ := by
  by_cases hK : A.kNorm (2 ^ ν) x = ∞
  · exact ⟨x, 0, by simp [hK]⟩
  obtain ⟨x₀, x₁, hx, h⟩ := exists_decomp_lt_of_lt_kNorm (ENNReal.lt_add_right hK hδ)
  exact ⟨x₀, x₁, hx.symm, h.le⟩

/-- Let $`x \in \alpha` and $`\delta > 0`. There are sequences $`(y_\nu)`, $`(z_\nu)` with
$`x = y_\nu + z_\nu` and $$`\|y_\nu\|_0 + 2^\nu \|z_\nu\|_1 \le K_\nu(x) + \delta` for all
$`\nu \in \mathbb{Z}`. -/
@[blueprint]
lemma exists_seq_decomp_le_kNorm_add {δ : ℝ≥0∞} (hδ : δ ≠ 0) (x : α) :
    ∃ y z : ℤ → α, ∀ ν : ℤ, y ν + z ν = x ∧
      ‖y ν‖ₑ[A.fst] + 2 ^ ν * ‖z ν‖ₑ[A.snd] ≤ A.kNorm (2 ^ ν) x + δ := by
  choose y z h using exists_decomp_le_kNorm_add A hδ x
  exact ⟨y, z, h⟩

/-- The norm
$$`\inf\Bigl\{\,\bigl\|\{2^{-\theta n}J(2^{n},a_{n})\}_{n \in \mathbb{Z}}\bigr\|_{\ell^{q}}
 : a \colon \mathbb{Z} \to \alpha \text{ finitely supported},\ \sum_{n}a_{n}=x\,\Bigr\}.` -/
@[blueprint]
def jInfNorm (θ : ℝ) (q : ℝ≥0∞) (x : α) : ℝ≥0∞ :=
  -- todo: what if we remove (_ : support.Finite)?
  ⨅ (a : ℤ → α) (_ : a.support.Finite) (_ : ∑ᶠ n, a n = x),
    discretePhiFunctional θ q (fun n ↦ A.jNorm (2 ^ n) (a n))

variable [Preorder α] [Abs α] [Abs.IsModulus α] 

/--
Let $`x = y_\mu + z_\mu` for all $`\mu \in \mathbb{Z}`, let $`a \in \mathbb{Z}`, $`m \in \mathbb{N}`
and $`r \in \alpha` with $`|r| \le |x|`, and put $`I = \{a, \dots, a+m\}`. Then there is
$`u \colon \mathbb{Z} \to \alpha` vanishing outside $`I` with
$`\sum_{\nu \in \mathbb{Z}} u_\nu = r` and,
for $`\nu \in I`:

* $`|u_\nu| \le |y_{\nu+1}|` if $`\nu < a + m`;
* $`|u_\nu| \le |z_\nu|` if $`a < \nu`;
* $`|u_\nu| \le |r|`.
-/
@[blueprint]
lemma exists_decomp_Icc {x : α} {y z : ℤ → α} (hyz : ∀ μ, y μ + z μ = x)
    (a : ℤ) (m : ℕ) {r : α} (hr : |r|ₑ ≤ |x|ₑ) :
    ∃ u : ℤ → α, u.support ⊆ Finset.Icc a (a + m) ∧
      ∑ᶠ ν, u ν = r ∧
      ∀ ν, |u ν|ₑ ≤ |r|ₑ ∧
        (ν < a + m → |u ν|ₑ ≤ |y (ν + 1)|ₑ) ∧ (a < ν → |u ν|ₑ ≤ |z ν|ₑ) := by
  sorry

/-- Lemma 1. -/
@[blueprint]
lemma jInfNorm_le_kNorm (θ : ℝ) (hθ : θ ∈ Ioo (0 : ℝ) 1) (q : ℝ≥0∞) :
    ∃ (C : ℝ≥0∞), C < ∞ ∧ ∀ x, jInfNorm A θ q x ≤ C * ‖x‖ₑ[A.kMethod θ q] :=
  sorry

end Lemma1

variable {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, AddCommGroup (α i)] {β : Type*}
  [AddCommMonoid β] [Preorder β] [Abs β]

variable (T : MultisubadditiveMap α β) (A : (i : ι) → Couple (α i)) (B : Couple β)

/- note: I am separating α₀ from the α_{m + 1} since it has a special meaning,
and it avoids the need to write m + 1. -/
variable (cα₀ : ℝ) (cα : ι → ℝ) (hα : ∀ k, cα k ≠ 0)

/- todo: we may need to assume 0 ≤ θ i ≤ 1 in the set. -/
/-- The set of $`ι`-tuples
$$`\Omega = \Bigl\{ (θ_i)_{i ∈ ι} \in [0,1]^ι :
  0 \le θ₀ \le 1
  \ \text{ and }\ T \colon \prod_{i} (A_i)_{\theta_i,q_i} \to (B)_{\theta_0,q} \text{ is bounded},\\
  \ \text{with } \theta_0 = \alpha_0 + \sum_{i} \alpha_i \theta_i,
  \ \text{for some } q_i, q \in (0,\infty] \Bigr\}.`
The value of the parameters $`q,q_i` are under an existential, and are not specified
for the points of this set.
-/
@[blueprint]
def Ω : Set (ι → ℝ) :=
  {θ | let θ₀ := cα₀ + ∑ i, cα i * θ i
    ∃ (q₀ : ℝ≥0∞) (q : ι → ℝ≥0∞),
    0 ≤ cα₀ + ∑ i, cα i * θ i ∧
    ∃ C, T.IsBoundedFor (fun i ↦ (A i).kMethod (θ i) (q i)) (B.kMethod θ₀ q₀) C}

section Theorem1

/-- Lemma 2, part 1. -/
@[blueprint]
lemma mem_Ω_iff : ∀ θ, θ ∈ Ω T A B cα₀ cα ↔
    let θ₀ := cα₀ + ∑ i, cα i
    ∃ C : ℝ≥0∞, C < ∞ ∧
    ∀ (a : (i : ι) → α i), ‖T a‖ₑ[B.kMethod θ₀ ∞] ≤
    C * ∏ i, ‖a i‖ₑ[(A i).fst] ^ (1 - θ i : ℝ) * ‖a i‖ₑ[(A i).snd] ^ (θ i : ℝ) := by
  sorry

/-- Lemma 2, part 2. -/
@[blueprint]
lemma knorm_of_mem_Ω : ∀ θ, θ ∈ Ω T A B cα₀ cα →
    let θ₀ := cα₀ + ∑ i, cα i
    ∃ C : ℝ≥0∞, C < ∞ ∧
    ∀ (t : ℝ≥0∞),
    ∀ (a : (i : ι) → α i), B.kNorm t (T a) ≤
    C * t ^ cα₀ * ∏ i, ‖a i‖ₑ[(A i).fst] ^ (1 - θ i) * ‖a i‖ₑ[(A i).snd] ^ (θ i) :=
  sorry

/-- The set $`Ω` is convex. In particular, if we do not care about the choice of $`q_i`s, then
$`T` is bounded in the convex hull of the $`(θ_i)_i`s for which it is already known to be bounded.
-/
@[blueprint
  (proofUses := [mem_Ω_iff])]
theorem convex_Ω : Convex ℝ (Ω T A B cα₀ cα) := sorry

end Theorem1


section Theorem2

/-- If $`(θ_i)_i` is in the interior of $`Ω`, then
$`T \colon \prod_i (A_i)_{θ_i,q_i} \to B_{θ_0,q_0}` is bounded for every choice of
exponents with $`q_0^{-1} \le \sum_i q_i^{-1}`.
This is stronger than mere membership in $`Ω`, where the $`q_i,q_0` are under an existential.
-/
@[blueprint
  (proofUses := [jInfNorm_le_kNorm, EQuasinorm.discreteKMethod_equiv_kmethod])]
theorem isBoundedOn_of_mem_interior_Ω (θ) (hθ : θ ∈ interior (Ω T A B cα₀ cα)) :
    let θ₀ := cα₀ + ∑ i, cα i
    ∀ (q₀ : ℝ≥0∞) (q : ι → ℝ≥0∞) (hq : q₀⁻¹ ≤ ∑ i, (q i)⁻¹),
    ∃ C, T.IsBoundedFor (fun i ↦ (A i).kMethod (θ i) (q i)) (B.kMethod θ₀ q₀) C :=
  sorry

end Theorem2

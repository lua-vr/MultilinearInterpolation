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

variable {M : Type*} [AddCommMonoid M] [Preorder M] [Modulus α M] [Modulus.IsDecomposable α M]

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
  -- review: llm proof
  have h0 := Modulus.IsDecomposable.modulus_zero_le (β := α)
  induction m generalizing a r with
  | zero =>
    refine ⟨fun ν ↦ if ν = a then r else 0, ?_, ?_, ?_⟩
    · intro ν hν
      by_cases h : ν = a <;> simp_all
    · rw [finsum_eq_single _ a (fun ν h ↦ by simp [h])]; simp
    · intro ν
      by_cases h : ν = a
      · subst h; simp
      · simp only [h, ite_false]
        exact ⟨h0 _, fun _ ↦ h0 _, fun _ ↦ h0 _⟩
  | succ m ih =>
    have hr' : |r|ₑ ≤ |y (a + 1)|ₑ + |z (a + 1)|ₑ :=
      hr.trans (by rw [← hyz (a + 1)]; exact Modulus.IsDecomposable.modulus_add_le _ _)
    obtain ⟨v, r', rfl, hvy, hrz, hvr, hrr⟩ := Modulus.IsDecomposable.exists_decomp hr'
    obtain ⟨u', hsupp, hsum, hu'⟩ := ih (a + 1) (hrr.trans hr)
    have hu'a : u' a = 0 := by
      by_contra h
      have := hsupp h
      simp at this
    have hu : (fun ν ↦ if ν = a then v else u' ν) =
        fun ν ↦ (Pi.single a v : ℤ → α) ν + u' ν := by
      funext ν; by_cases h : ν = a <;> simp [h, hu'a]
    refine ⟨fun ν ↦ if ν = a then v else u' ν, ?_, ?_, ?_⟩
    · intro ν hν
      by_cases h : ν = a
      · subst h; simp; omega
      · have := hsupp (by simpa [h] using hν)
        simp at this ⊢; omega
    · rw [hu, finsum_add_distrib, hsum]
      · rw [finsum_eq_single _ a (fun ν h ↦ by simp [h])]; simp
      · exact (Set.finite_singleton a).subset (Pi.support_single_subset)
      · exact (Finset.finite_toSet _).subset hsupp
    · intro ν
      by_cases h : ν = a
      · subst h
        simp only [ite_true]
        exact ⟨hvr, fun _ ↦ hvy, fun h ↦ absurd h (lt_irrefl _)⟩
      · simp only [h, ite_false]
        obtain ⟨h1, h2, h3⟩ := hu' ν
        refine ⟨h1.trans hrr, fun hν ↦ h2 (by push_cast at hν; omega), fun hν ↦ ?_⟩
        rcases eq_or_lt_of_le (show a + 1 ≤ ν by omega) with rfl | hν'
        · exact h1.trans hrz
        · exact h3 hν'

/--
Let $`N \ge 1` and $`x = y_\mu + z_\mu` for all $`\mu \in \mathbb{Z}`. Then there is
$`u \colon \mathbb{Z} \to \alpha` vanishing outside $`W_N = \{-N, \dots, N-1\}` with
$`\sum_{\nu \in \mathbb{Z}} u_\nu = x` and:

* $`|u_\nu| \le |y_{\nu+1}|` if $`\nu < N - 1`;
* $`|u_\nu| \le |z_\nu|` if $`-N < \nu`;
* $`|u_\nu| \le |x|`.
-/
@[blueprint]
lemma exists_decomp_Ico_symm {x : α} {y z : ℤ → α} (hyz : ∀ μ, y μ + z μ = x)
    {N : ℕ} (hN : 1 ≤ N) :
    ∃ u : ℤ → α, u.support ⊆ Finset.Ico (-N : ℤ) N ∧
      ∑ᶠ ν, u ν = x ∧
      ∀ ν, |u ν|ₑ ≤ |x|ₑ ∧
        (ν < N - 1 → |u ν|ₑ ≤ |y (ν + 1)|ₑ) ∧ (-N < ν → |u ν|ₑ ≤ |z ν|ₑ) := by
  -- review: llm proof
  obtain ⟨u, hs, hsum, hu⟩ := exists_decomp_Icc hyz (-N) (2 * N - 1) le_rfl
  refine ⟨u, fun ν hν ↦ ?_, hsum, fun ν ↦ ?_⟩
  · have := hs hν
    simp only [Finset.coe_Icc, Set.mem_Icc, Finset.coe_Ico, Set.mem_Ico] at this ⊢
    omega
  · obtain ⟨h1, h2, h3⟩ := hu ν
    exact ⟨h1, fun h ↦ h2 (by omega), h3⟩

omit [AddCommMonoid M] [Modulus.IsDecomposable α M] in
/--
Let $`\|y_\mu\|_0 + 2^\mu \|z_\mu\|_1 \le K_\mu(x) + \delta` for all $`\mu \in \mathbb{Z}`,
and let $`u` satisfy the conclusion of {name}`exists_decomp_Ico_symm`. Put
$`E_{-N} = 2^{-N}\|x\|_1`, $`E_{N-1} = \|x\|_0` and $`E_\nu = 0` otherwise. Then
$$`J_\nu(u_\nu) \le \max\bigl(K_{\nu+1}(x) + \delta,\ E_\nu\bigr)` for $`\nu \in W_N`.
-/
@[blueprint]
lemma jNorm_le_max_kNorm [A.fst.IsSolid] [A.snd.IsSolid] {x : α} {y z u : ℤ → α}
    {δ : ℝ≥0∞} {N : ℕ}
    (hyz : ∀ μ : ℤ, ‖y μ‖ₑ[A.fst] + 2 ^ μ * ‖z μ‖ₑ[A.snd] ≤ A.kNorm (2 ^ μ) x + δ)
    (hu : ∀ ν, |u ν|ₑ ≤ |x|ₑ ∧
      (ν < N - 1 → |u ν|ₑ ≤ |y (ν + 1)|ₑ) ∧ (-N < ν → |u ν|ₑ ≤ |z ν|ₑ))
    {ν : ℤ} (hν : ν ∈ Ico (-N : ℤ) N) :
    A.jNorm (2 ^ ν) (u ν) ≤ max (A.kNorm (2 ^ (ν + 1)) x + δ)
      (if ν = -N then 2 ^ ν * ‖x‖ₑ[A.snd] else if ν = N - 1 then ‖x‖ₑ[A.fst] else 0) := by
  -- review: llm proof
  obtain ⟨hux, huy, huz⟩ := hu ν
  obtain ⟨hν₀, hν₁⟩ := hν
  refine max_le ?_ ?_
  · rcases lt_or_eq_of_le (show ν ≤ N - 1 by omega) with h | rfl
    · refine le_max_of_le_left ?_
      grw [IsSolid.solid (huy h), ← hyz (ν + 1)]
      exact le_self_add
    · refine le_max_of_le_right ?_
      simp only [show (N : ℤ) - 1 ≠ -N by omega, ite_false, ite_true]
      exact IsSolid.solid hux
  · rcases lt_or_eq_of_le hν₀ with h | rfl
    · refine le_max_of_le_left ?_
      have hK : A.kNorm (2 ^ ν) x ≤ A.kNorm (2 ^ (ν + 1)) x :=
        iInf₂_mono fun _ _ ↦ by
          gcongr
          exacts [one_le_two, by omega]
      grw [IsSolid.solid (huz h), ← hK, ← hyz ν]
      exact le_add_self
    · refine le_max_of_le_right ?_
      simp only [ite_true]
      grw [IsSolid.solid hux]

/-- Lemma 1, for a couple of solid quasinorms with respect to a decomposable modulus. Janson
proves it for arbitrary quasinormed groups, by differences of almost optimal decompositions. -/
@[blueprint]
lemma jInfNorm_le_kNorm [A.fst.IsSolid] [A.snd.IsSolid] (θ : ℝ) (hθ : θ ∈ Ioo (0 : ℝ) 1)
    (q : ℝ≥0∞) :
    ∃ (C : ℝ≥0∞), C < ∞ ∧ ∀ x, jInfNorm A θ q x ≤ C * ‖x‖ₑ[A.kMethod θ q] :=
  sorry

end Lemma1

variable {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, AddCommGroup (α i)] {β : Type*}
  [AddCommMonoid β] {M : Type*} [AddCommMonoid M] [Preorder M] [Modulus β M]

variable (T : MultisubadditiveMap α β) (A : (i : ι) → Couple (α i)) (B : Couple β)

/- note: I am separating α₀ from the α_{m + 1} since it has a special meaning,
and it avoids the need to write m + 1. -/
variable (cα₀ : ℝ) (cα : ι → ℝ) (hα : ∀ k, cα k ≠ 0)

/- todo: we may need to assume 0 ≤ θ i ≤ 1 in the set. -/
/-- The set of $`ι`-tuples
$$`\begin{aligned}\Omega = \Bigl\{ (θ_i)_{i ∈ ι} \in [0,1]^ι :
  0 \le θ₀ \le 1
  \ \text{ and }\ T \colon \prod_{i} (A_i)_{\theta_i,q_i} \to (B)_{\theta_0,q} \text{ is bounded},\\
  \ \text{with } \theta_0 = \alpha_0 + \sum_{i} \alpha_i \theta_i,
  \ \text{for some } q_i, q \in (0,\infty] \Bigr\}.\end{aligned}`
The value of the parameters $`q,q_i` are under an existential, and are not specified
for the points of this set.
-/
@[blueprint]
def Ω : Set (ι → ℝ) :=
  {θ | let θ₀ := cα₀ + ∑ i, cα i * θ i
    ∃ (q₀ : ℝ≥0∞) (q : ι → ℝ≥0∞),
    0 ≤ cα₀ + ∑ i, cα i * θ i ∧
    ∃ C, T.IsBoundedFor (fun i ↦ (A i).kMethod (θ i) (q i)) (B.kMethod θ₀ q₀) C}

/- The source couples are solid with respect to decomposable moduli, as required by
`jInfNorm_le_kNorm`. They are not mentioned in the statements below, hence the `include`. -/
variable {Mα : ι → Type*} [∀ i, AddCommMonoid (Mα i)] [∀ i, Preorder (Mα i)]
  [∀ i, Modulus (α i) (Mα i)] [hMα : ∀ i, Modulus.IsDecomposable (α i) (Mα i)]
  [hA₀ : ∀ i, (A i).fst.IsSolid] [hA₁ : ∀ i, (A i).snd.IsSolid]

section Theorem1

/-- Lemma 2, part 1, direction (i) → (ii). It follows from the interpolation inequality
$`‖a‖_{θ,q} ≲ ‖a‖_0^{1-θ}‖a‖_1^θ` and needs no solidity. -/
@[blueprint]
lemma enorm_le_prod_of_mem_Ω : ∀ θ, θ ∈ Ω T A B cα₀ cα →
    let θ₀ := cα₀ + ∑ i, cα i * θ i
    ∃ C : ℝ≥0∞, C < ∞ ∧
    ∀ (a : (i : ι) → α i), ‖T a‖ₑ[B.kMethod θ₀ ∞] ≤
    C * ∏ i, ‖a i‖ₑ[(A i).fst] ^ (1 - θ i : ℝ) * ‖a i‖ₑ[(A i).snd] ^ (θ i : ℝ) := by
  sorry

/-- Lemma 2, part 2. -/
@[blueprint]
lemma knorm_of_mem_Ω : ∀ θ, θ ∈ Ω T A B cα₀ cα →
    let θ₀ := cα₀ + ∑ i, cα i * θ i
    ∃ C : ℝ≥0∞, C < ∞ ∧
    ∀ (t : ℝ≥0∞),
    ∀ (a : (i : ι) → α i), B.kNorm t (T a) ≤
    C * t ^ cα₀ * ∏ i, ‖a i‖ₑ[(A i).fst] ^ (1 - θ i) * ‖a i‖ₑ[(A i).snd] ^ (θ i) :=
  sorry

include hMα hA₀ hA₁

/-- Lemma 2, part 1, direction (ii) → (i). It uses {name}`jInfNorm_le_kNorm`, hence the
solidity hypotheses on the source couples. -/
@[blueprint
  (proofUses := [jInfNorm_le_kNorm])]
lemma mem_Ω_of_enorm_le_prod : ∀ θ,
    (let θ₀ := cα₀ + ∑ i, cα i * θ i
    ∃ C : ℝ≥0∞, C < ∞ ∧
    ∀ (a : (i : ι) → α i), ‖T a‖ₑ[B.kMethod θ₀ ∞] ≤
    C * ∏ i, ‖a i‖ₑ[(A i).fst] ^ (1 - θ i : ℝ) * ‖a i‖ₑ[(A i).snd] ^ (θ i : ℝ)) →
    θ ∈ Ω T A B cα₀ cα := by
  sorry

/-- Lemma 2, part 1. -/
@[blueprint
  (proofUses := [enorm_le_prod_of_mem_Ω, mem_Ω_of_enorm_le_prod])]
lemma mem_Ω_iff : ∀ θ, θ ∈ Ω T A B cα₀ cα ↔
    let θ₀ := cα₀ + ∑ i, cα i * θ i
    ∃ C : ℝ≥0∞, C < ∞ ∧
    ∀ (a : (i : ι) → α i), ‖T a‖ₑ[B.kMethod θ₀ ∞] ≤
    C * ∏ i, ‖a i‖ₑ[(A i).fst] ^ (1 - θ i : ℝ) * ‖a i‖ₑ[(A i).snd] ^ (θ i : ℝ) :=
  fun θ ↦ ⟨enorm_le_prod_of_mem_Ω T A B cα₀ cα θ, mem_Ω_of_enorm_le_prod T A B cα₀ cα θ⟩

/-- The set $`Ω` is convex. In particular, if we do not care about the choice of $`q_i`s, then
$`T` is bounded in the convex hull of the $`(θ_i)_i`s for which it is already known to be bounded.
-/
@[blueprint
  (proofUses := [mem_Ω_iff])]
theorem convex_Ω : Convex ℝ (Ω T A B cα₀ cα) := sorry

end Theorem1


section Theorem2

include hMα hA₀ hA₁

/-- If $`(θ_i)_i` is in the interior of $`Ω`, then
$`T \colon \prod_i (A_i)_{θ_i,q_i} \to B_{θ_0,q_0}` is bounded for every choice of
exponents with $`q_0^{-1} \le \sum_i q_i^{-1}`.
This is stronger than mere membership in $`Ω`, where the $`q_i,q_0` are under an existential.
-/
@[blueprint
  (proofUses := [jInfNorm_le_kNorm, EQuasinorm.discreteKMethod_equiv_kmethod])]
theorem isBoundedOn_of_mem_interior_Ω (θ) (hθ : θ ∈ interior (Ω T A B cα₀ cα)) :
    let θ₀ := cα₀ + ∑ i, cα i * θ i
    ∀ (q₀ : ℝ≥0∞) (q : ι → ℝ≥0∞) (hq : q₀⁻¹ ≤ ∑ i, (q i)⁻¹),
    ∃ C, T.IsBoundedFor (fun i ↦ (A i).kMethod (θ i) (q i)) (B.kMethod θ₀ q₀) C :=
  sorry

end Theorem2

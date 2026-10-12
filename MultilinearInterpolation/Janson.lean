/-
Copyright (c) 2026 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/

module

public import MultilinearInterpolation.EQuasinorm.Multisubadditive
public import MultilinearInterpolation.EQuasinorm.ESeminorm
public import MultilinearInterpolation.KMethod
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import MultilinearInterpolation.Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import MultilinearInterpolation.Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
Following
 *On interpolation of multi-linear operators* by Svante Janson.
-/

@[expose] public noncomputable section

open Set EQuasinorm MeasureTheory Filter Topology
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
  ⨅ (a : ℤ → α) (_ : a.support.Finite) (_ : ∑ᶠ n, a n = x),
    discretePhiFunctional θ q (fun n ↦ A.jNorm (2 ^ n) (a n))

/-- A finitely supported $`a \colon \mathbb{Z} \to \alpha` with $`\sum_n a_n = x` bounds
{name}`jInfNorm` by its cost. -/
@[blueprint]
lemma jInfNorm_le_discretePhiFunctional {θ : ℝ} {q : ℝ≥0∞} {x : α} {a : ℤ → α}
    (ha : a.support.Finite) (hsum : ∑ᶠ n, a n = x) :
    jInfNorm A θ q x ≤ discretePhiFunctional θ q (fun n ↦ A.jNorm (2 ^ n) (a n)) :=
  iInf_le_of_le a (iInf_le_of_le ha (iInf_le _ hsum))

/-- For $`q = 0`, {name}`jInfNorm` vanishes: the family equal to $`x` at $`0` and to $`0`
elsewhere costs $`0`. -/
@[simp, blueprint]
lemma jInfNorm_exponent_zero (θ : ℝ) (x : α) : jInfNorm A θ 0 x = 0 := by
  refine le_antisymm ((jInfNorm_le_discretePhiFunctional A (a := Pi.single 0 x)
    ((finite_singleton 0).subset Pi.support_single_subset) ?_).trans_eq
    (discretePhiFunctional_exponent_zero _)) zero_le
  rw [finsum_eq_single _ 0 fun i hi ↦ Pi.single_eq_of_ne hi _, Pi.single_eq_same]

/-- Swapping the two quasinorms replaces $`θ` by $`1 - θ` in {name}`jInfNorm`. -/
@[blueprint]
lemma jInfNorm_swap (θ : ℝ) (q : ℝ≥0∞) (x : α) :
    jInfNorm A.swap θ q x = jInfNorm A (1 - θ) q x := by
  refine (neg_injective.surjective_comp_right (γ := α)).iInf_congr _ fun a ↦ ?_
  refine iInf_congr_Prop ?_ fun _ ↦ iInf_congr_Prop ?_ fun _ ↦ ?_
  · rw [Function.support_comp_eq_preimage, Set.neg_preimage, Set.finite_neg]
  · exact (finsum_comp_equiv (Equiv.neg ℤ) (f := a)).congr_left
  · rw [← discretePhiFunctional_reflect]
    refine congrArg _ (funext fun n ↦ ?_)
    rw [Function.comp_apply, neg_neg]
    exact (jNorm_swap_zpow n (a n)).symm

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
$`u \colon \mathbb{Z} \to \alpha` vanishing outside $`\{-N, \dots, N-1\}` with
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
  obtain ⟨u, hs, hsum, hu⟩ := exists_decomp_Icc hyz (-N) (2 * N - 1) le_rfl
  refine ⟨u, fun ν hν ↦ ?_, hsum, fun ν ↦ ?_⟩
  · have := hs hν
    simp only [Finset.coe_Icc, Set.mem_Icc, Finset.coe_Ico, Set.mem_Ico] at this ⊢
    omega
  · obtain ⟨h1, h2, h3⟩ := hu ν
    exact ⟨h1, fun h ↦ h2 (by omega), h3⟩

/-- The error at the two ends of the decomposition of {name}`exists_decomp_Ico_symm`:
$$`E_N = 2^{-N}\|x\|_1\,\mathbf{1}_{\{-N\}} + \|x\|_0\,\mathbf{1}_{\{N-1\}}.` -/
@[blueprint]
def boundaryError (N : ℕ) (x : α) : ℤ → ℝ≥0∞ :=
  Pi.single (-N : ℤ) (2 ^ (-N : ℤ) * ‖x‖ₑ[A.snd]) + Pi.single ((N : ℤ) - 1) ‖x‖ₑ[A.fst]

/-- For $`0 < θ < 1`, $`q ≠ 0` and $`x ∈ A_0 ∩ A_1`, with $`r = \min(q, 1)`,
$`Φ_{θ,q}(E_N)^r → 0` as $`N → ∞`. The two terms of $`E_N` contribute
$`2^{(θ-1)N}\|x\|_1` and $`2^θ\,2^{-θN}\|x\|_0` to $`Φ_{θ,q}`. -/
@[blueprint]
lemma tendsto_discretePhiFunctional_boundaryError_rpow {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) 1)
    {q : ℝ≥0∞} (hq : q ≠ 0) {x : α} (hx : x ∈ A.inf.finiteLocus) :
    Tendsto (fun N : ℕ ↦ discretePhiFunctional θ q (boundaryError A N x) ^ (min q 1).toReal)
      atTop (𝓝 0) := by
  have hr : 0 < (min q 1).toReal := ENNReal.toReal_pos (by simp [hq]) (by simp)
  obtain ⟨hx₀, hx₁⟩ := mem_finiteLocus_inf.1 hx
  have key {a : ℝ} (ha : a < 0) {c : ℝ≥0∞} (hc : c ≠ ∞) :
      Tendsto (fun N : ℕ ↦ ((2 : ℝ≥0∞) ^ (a * N) * c) ^ (min q 1).toReal) atTop (𝓝 0) :=
    (zero_mul c ▸ ENNReal.Tendsto.mul_const ((ENNReal.tendsto_rpow_atBot_of_one_lt_base
      ENNReal.one_lt_two).comp (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg ha))
      (Or.inr hc)).ennrpow_const_nhds_zero hr
  refine tendsto_nhds_bot_mono' (add_zero (0 : ℝ≥0∞) ▸ (key (sub_neg.2 hθ.2) hx₁.ne).add
    (key (neg_neg_of_pos hθ.1) (c := 2 ^ θ * ‖x‖ₑ[A.fst]) (by finiteness))) fun N ↦ ?_
  grw [boundaryError, discretePhiFunctional_add_rpow_le hq, discretePhiFunctional_single hq,
    discretePhiFunctional_single hq]
  simp only [← mul_assoc, ← ENNReal.rpow_add_intCast two_ne_zero ENNReal.ofNat_ne_top,
    ← ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top]
  exact le_of_eq (by congr 4 <;> push_cast <;> ring)

omit [AddCommMonoid M] [Modulus.IsDecomposable α M] in
/--
Let $`\|y_\mu\|_0 + 2^\mu \|z_\mu\|_1 \le K_\mu(x) + \delta` for all $`\mu \in \mathbb{Z}`,
and let $`u` vanish outside $`\{-N, \dots, N-1\}` and satisfy the bounds of
{name}`exists_decomp_Ico_symm`. Then for every $`\nu \in \mathbb{Z}`, with $`E_N` the
{name}`boundaryError`,
$$`J_\nu(u_\nu) \le K_{\nu+1}(x) + \delta\,\mathbf{1}_{\{-N,\dots,N-1\}}(\nu) + E_N(\nu).`
For $`-N \le \nu \le N-1`, solidity gives $`\|u_\nu\|_0 \le \|y_{\nu+1}\|_0` and
$`2^\nu\|u_\nu\|_1 \le 2^\nu\|z_\nu\|_1`, both at most $`K_{\nu+1}(x) + \delta`, except at
$`\nu = N-1` and at $`\nu = -N` respectively, where only $`|u_\nu| \le |x|` is available.
-/
@[blueprint]
lemma jNorm_le_kNorm_add [A.fst.IsSolid] [A.snd.IsSolid] {x : α} {y z u : ℤ → α}
    {δ : ℝ≥0∞} {N : ℕ}
    (hyz : ∀ μ : ℤ, ‖y μ‖ₑ[A.fst] + 2 ^ μ * ‖z μ‖ₑ[A.snd] ≤ A.kNorm (2 ^ μ) x + δ)
    (hsupp : u.support ⊆ Ico (-N : ℤ) N)
    (hu : ∀ ν, |u ν|ₑ ≤ |x|ₑ ∧
      (ν < N - 1 → |u ν|ₑ ≤ |y (ν + 1)|ₑ) ∧ (-N < ν → |u ν|ₑ ≤ |z ν|ₑ)) (ν : ℤ) :
    A.jNorm (2 ^ ν) (u ν) ≤ A.kNorm (2 ^ (ν + 1)) x + (Ico (-N : ℤ) N).indicator (fun _ ↦ δ) ν +
      boundaryError A N x ν := by
  by_cases hν : ν ∈ Ico (-N : ℤ) N
  swap
  · simp [Function.notMem_support.1 (mt (@hsupp ν) hν)]
  obtain ⟨hux, huy, huz⟩ := hu ν
  rw [indicator_of_mem hν]
  obtain ⟨hν₀, hν₁⟩ := hν
  refine max_le ?_ ?_
  · rcases lt_or_eq_of_le (show ν ≤ N - 1 by omega) with h | rfl
    · grw [IsSolid.solid (huy h), ← hyz (ν + 1)]
      exact le_add_right le_self_add
    · rw [boundaryError, Pi.add_apply, Pi.single_eq_same]
      exact le_add_left (le_add_left (IsSolid.solid hux))
  · rcases lt_or_eq_of_le hν₀ with h | rfl
    · have hK : A.kNorm (2 ^ ν) x ≤ A.kNorm (2 ^ (ν + 1)) x :=
        monotone_kNorm (ENNReal.zpow_le_of_le one_le_two (by omega))
      grw [IsSolid.solid (huz h), ← hK, ← hyz ν]
      exact le_add_right le_add_self
    · rw [boundaryError, Pi.add_apply, Pi.single_eq_same]
      refine le_add_left (le_add_right ?_)
      grw [IsSolid.solid hux]

/--
For $`N ≥ 1` and $`δ > 0`, with $`E_N` the {name}`boundaryError`,
$$`\mathcal{J}(x) \le \Phi_{\theta,q}\bigl(\nu \mapsto K_{\nu+1}(x)
  + \delta\,\mathbf{1}_{\{-N,\dots,N-1\}}(\nu) + E_N(\nu)\bigr).`
The family $`u` of {name}`exists_decomp_Ico_symm` is admissible, and
{name}`jNorm_le_kNorm_add` bounds its cost termwise.
-/
@[blueprint]
lemma jInfNorm_le_discretePhiFunctional_kNorm_add [A.fst.IsSolid] [A.snd.IsSolid]
    (θ : ℝ) (q : ℝ≥0∞) {δ : ℝ≥0∞} (hδ : δ ≠ 0) {N : ℕ} (hN : 1 ≤ N) (x : α) :
    jInfNorm A θ q x ≤ discretePhiFunctional θ q
      ((fun ν : ℤ ↦ A.kNorm (2 ^ (ν + 1)) x) + (Ico (-N : ℤ) N).indicator (fun _ ↦ δ) +
        boundaryError A N x) := by
  obtain ⟨y, z, hyz⟩ := exists_seq_decomp_le_kNorm_add A hδ x
  obtain ⟨u, hsupp, hsum, hu⟩ := exists_decomp_Ico_symm (fun μ ↦ (hyz μ).1) hN
  refine (jInfNorm_le_discretePhiFunctional A ((Finset.finite_toSet _).subset hsupp) hsum).trans
    (discretePhiFunctional_mono fun ν ↦ ?_)
  exact jNorm_le_kNorm_add A (fun μ ↦ (hyz μ).2) (by simpa using hsupp) hu ν

/--
The estimate for fixed $`N ≥ 1` and $`δ > 0`. With $`r = \min(q, 1)`,
$$`\mathcal{J}(x)^r \le (2^\theta\|x\|_K)^r + \bigl(2^{N\theta}\delta\,(2N)^{1/q}\bigr)^r
  + \Phi_{\theta,q}(E_N)^r.`
The bound of {name}`jInfNorm_le_discretePhiFunctional_kNorm_add` splits into three terms by
{name}`discretePhiFunctional_add_rpow_le`; the first two are computed or estimated separately.
-/
@[blueprint]
lemma jInfNorm_rpow_le_of_delta [A.fst.IsSolid] [A.snd.IsSolid] {θ : ℝ} (hθ : 0 ≤ θ)
    {q : ℝ≥0∞} (hq : q ≠ 0) {δ : ℝ≥0∞} (hδ : δ ≠ 0) {N : ℕ} (hN : 1 ≤ N) (x : α) :
    jInfNorm A θ q x ^ (min q 1).toReal ≤
      (2 ^ θ * ‖x‖ₑ[A.discreteKMethod θ q]) ^ (min q 1).toReal +
      (2 ^ (N * θ) * δ * (2 * N : ℝ≥0∞) ^ (1 / q.toReal)) ^ (min q 1).toReal +
      discretePhiFunctional θ q (boundaryError A N x) ^ (min q 1).toReal := by
  grw [jInfNorm_le_discretePhiFunctional_kNorm_add A θ q hδ hN x,
    discretePhiFunctional_add_rpow_le hq, discretePhiFunctional_add_rpow_le hq,
    discretePhiFunctional_shift (fun k ↦ A.kNorm (2 ^ k) x),
    discretePhiFunctional_indicator_Ico_le hθ]
  rfl

/-- Lemma 1 with the constant $`2^\theta`, for the discrete $`K`-method, $`x ∈ A_0 ∩ A_1` and a
couple of solid quasinorms with respect to a decomposable modulus.

For $`q ≠ 0`, let $`N → ∞` in {name}`jInfNorm_rpow_le_of_delta`, with $`δ_N > 0` chosen so
that the middle term is at most $`N^{-r}`, where $`r = \min(q, 1)`. The last term tends to $`0`
by {name}`tendsto_discretePhiFunctional_boundaryError_rpow`. For $`q = 0` the left-hand side
vanishes ({name}`jInfNorm_exponent_zero`). -/
@[blueprint]
lemma jInfNorm_le_two_rpow_mul_discreteKMethod [A.fst.IsSolid] [A.snd.IsSolid]
    (θ : ℝ) (hθ : θ ∈ Ioo (0 : ℝ) 1) (q : ℝ≥0∞) : ∀ x ∈ A.inf.finiteLocus,
    jInfNorm A θ q x ≤ 2 ^ θ * ‖x‖ₑ[A.discreteKMethod θ q] := by
  intro x hx
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  have hr : 0 < (min q 1).toReal := ENNReal.toReal_pos (by simp [hq]) (by simp)
  have hδ (N : ℕ) : ∃ δ : ℝ≥0∞, 0 < δ ∧
      2 ^ ((N : ℝ) * θ) * δ * (2 * N : ℝ≥0∞) ^ (1 / q.toReal) < (N : ℝ≥0∞)⁻¹ := by
    obtain ⟨δ, h₀, h⟩ := ENNReal.exists_pos_mul_lt (a := 2 ^ ((N : ℝ) * θ) *
      (2 * N : ℝ≥0∞) ^ (1 / q.toReal)) (b := (N : ℝ≥0∞)⁻¹) (by finiteness) (by simp)
    exact ⟨δ, h₀, by rwa [mul_left_comm, ← mul_assoc] at h⟩
  choose δ hδ₀ hδ using hδ
  have := ge_of_tendsto
    ((tendsto_const_nhds.add (ENNReal.tendsto_inv_nat_nhds_zero.ennrpow_const_nhds_zero hr)).add
      (tendsto_discretePhiFunctional_boundaryError_rpow A hθ hq hx))
    ((eventually_ge_atTop 1).mono fun N hN ↦
      (jInfNorm_rpow_le_of_delta A hθ.1.le hq (hδ₀ N).ne' hN x).trans (by grw [(hδ N).le]))
  rw [add_zero, add_zero] at this
  exact (ENNReal.rpow_le_rpow_iff hr).1 this

/-- Lemma 1 with the constant $`2^{\min(\theta, 1-\theta)}`, for the discrete $`K`-method,
$`x ∈ A_0 ∩ A_1` and a couple of solid quasinorms with respect to a decomposable modulus. The
constant is optimal for $`q = \infty`. Janson proves Lemma 1, without explicit constant, for
arbitrary quasinormed groups, by differences of almost optimal decompositions.

The constant $`2^{1-\theta}` follows from {name}`jInfNorm_le_two_rpow_mul_discreteKMethod` for the
swapped couple, by {name}`jInfNorm_swap` and {name}`Couple.enorm_discreteKMethod_swap`.

The restriction to $`A_0 ∩ A_1` is necessary: finite sums of elements of finite $`J`-norm lie in
$`A_0 ∩ A_1`, so {name}`jInfNorm` is infinite outside it for $`q > 0`. -/
@[blueprint]
lemma jInfNorm_le_discreteKMethod [A.fst.IsSolid] [A.snd.IsSolid]
    (θ : ℝ) (hθ : θ ∈ Ioo (0 : ℝ) 1) (q : ℝ≥0∞) : ∀ x ∈ A.inf.finiteLocus,
    jInfNorm A θ q x ≤ 2 ^ min θ (1 - θ) * ‖x‖ₑ[A.discreteKMethod θ q] := by
  intro x hx
  rcases min_choice θ (1 - θ) with h | h <;> rw [h]
  · exact jInfNorm_le_two_rpow_mul_discreteKMethod A θ hθ q x hx
  · have := jInfNorm_le_two_rpow_mul_discreteKMethod A.swap (1 - θ)
      ⟨sub_pos.2 hθ.2, sub_lt_self 1 hθ.1⟩ q x (finiteLocus_inf_comm A.fst A.snd ▸ hx)
    rwa [jInfNorm_swap, Couple.enorm_discreteKMethod_swap, sub_sub_cancel] at this

#simp 2 + 2

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
for the points of this set. Boundedness is only required on $`∏_i (A_i)_0 ∩ (A_i)_1`, where
{name}`jInfNorm_le_discreteKMethod` holds.
-/
@[blueprint]
def Ω : Set (ι → ℝ) :=
  {θ | let θ₀ := cα₀ + ∑ i, cα i * θ i
    ∃ (q₀ : ℝ≥0∞) (q : ι → ℝ≥0∞),
    0 ≤ cα₀ + ∑ i, cα i * θ i ∧
    ∃ C, T.IsBoundedForOn (fun i ↦ (A i).kMethod (θ i) (q i)) (B.kMethod θ₀ q₀) C
      (fun i x ↦ x ∈ (A i).inf.finiteLocus ∧ ‖x‖ₑ[(A i).kMethod (θ i) (q i)] < ∞)}

/- The source couples are solid with respect to decomposable moduli, as required by
`jInfNorm_le_discreteKMethod`. They are not mentioned in the statements below, hence the
`include`. -/
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
    ∀ (a : (i : ι) → α i), (∀ i, a i ∈ (A i).inf.finiteLocus) →
    ‖T a‖ₑ[B.kMethod θ₀ ∞] ≤
    C * ∏ i, ‖a i‖ₑ[(A i).fst] ^ (1 - θ i : ℝ) * ‖a i‖ₑ[(A i).snd] ^ (θ i : ℝ) := by
  sorry

/-- Lemma 2, part 2. -/
@[blueprint]
lemma knorm_of_mem_Ω : ∀ θ, θ ∈ Ω T A B cα₀ cα →
    let θ₀ := cα₀ + ∑ i, cα i * θ i
    ∃ C : ℝ≥0∞, C < ∞ ∧
    ∀ (t : ℝ≥0∞),
    ∀ (a : (i : ι) → α i), (∀ i, a i ∈ (A i).inf.finiteLocus) →
    B.kNorm t (T a) ≤
    C * t ^ cα₀ * ∏ i, ‖a i‖ₑ[(A i).fst] ^ (1 - θ i) * ‖a i‖ₑ[(A i).snd] ^ (θ i) :=
  sorry

include hMα hA₀ hA₁

/-- Lemma 2, part 1, direction (ii) → (i). It uses {name}`jInfNorm_le_discreteKMethod`, hence the
solidity hypotheses on the source couples. -/
@[blueprint
  (proofUses := [jInfNorm_le_discreteKMethod, EQuasinorm.discreteKMethod_equiv_kmethod])]
lemma mem_Ω_of_enorm_le_prod : ∀ θ,
    (let θ₀ := cα₀ + ∑ i, cα i * θ i
    ∃ C : ℝ≥0∞, C < ∞ ∧
    ∀ (a : (i : ι) → α i), (∀ i, a i ∈ (A i).inf.finiteLocus) →
    ‖T a‖ₑ[B.kMethod θ₀ ∞] ≤
    C * ∏ i, ‖a i‖ₑ[(A i).fst] ^ (1 - θ i : ℝ) * ‖a i‖ₑ[(A i).snd] ^ (θ i : ℝ)) →
    θ ∈ Ω T A B cα₀ cα := by
  sorry

/-- Lemma 2, part 1. -/
@[blueprint
  (proofUses := [enorm_le_prod_of_mem_Ω, mem_Ω_of_enorm_le_prod])]
lemma mem_Ω_iff : ∀ θ, θ ∈ Ω T A B cα₀ cα ↔
    let θ₀ := cα₀ + ∑ i, cα i * θ i
    ∃ C : ℝ≥0∞, C < ∞ ∧
    ∀ (a : (i : ι) → α i), (∀ i, a i ∈ (A i).inf.finiteLocus) →
    ‖T a‖ₑ[B.kMethod θ₀ ∞] ≤
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
As in $`Ω`, boundedness is on $`∏_i (A_i)_0 ∩ (A_i)_1`.
-/
@[blueprint
  (proofUses := [jInfNorm_le_discreteKMethod, EQuasinorm.discreteKMethod_equiv_kmethod])]
theorem isBoundedOn_of_mem_interior_Ω (θ) (hθ : θ ∈ interior (Ω T A B cα₀ cα)) :
    let θ₀ := cα₀ + ∑ i, cα i * θ i
    ∀ (q₀ : ℝ≥0∞) (q : ι → ℝ≥0∞) (hq : q₀⁻¹ ≤ ∑ i, (q i)⁻¹),
    ∃ C, T.IsBoundedForOn (fun i ↦ (A i).kMethod (θ i) (q i)) (B.kMethod θ₀ q₀) C
      (fun i x ↦ x ∈ (A i).inf.finiteLocus ∧ ‖x‖ₑ[(A i).kMethod (θ i) (q i)] < ∞) :=
  sorry

end Theorem2

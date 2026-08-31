/-
Copyright (c) 2026 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import MultilinearInterpolation.EQuasinorm.ESeminorm

set_option doc.verso false

/-!
# Scratch: the Aoki-Rolewicz theorem

A complete proof of Bergh-Löfström, *Interpolation Spaces, An Introduction*, **Lemma 3.10.1**:

> Suppose that `A` is a `c`-normed Abelian group and let `ρ` be defined by the equation
> `(2c)^ρ = 2`.  Then there is a `1`-norm `‖·‖*` on `A` such that
> `‖a‖* ≤ ‖a‖^ρ ≤ 2 ‖a‖*`.                                                            (4)

The book's `ρ` is called `p` here.  The hypothesis is kept in the book's form `(2 * A.C) ^ p = 2`;
see `EQuasinorm.C_eq_rpow_iff` for the closed form `A.C = 2 ^ (p⁻¹ - 1)`.

The construction is the book's:
`‖a‖* = inf {∑ ‖aⱼ‖^p : ∑ aⱼ = a}` (`EQuasinorm.starNorm`).

The heart of the proof is inequality (5) of the book,
`‖∑ⱼ aⱼ‖^p ≤ maxⱼ (2 ^ νⱼ * ‖aⱼ‖^p)`  whenever `νⱼ ≥ 0` and `∑ⱼ 2 ^ (-νⱼ) ≤ 1`,
proved here as `EQuasinorm.enorm_sum_rpow_le_of_weights` in the scaled form that avoids negative
exponents: the weights are natural numbers `wⱼ = 2 ^ (k - νⱼ)` with `∑ⱼ wⱼ ≤ 2 ^ k`.

The step the book dispatches with "it is easily seen that there are two disjoint, nonempty sets
`I₁` and `I₂`" is `Finset.exists_split_sum_le` below; it rests on the fact that a family of powers
of two, each dividing `N` and of total mass at least `N`, has a subfragment of mass exactly `N`
(`Finset.exists_subset_sum_eq_of_dvd`).
-/

noncomputable section

open scoped ENNReal NNReal

/-! ## Dyadic combinatorics

The purely arithmetic content of the splitting step in the book's induction.
-/

section Dyadic

variable {ι : Type*}

/-- Two powers of two are ordered by divisibility. -/
private lemma dvd_of_le_of_pow_two {a b : ℕ} (ha : ∃ e : ℕ, a = 2 ^ e) (hb : ∃ e : ℕ, b = 2 ^ e)
    (hab : a ≤ b) : a ∣ b := by
  obtain ⟨e, rfl⟩ := ha
  obtain ⟨f, rfl⟩ := hb
  exact pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right Nat.one_lt_two).1 hab)

/-- **Exact dyadic subset sum.** If every weight `w j`, `j ∈ s`, is a power of two dividing `N`,
and the total weight is at least `N`, then some subfamily has total weight exactly `N`.

Greedily remove a largest weight: it divides `N`, and every remaining weight divides both `N` and
it, hence divides `N - w j₀`. -/
theorem Finset.exists_subset_sum_eq_of_dvd [DecidableEq ι] {w : ι → ℕ}
    (hw : ∀ j, ∃ e : ℕ, w j = 2 ^ e) (s : Finset ι) :
    ∀ N : ℕ, (∀ j ∈ s, w j ∣ N) → N ≤ ∑ j ∈ s, w j → ∃ I ⊆ s, ∑ j ∈ I, w j = N := by
  induction s using Finset.strongInduction with
  | _ s ih =>
    intro N hdvd hle
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · exact ⟨∅, Finset.empty_subset _, by simp⟩
    have hs : s.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro rfl
      simp only [Finset.sum_empty, Nat.le_zero] at hle
      omega
    obtain ⟨j₀, hj₀, hmax⟩ := s.exists_max_image w hs
    have hj₀N : w j₀ ≤ N := Nat.le_of_dvd hN (hdvd j₀ hj₀)
    have herase : ∑ j ∈ s.erase j₀, w j + w j₀ = ∑ j ∈ s, w j := Finset.sum_erase_add s w hj₀
    obtain ⟨I, hIs, hIsum⟩ :=
      ih (s.erase j₀) (Finset.erase_ssubset hj₀) (N - w j₀)
        (fun j hj => Nat.dvd_sub (hdvd j (Finset.mem_of_mem_erase hj))
          (dvd_of_le_of_pow_two (hw j) (hw j₀) (hmax j (Finset.mem_of_mem_erase hj))))
        (by omega)
    have hj₀I : j₀ ∉ I := fun h => (Finset.mem_erase.1 (hIs h)).1 rfl
    refine ⟨insert j₀ I, Finset.insert_subset hj₀ (hIs.trans (Finset.erase_subset _ _)), ?_⟩
    rw [Finset.sum_insert hj₀I, hIsum]
    omega

/-- **The splitting step** of the book's induction: "it is easily seen that there are two disjoint,
nonempty sets `I₁` and `I₂`".

A family of at least two dyadic weights, each dividing `N`, of total mass at most `2 * N`, splits
into two nonempty parts of mass at most `N` each. -/
theorem Finset.exists_split_sum_le [DecidableEq ι] {w : ι → ℕ} (hw : ∀ j, ∃ e : ℕ, w j = 2 ^ e)
    {s : Finset ι} {N : ℕ} (hN : 0 < N) (hdvd : ∀ j ∈ s, w j ∣ N)
    (hsum : ∑ j ∈ s, w j ≤ 2 * N) (hcard : 2 ≤ s.card) :
    ∃ I ⊆ s, I.Nonempty ∧ (s \ I).Nonempty ∧
      ∑ j ∈ I, w j ≤ N ∧ ∑ j ∈ s \ I, w j ≤ N := by
  rcases le_or_gt (∑ j ∈ s, w j) N with hle | hlt
  · -- The whole family already fits into one part; peel off a single element.
    obtain ⟨j₀, hj₀⟩ := Finset.card_pos.1 (by omega : 0 < s.card)
    have hsub : ({j₀} : Finset ι) ⊆ s := Finset.singleton_subset_iff.2 hj₀
    refine ⟨{j₀}, hsub, Finset.singleton_nonempty _, ?_, ?_, ?_⟩
    · rw [Finset.sdiff_nonempty]
      intro hss
      have := Finset.card_le_card hss
      simp only [Finset.card_singleton] at this
      omega
    · exact le_trans (by simpa using Finset.single_le_sum (fun i _ => Nat.zero_le (w i)) hj₀) hle
    · exact le_trans (Finset.sum_le_sum_of_subset (Finset.sdiff_subset)) hle
  · -- Otherwise cut out a subfamily of mass exactly `N`; the rest has mass `≤ 2N - N = N`.
    obtain ⟨I, hIs, hIsum⟩ := Finset.exists_subset_sum_eq_of_dvd hw s N hdvd hlt.le
    have hsplit : ∑ j ∈ s \ I, w j + ∑ j ∈ I, w j = ∑ j ∈ s, w j := Finset.sum_sdiff hIs
    refine ⟨I, hIs, ?_, ?_, hIsum.le, by omega⟩
    · rw [Finset.nonempty_iff_ne_empty]
      rintro rfl
      simp only [Finset.sum_empty] at hIsum
      omega
    · rw [Finset.nonempty_iff_ne_empty]
      rintro he
      rw [he, Finset.sum_empty] at hsplit
      omega

end Dyadic

/-! ## Inequality (5): the induction

Everything below takes place in a `c`-normed monoid `A` with `(2 * A.C) ^ p = 2`.
-/

namespace EQuasinorm

variable {α : Type*} [AddCommMonoid α] {A : EQuasinorm α} {p : ℝ}

/-- The `C`-triangle inequality, raised to the power `p`, becomes `2`-subadditivity for `max`.
This is the only place where the defining equation `(2 * A.C) ^ p = 2` is used. -/
lemma enorm_add_rpow_le_two_mul_max (hp : 0 ≤ p) (h2 : (2 * A.C) ^ p = 2) (x y : α) :
    ‖x + y‖ₑ[A] ^ p ≤ 2 * max (‖x‖ₑ[A] ^ p) (‖y‖ₑ[A] ^ p) := by
  have hmono : Monotone fun z : ℝ≥0∞ => z ^ p := fun _ _ h => ENNReal.rpow_le_rpow h hp
  calc ‖x + y‖ₑ[A] ^ p ≤ (2 * A.C * max ‖x‖ₑ[A] ‖y‖ₑ[A]) ^ p := by
        refine ENNReal.rpow_le_rpow ?_ hp
        calc ‖x + y‖ₑ[A] ≤ A.C * (‖x‖ₑ[A] + ‖y‖ₑ[A]) := A.enorm_add_le_mul x y
          _ ≤ A.C * (2 * max ‖x‖ₑ[A] ‖y‖ₑ[A]) := by
              gcongr
              rw [two_mul]
              exact add_le_add (le_max_left _ _) (le_max_right _ _)
          _ = 2 * A.C * max ‖x‖ₑ[A] ‖y‖ₑ[A] := by ring
    _ = 2 * max (‖x‖ₑ[A] ^ p) (‖y‖ₑ[A] ^ p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp, h2, hmono.map_max]

/-- **Inequality (5)** of Bergh-Löfström, Lemma 3.10.1, in scaled form.

The book's weights are `2 ^ (-νⱼ)` subject to `νⱼ ≥ 0` and `∑ⱼ 2 ^ (-νⱼ) ≤ 1`; here they are
`w j / 2 ^ k` with `w j` a power of two dividing `2 ^ k` and `∑ⱼ w j ≤ 2 ^ k`, which keeps every
exponent a natural number.  The book's conclusion `‖∑ aⱼ‖ ^ p ≤ maxⱼ (2 ^ νⱼ * ‖aⱼ‖ ^ p)` is
phrased as: any `B` dominating each `2 ^ νⱼ * ‖aⱼ‖ ^ p` dominates `‖∑ aⱼ‖ ^ p`.

Unlike the book we induct on `k` rather than on the number of summands, so the two parts produced
by the splitting step need not be smaller -- only of half the mass.
-/
theorem enorm_sum_rpow_le_of_weights (hp : 0 < p) (h2 : (2 * A.C) ^ p = 2)
    {ι : Type*} [DecidableEq ι] {w : ι → ℕ} (hw : ∀ j, ∃ e : ℕ, w j = 2 ^ e) :
    ∀ (k : ℕ) (s : Finset ι) (a : ι → α) (B : ℝ≥0∞), (∀ j ∈ s, w j ∣ 2 ^ k) →
      ∑ j ∈ s, w j ≤ 2 ^ k → (∀ j ∈ s, (2 : ℝ≥0∞) ^ k * ‖a j‖ₑ[A] ^ p ≤ w j * B) →
      ‖∑ j ∈ s, a j‖ₑ[A] ^ p ≤ B := by
  have hone : ∀ j, 1 ≤ w j := fun j => by
    obtain ⟨e, he⟩ := hw j; exact he ▸ Nat.one_le_two_pow
  -- The cases `s = ∅` and `s = {j}`, for every `k`.  (`n = 1` in the book.)
  have small : ∀ (k : ℕ) (s : Finset ι) (a : ι → α) (B : ℝ≥0∞), s.card ≤ 1 →
      (∀ j ∈ s, w j ∣ 2 ^ k) → (∀ j ∈ s, (2 : ℝ≥0∞) ^ k * ‖a j‖ₑ[A] ^ p ≤ w j * B) →
      ‖∑ j ∈ s, a j‖ₑ[A] ^ p ≤ B := by
    intro k s a B hcard hdvd hb
    rcases Finset.eq_empty_or_nonempty s with rfl | ⟨j, hj⟩
    · simp [ENNReal.zero_rpow_of_pos hp]
    have hsj : s = {j} := Finset.eq_singleton_iff_unique_mem.2
      ⟨hj, fun x hx => Finset.card_le_one.1 hcard x hx j hj⟩
    subst hsj
    rw [Finset.sum_singleton]
    have hle : (w j : ℝ≥0∞) ≤ 2 ^ k := by
      have h := Nat.le_of_dvd (by positivity) (hdvd j hj)
      calc (w j : ℝ≥0∞) ≤ ((2 ^ k : ℕ) : ℝ≥0∞) := Nat.cast_le.2 h
        _ = 2 ^ k := by push_cast; ring
    refine (ENNReal.mul_le_mul_iff_right (a := (2 : ℝ≥0∞) ^ k) (pow_ne_zero _ two_ne_zero)
      (by finiteness)).1 ?_
    exact (hb j hj).trans (mul_le_mul_left hle B)
  intro k
  induction k with
  | zero =>
    intro s a B hdvd hsum hb
    refine small 0 s a B ?_ hdvd hb
    have hcard : s.card ≤ ∑ j ∈ s, w j := by
      rw [Finset.card_eq_sum_ones]
      exact Finset.sum_le_sum fun j _ => hone j
    simp only [pow_zero] at hsum
    omega
  | succ k ih =>
    intro s a B hdvd hsum hb
    rcases le_or_gt s.card 1 with hcard | hcard
    · exact small (k + 1) s a B hcard hdvd hb
    -- With at least two summands present, no single weight can exceed `2 ^ k`.
    have hdvd' : ∀ j ∈ s, w j ∣ 2 ^ k := by
      intro j hj
      obtain ⟨j', hj', hne⟩ : ∃ j' ∈ s, j' ≠ j := by
        by_contra hc
        push Not at hc
        have hsub : s ⊆ {j} := fun x hx => Finset.mem_singleton.2 (hc x hx)
        have := Finset.card_le_card hsub
        simp only [Finset.card_singleton] at this
        omega
      have hpair : w j + w j' ≤ ∑ i ∈ s, w i := by
        have hsub : ({j, j'} : Finset ι) ⊆ s := by
          intro x hx
          rcases Finset.mem_insert.1 hx with rfl | hx
          · exact hj
          · rw [Finset.mem_singleton.1 hx]; exact hj'
        calc w j + w j' = ∑ i ∈ ({j, j'} : Finset ι), w i := by
              rw [Finset.sum_insert (by simpa using Ne.symm hne), Finset.sum_singleton]
          _ ≤ ∑ i ∈ s, w i := Finset.sum_le_sum_of_subset hsub
      obtain ⟨e, he⟩ := hw j
      have hlt : (2 : ℕ) ^ e < 2 ^ (k + 1) := by
        have := hone j'
        omega
      exact he ▸ pow_dvd_pow 2 (by
        have := (Nat.pow_lt_pow_iff_right Nat.one_lt_two).1 hlt
        omega)
    obtain ⟨I, hIs, -, -, hIsum, hIcsum⟩ :=
      Finset.exists_split_sum_le hw (N := 2 ^ k) (by positivity) hdvd'
        (by rw [show 2 * 2 ^ k = 2 ^ (k + 1) by ring]; exact hsum) hcard
    -- Halving `B` alongside `k`.
    have hb' : ∀ t : Finset ι, t ⊆ s → ∀ j ∈ t,
        (2 : ℝ≥0∞) ^ k * ‖a j‖ₑ[A] ^ p ≤ w j * (B / 2) := by
      intro t hts j hj
      rw [← mul_div_assoc, ENNReal.le_div_iff_mul_le (Or.inl (by norm_num))
        (Or.inl (by norm_num))]
      calc (2 : ℝ≥0∞) ^ k * ‖a j‖ₑ[A] ^ p * 2 = 2 ^ (k + 1) * ‖a j‖ₑ[A] ^ p := by ring
        _ ≤ w j * B := hb j (hts hj)
    have hI : ‖∑ j ∈ I, a j‖ₑ[A] ^ p ≤ B / 2 :=
      ih I a (B / 2) (fun j hj => hdvd' j (hIs hj)) hIsum (hb' I hIs)
    have hIc : ‖∑ j ∈ s \ I, a j‖ₑ[A] ^ p ≤ B / 2 :=
      ih (s \ I) a (B / 2) (fun j hj => hdvd' j (Finset.sdiff_subset hj)) hIcsum
        (hb' _ Finset.sdiff_subset)
    rw [← Finset.sum_sdiff hIs]
    calc ‖∑ j ∈ s \ I, a j + ∑ j ∈ I, a j‖ₑ[A] ^ p
        ≤ 2 * max (‖∑ j ∈ s \ I, a j‖ₑ[A] ^ p) (‖∑ j ∈ I, a j‖ₑ[A] ^ p) :=
          enorm_add_rpow_le_two_mul_max hp.le h2 _ _
      _ ≤ 2 * (B / 2) := by gcongr; exact max_le hIc hI
      _ = B := ENNReal.mul_div_cancel' (by norm_num) (by norm_num)

/-- The last paragraph of the book's proof: given `a = a₁ + ⋯ + aₙ`, put `M = ∑ⱼ ‖aⱼ‖ ^ p` and
choose `νⱼ` with `2 ^ (-νⱼ) ≤ ‖aⱼ‖^p / M ≤ 2 ^ (-νⱼ + 1)`; then `∑ⱼ 2 ^ (-νⱼ) ≤ 1`, so
inequality (5) gives `‖a‖ ^ p ≤ maxⱼ (2 ^ νⱼ * ‖aⱼ‖ ^ p) ≤ 2 M`.

The book's quasi-norms satisfy `‖a‖ = 0 ↔ a = 0`, so every `‖aⱼ‖ ^ p` is positive and `νⱼ` is
well defined.  An `EQuasinorm` need not be definite, so the summands of zero norm are collected
separately and given weight `1`; the exponents chosen for the others leave room for them, because
`2 ^ (-νⱼ)` is chosen *strictly* below `‖aⱼ‖^p / M`. -/
theorem enorm_sum_rpow_le_two_mul_sum (hp : 0 < p) (h2 : (2 * A.C) ^ p = 2)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → α) :
    ‖∑ j ∈ s, a j‖ₑ[A] ^ p ≤ 2 * ∑ j ∈ s, ‖a j‖ₑ[A] ^ p := by
  classical
  set b : ι → ℝ≥0∞ := fun j => ‖a j‖ₑ[A] ^ p with hbdef
  set M : ℝ≥0∞ := ∑ j ∈ s, b j with hMdef
  rcases eq_or_ne M ∞ with hMtop | hMtop
  · rw [hMtop, ENNReal.mul_top (by norm_num)]
    exact le_top
  -- `P` collects the summands of nonzero norm.
  set P : Finset ι := s.filter (fun j => b j ≠ 0) with hPdef
  have hPs : P ⊆ s := Finset.filter_subset _ _
  have hmemP : ∀ j ∈ P, b j ≠ 0 := fun j hj => (Finset.mem_filter.1 hj).2
  have hbM : ∀ j ∈ s, b j ≤ M := fun j hj => Finset.single_le_sum (fun _ _ => zero_le) hj
  have hbtop : ∀ j ∈ s, b j ≠ ∞ := fun j hj h => hMtop (top_le_iff.1 (h ▸ hbM j hj))
  have hPM : ∑ j ∈ P, b j = M := by
    rw [hMdef]
    refine Finset.sum_subset hPs fun j hj hjP => ?_
    by_contra hc
    exact hjP (Finset.mem_filter.2 ⟨hj, hc⟩)
  -- The exponents `νⱼ` of the book.
  have hex : ∀ j ∈ P, ∃ n : ℕ, M < 2 ^ n * b j ∧ (2 : ℝ≥0∞) ^ n * b j ≤ 2 * M := by
    intro j hj
    have hj' : j ∈ s := hPs hj
    have hb0 : b j ≠ 0 := hmemP j hj
    have hbt : b j ≠ ∞ := hbtop j hj'
    have hexists : ∃ n : ℕ, M < 2 ^ n * b j := by
      obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ENNReal.div_lt_top hMtop hb0).ne
      rw [ENNReal.div_lt_iff (Or.inl hb0) (Or.inl hbt)] at hn
      refine ⟨n, hn.trans_le (mul_le_mul_left ?_ _)⟩
      calc (n : ℝ≥0∞) ≤ ((2 ^ n : ℕ) : ℝ≥0∞) := Nat.cast_le.2 Nat.lt_two_pow_self.le
        _ = 2 ^ n := by push_cast; ring
    have hspec : M < 2 ^ Nat.find hexists * b j := Nat.find_spec hexists
    obtain ⟨m, hm⟩ : ∃ m, Nat.find hexists = m + 1 := by
      refine ⟨Nat.find hexists - 1, ?_⟩
      rcases Nat.eq_zero_or_pos (Nat.find hexists) with h0 | h0
      · rw [h0, pow_zero, one_mul] at hspec
        exact absurd (hbM j hj') (not_le.2 hspec)
      · omega
    refine ⟨Nat.find hexists, hspec, ?_⟩
    have hmin : ¬ M < 2 ^ m * b j := Nat.find_min hexists (by omega)
    calc (2 : ℝ≥0∞) ^ Nat.find hexists * b j = 2 * (2 ^ m * b j) := by rw [hm]; ring
      _ ≤ 2 * M := by gcongr; exact not_lt.1 hmin
  choose! ν hν₁ hν₂ using hex
  set k : ℕ := s.sup ν with hkdef
  have hνk : ∀ j ∈ P, ν j ≤ k := fun j hj => Finset.le_sup (f := ν) (hPs hj)
  -- The dyadic masses `2 ^ (k - νⱼ)` sum to *strictly* less than `2 ^ k`.
  have hPsum : ∑ j ∈ P, 2 ^ (k - ν j) < 2 ^ k := by
    rcases Finset.eq_empty_or_nonempty P with hPe | hPne
    · simp [hPe]
    have hM0 : M ≠ 0 := by
      obtain ⟨j, hj⟩ := hPne
      exact fun h => hmemP j hj (le_antisymm (h ▸ hbM j (hPs hj)) zero_le)
    have key : ∀ j ∈ P, ((2 : ℝ≥0∞) ^ (k - ν j)) * M < 2 ^ k * b j := by
      intro j hj
      calc ((2 : ℝ≥0∞) ^ (k - ν j)) * M < 2 ^ (k - ν j) * (2 ^ ν j * b j) :=
            ENNReal.mul_lt_mul_right (pow_ne_zero _ two_ne_zero) (by finiteness) (hν₁ j hj)
        _ = 2 ^ k * b j := by
            rw [← mul_assoc, ← pow_add]
            congr 2
            have := hνk j hj
            omega
    have hlt : (∑ j ∈ P, ((2 : ℝ≥0∞) ^ (k - ν j))) * M < 2 ^ k * M := by
      calc (∑ j ∈ P, ((2 : ℝ≥0∞) ^ (k - ν j))) * M
          = ∑ j ∈ P, ((2 : ℝ≥0∞) ^ (k - ν j)) * M := Finset.sum_mul ..
        _ < ∑ j ∈ P, (2 : ℝ≥0∞) ^ k * b j := ENNReal.sum_lt_sum_of_nonempty hPne key
        _ = 2 ^ k * M := by rw [← Finset.mul_sum, hPM]
    have hlt' : (∑ j ∈ P, ((2 : ℝ≥0∞) ^ (k - ν j))) < 2 ^ k := by
      by_contra hc
      exact absurd (mul_le_mul_left (not_lt.1 hc) M) (not_le.2 hlt)
    have hcast : ((∑ j ∈ P, 2 ^ (k - ν j) : ℕ) : ℝ≥0∞) < ((2 ^ k : ℕ) : ℝ≥0∞) := by
      push_cast
      exact hlt'
    exact_mod_cast hcast
  -- The weights: `2 ^ m * 2 ^ (k - νⱼ)` on `P`, and `1` on the summands of zero norm, where
  -- `2 ^ m ≥ #(s \ P)` provides exactly the room left over by `hPsum`.
  set m : ℕ := s.card with hmdef
  obtain ⟨w, hwpow, hwP, hwZ⟩ : ∃ w : ι → ℕ, (∀ j, ∃ e : ℕ, w j = 2 ^ e) ∧
      (∀ j ∈ P, w j = 2 ^ m * 2 ^ (k - ν j)) ∧ (∀ j ∈ s, j ∉ P → w j = 1) := by
    refine ⟨fun j => if b j = 0 then 1 else 2 ^ (m + k - ν j), fun j => ?_, fun j hj => ?_,
      fun j hj hjP => ?_⟩
    · by_cases h : b j = 0
      · exact ⟨0, by simp [h]⟩
      · exact ⟨m + k - ν j, by simp [h]⟩
    · have h : b j ≠ 0 := hmemP j hj
      have hνj := hνk j hj
      simp only [if_neg h]
      rw [← pow_add]
      congr 1
      omega
    · have h : b j = 0 := by
        by_contra hc
        exact hjP (Finset.mem_filter.2 ⟨hj, hc⟩)
      simp [h]
  have hdvdK : ∀ j ∈ s, w j ∣ 2 ^ (m + k) := by
    intro j hj
    by_cases h : j ∈ P
    · rw [hwP j h, ← pow_add]
      exact pow_dvd_pow 2 (by have := hνk j h; omega)
    · rw [hwZ j hj h]
      exact one_dvd _
  have hsumK : ∑ j ∈ s, w j ≤ 2 ^ (m + k) := by
    have hsplit : ∑ j ∈ P, w j + ∑ j ∈ s \ P, w j = ∑ j ∈ s, w j := by
      rw [add_comm]
      exact Finset.sum_sdiff hPs
    have h1 : ∑ j ∈ P, w j = 2 ^ m * ∑ j ∈ P, 2 ^ (k - ν j) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl hwP
    have h2' : ∑ j ∈ s \ P, w j = (s \ P).card := by
      rw [Finset.card_eq_sum_ones]
      exact Finset.sum_congr rfl fun j hj =>
        hwZ j (Finset.mem_sdiff.1 hj).1 (Finset.mem_sdiff.1 hj).2
    have h3 : (s \ P).card ≤ 2 ^ m :=
      le_trans (Finset.card_le_card Finset.sdiff_subset) Nat.lt_two_pow_self.le
    have h6 : (2 : ℕ) ^ m ≤ 2 ^ m * 2 ^ k := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos k)
    calc ∑ j ∈ s, w j = 2 ^ m * (∑ j ∈ P, 2 ^ (k - ν j)) + (s \ P).card := by
          rw [← hsplit, h1, h2']
      _ ≤ 2 ^ m * (2 ^ k - 1) + 2 ^ m := by gcongr; omega
      _ = 2 ^ m * 2 ^ k - 2 ^ m + 2 ^ m := by rw [Nat.mul_sub, mul_one]
      _ = 2 ^ m * 2 ^ k := Nat.sub_add_cancel h6
      _ = 2 ^ (m + k) := (pow_add 2 m k).symm
  have hbK : ∀ j ∈ s, (2 : ℝ≥0∞) ^ (m + k) * b j ≤ w j * (2 * M) := by
    intro j hj
    by_cases h : j ∈ P
    · have hνj := hνk j h
      have hcast : ((w j : ℕ) : ℝ≥0∞) = 2 ^ (m + (k - ν j)) := by
        rw [hwP j h]
        push_cast
        rw [pow_add]
      rw [hcast]
      calc (2 : ℝ≥0∞) ^ (m + k) * b j = 2 ^ (m + (k - ν j)) * (2 ^ ν j * b j) := by
            rw [← mul_assoc, ← pow_add]
            congr 2
            omega
        _ ≤ 2 ^ (m + (k - ν j)) * (2 * M) := mul_le_mul_right (hν₂ j h) _
    · have hb0 : b j = 0 := by
        by_contra hc
        exact h (Finset.mem_filter.2 ⟨hj, hc⟩)
      simp [hb0]
  exact enorm_sum_rpow_le_of_weights hp h2 hwpow (m + k) s a (2 * M) hdvdK hsumK hbK

/-! ## The `1`-norm `‖·‖*` and inequality (4) -/

variable (A p)

/-- The book's `‖a‖*` from the proof of Lemma 3.10.1:
`‖a‖* = inf {∑_{j<n} ‖aⱼ‖ ^ p : ∑_{j<n} aⱼ = a, n ≥ 1}`.

The empty decomposition `n = 0` is admitted as well; it is available only for `a = 0`, where it
contributes the value `0`, which `‖0‖ ^ p` equals anyway. -/
def starNorm (a : α) : ℝ≥0∞ :=
  ⨅ (n : ℕ) (a' : Fin n → α) (_ : ∑ i, a' i = a), ∑ j, ‖a' j‖ₑ[A] ^ p

variable {A p}

lemma starNorm_le_of_sum_eq {a : α} {n : ℕ} {a' : Fin n → α} (h : ∑ i, a' i = a) :
    A.starNorm p a ≤ ∑ j, ‖a' j‖ₑ[A] ^ p :=
  iInf_le_of_le n (iInf_le_of_le a' (iInf_le _ h))

@[simp] lemma starNorm_zero : A.starNorm p 0 = 0 := by
  refine le_antisymm ?_ zero_le
  have h : ∑ _i : Fin 0, (0 : α) = 0 := by simp
  simpa using starNorm_le_of_sum_eq (A := A) (p := p) h

/-- `‖·‖*` satisfies the `1`-triangle inequality: concatenating a decomposition of `x` with one of
`y` gives a decomposition of `x + y`.  This is the book's first paragraph, and needs no hypothesis
relating `p` to `A.C`. -/
lemma starNorm_add_le (x y : α) : A.starNorm p (x + y) ≤ A.starNorm p x + A.starNorm p y := by
  refine ENNReal.le_iInf₂_add_iInf₂ fun n a' m b' => ?_
  by_cases hx : ∑ i, a' i = x
  · by_cases hy : ∑ i, b' i = y
    · rw [iInf_pos hx, iInf_pos hy]
      refine le_trans (starNorm_le_of_sum_eq (a' := Fin.append a' b') ?_) (le_of_eq ?_)
      · rw [Fin.sum_univ_add]
        simp only [Fin.append_left, Fin.append_right, hx, hy]
      · rw [Fin.sum_univ_add]
        simp only [Fin.append_left, Fin.append_right]
    · rw [iInf_neg hy]
      simp
  · rw [iInf_neg hx]
    simp

/-- The left half of inequality (4): take the one-term decomposition. -/
lemma starNorm_le_rpow (a : α) : A.starNorm p a ≤ ‖a‖ₑ[A] ^ p := by
  have h : ∑ _i : Fin 1, a = a := by simp
  simpa using starNorm_le_of_sum_eq (A := A) (p := p) h

/-- The right half of inequality (4), i.e. the whole content of the induction above. -/
lemma rpow_le_two_mul_starNorm (hp : 0 < p) (h2 : (2 * A.C) ^ p = 2) (a : α) :
    ‖a‖ₑ[A] ^ p ≤ 2 * A.starNorm p a := by
  rw [starNorm]
  simp only [ENNReal.mul_iInf_of_ne (two_ne_zero) (ENNReal.ofNat_ne_top)]
  refine le_iInf₂ fun n a' => le_iInf fun h => ?_
  rw [← h]
  exact enorm_sum_rpow_le_two_mul_sum hp h2 Finset.univ a'

variable (A p)

/-- **Bergh-Löfström, Lemma 3.10.1.**  `‖·‖*` is an honest (extended) seminorm, i.e. a
`1`-normed structure, on `α`. -/
def aokiRolewicz : ESeminorm α where
  enorm := ⟨A.starNorm p⟩
  enorm_zero := starNorm_zero
  enorm_add_le_mul x y := by simpa using starNorm_add_le x y
  C_eq_one := rfl

@[simp] lemma enorm_aokiRolewicz (a : α) : ‖a‖ₑ[A.aokiRolewicz p] = A.starNorm p a := rfl

variable {A p}

/-- **Inequality (4)** of Lemma 3.10.1: `‖a‖* ≤ ‖a‖ ^ p ≤ 2 ‖a‖*`. -/
theorem aokiRolewicz_le_rpow_le_two_mul (hp : 0 < p) (h2 : (2 * A.C) ^ p = 2) (a : α) :
    ‖a‖ₑ[A.aokiRolewicz p] ≤ ‖a‖ₑ[A] ^ p ∧ ‖a‖ₑ[A] ^ p ≤ 2 * ‖a‖ₑ[A.aokiRolewicz p] :=
  ⟨starNorm_le_rpow a, rpow_le_two_mul_starNorm hp h2 a⟩

/-- Lemma 3.10.1 in the shape used in `MultilinearInterpolation.AokiRolewicz`: the Aoki-Rolewicz
seminorm is equivalent, as a quasinorm, to `A.pow p`. -/
theorem aokiRolewicz_equiv_pow (hp : 0 < p) (h2 : (2 * A.C) ^ p = 2) :
    (A.aokiRolewicz p).toEQuasinorm ≈ A.pow p :=
  ⟨⟨2, by norm_num, fun x => rpow_le_two_mul_starNorm hp h2 x⟩,
    ⟨1, by norm_num, fun x => by
      show A.starNorm p x ≤ 1 * ‖x‖ₑ[A] ^ p
      simpa using starNorm_le_rpow x⟩⟩

end EQuasinorm

/-!
## Notes for porting into `MultilinearInterpolation.AokiRolewicz`

Additionally `0 < p` is needed: it is used for monotonicity of `· ^ p`, and for
`(0 : ℝ≥0∞) ^ p = 0` in the empty-decomposition case.

**Definiteness.**  Bergh-Löfström's axiom (1) includes `‖a‖ = 0 ↔ a = 0`, which `EQuasinorm` does
not require.  The book uses it implicitly when choosing `νⱼ` from `2 ^ (-νⱼ) ≤ ‖aⱼ‖^p / M`, which
has no solution for `‖aⱼ‖ = 0`.  `enorm_sum_rpow_le_two_mul_sum` handles this without extra
hypotheses and without loss in the constant: see the last part of its proof.

Axiom (2), `‖-a‖ = ‖a‖`, is used by the book only to check that `‖·‖*` inherits it, so it plays no
role here; `α` need only be an `AddCommMonoid`.

**Sorry-freeness.**  Everything above is `sorry`-free except `aokiRolewicz_equiv_pow`, which
mentions `EQuasinorm.pow`; that definition currently has `sorry` in its `C`, `C_lt`, `enorm_zero`
and `enorm_add_le_mul` fields in `EQuasinorm/Basic.lean`.  Only `.enorm` is used by `· ≤ ·`, so
filling those fields in will make the equivalence sorry-free with no change here.
`aokiRolewicz_le_rpow_le_two_mul` is the same statement with the `pow` wrapper removed.
-/

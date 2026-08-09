import MultilinearInterpolation.Janson

open Set EQuasinorm MeasureTheory Function
open scoped ENNReal NNReal

noncomputable section

section Aux

lemma eLpNorm_one_count_eq_sum {κ : Type*} [Fintype κ] [MeasurableSpace κ]
    [MeasurableSingletonClass κ] (f : κ → ℝ≥0∞) :
    eLpNorm f 1 Measure.count = ∑ k, f k := by
  rw [eLpNorm_one_eq_lintegral_enorm, lintegral_count, tsum_fintype]
  simp

lemma eLpNorm_count_rpow_eq_sum {κ : Type*} [Fintype κ] [MeasurableSpace κ]
    [MeasurableSingletonClass κ] {q : ℝ≥0∞} (hq0 : q ≠ 0) (hq : q ≠ ∞) (f : κ → ℝ≥0∞) :
    eLpNorm f q Measure.count ^ q.toReal = ∑ k, f k ^ q.toReal := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hq, lintegral_count, tsum_fintype, one_div,
    ENNReal.rpow_inv_rpow (ENNReal.toReal_pos hq0 hq).ne']
  simp

end Aux

namespace MultisubadditiveMap

variable {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, AddCommMonoid (α i)] {β : Type*}
  [AddMonoid β] [Preorder β] [Abs β]
variable (T : MultisubadditiveMap α β) (B : EQuasinorm β)

/-- `T` is subadditive in each variable, measured in the quasinorm `B`. -/
def IsEnormSubadditive : Prop :=
  ∀ [DecidableEq ι] (f : ∀ i, α i) (i : ι) (x y : α i),
    ‖T (update f i (x + y))‖ₑ[B] ≤ ‖T (update f i x)‖ₑ[B] + ‖T (update f i y)‖ₑ[B]

variable {T B}

lemma IsEnormSubadditive.enorm_update_sum_le [DecidableEq ι] (hT : T.IsEnormSubadditive B)
    {κ : Type*} {s : Finset κ} (hs : s.Nonempty) (f : ∀ i, α i) (i : ι) (w : κ → α i) :
    ‖T (update f i (∑ n ∈ s, w n))‖ₑ[B] ≤ ∑ n ∈ s, ‖T (update f i (w n))‖ₑ[B] := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simp
  | cons a s ha hs ih =>
    rw [Finset.sum_cons, Finset.sum_cons]
    exact (hT f i (w a) _).trans (by gcongr)

private lemma aux [DecidableEq ι] (hT : T.IsEnormSubadditive B)
    {κ : ι → Type*} [∀ i, DecidableEq (κ i)] {n : ℕ} :
    ∀ (s : ∀ i, Finset (κ i)), (∀ i, (s i).Nonempty) → (∑ i, (s i).card = n) →
    ∀ (u : ∀ i, κ i → α i),
    ‖T (fun i ↦ ∑ k ∈ s i, u i k)‖ₑ[B] ≤
      ∑ g ∈ Fintype.piFinset s, ‖T (fun i ↦ u i (g i))‖ₑ[B] := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro s hs hcard u
  by_cases hs1 : ∀ i, (s i).card ≤ 1
  · have hcard1 : ∀ i, (s i).card = 1 := fun i ↦ le_antisymm (hs1 i) (Finset.card_pos.2 (hs i))
    choose r hr using fun i ↦ Finset.card_eq_one.1 (hcard1 i)
    have : s = fun i ↦ {r i} := funext hr
    subst this
    simp [Fintype.piFinset_singleton]
  push Not at hs1
  obtain ⟨i₀, hi₀⟩ := hs1
  obtain ⟨j₁, hj₁, j₂, hj₂, hne⟩ := Finset.one_lt_card.1 hi₀
  obtain ⟨b, hbdef⟩ : ∃ b : ∀ i, Finset (κ i), b = update s i₀ (s i₀ \ {j₂}) := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c : ∀ i, Finset (κ i), c = update s i₀ {j₂} := ⟨_, rfl⟩
  have hbi₀ : b i₀ = s i₀ \ {j₂} := by rw [hbdef]; exact update_self ..
  have hci₀ : c i₀ = {j₂} := by rw [hcdef]; exact update_self ..
  have hbi : ∀ i, i ≠ i₀ → b i = s i := fun i hi ↦ by rw [hbdef]; exact update_of_ne hi ..
  have hci : ∀ i, i ≠ i₀ → c i = s i := fun i hi ↦ by rw [hcdef]; exact update_of_ne hi ..
  have hbsub : ∀ i, b i ⊆ s i := by
    intro i; rcases eq_or_ne i i₀ with rfl | hi
    · simp [hbi₀]
    · simp [hbi i hi]
  have hcsub : ∀ i, c i ⊆ s i := by
    intro i; rcases eq_or_ne i i₀ with rfl | hi
    · simp [hci₀, hj₂]
    · simp [hci i hi]
  have hbne : ∀ i, (b i).Nonempty := by
    intro i; rcases eq_or_ne i i₀ with rfl | hi
    · exact ⟨j₁, by simp [hbi₀, hj₁, hne]⟩
    · rw [hbi i hi]; exact hs i
  have hcne : ∀ i, (c i).Nonempty := by
    intro i; rcases eq_or_ne i i₀ with rfl | hi
    · simp [hci₀]
    · rw [hci i hi]; exact hs i
  have hbcard : ∑ i, (b i).card < n := by
    rw [← hcard]
    refine Finset.sum_lt_sum (fun i _ ↦ Finset.card_le_card (hbsub i)) ⟨i₀, Finset.mem_univ _, ?_⟩
    rw [hbi₀, Finset.sdiff_singleton_eq_erase]
    exact Finset.card_erase_lt_of_mem hj₂
  have hccard : ∑ i, (c i).card < n := by
    rw [← hcard]
    refine Finset.sum_lt_sum (fun i _ ↦ Finset.card_le_card (hcsub i)) ⟨i₀, Finset.mem_univ _, ?_⟩
    rw [hci₀]; simpa using hi₀
  have hsum₀ : ∑ k ∈ s i₀, u i₀ k = (∑ k ∈ b i₀, u i₀ k) + (∑ k ∈ c i₀, u i₀ k) := by
    rw [hbi₀, hci₀, Finset.sdiff_singleton_eq_erase, Finset.sum_singleton,
      Finset.sum_erase_add _ _ hj₂]
  have hBeq : update (fun i ↦ ∑ k ∈ s i, u i k) i₀ (∑ k ∈ b i₀, u i₀ k) =
      fun i ↦ ∑ k ∈ b i, u i k := by
    funext i; rcases eq_or_ne i i₀ with rfl | hi
    · rw [update_self]
    · rw [update_of_ne hi, hbi i hi]
  have hCeq : update (fun i ↦ ∑ k ∈ s i, u i k) i₀ (∑ k ∈ c i₀, u i₀ k) =
      fun i ↦ ∑ k ∈ c i, u i k := by
    funext i; rcases eq_or_ne i i₀ with rfl | hi
    · rw [update_self]
    · rw [update_of_ne hi, hci i hi]
  have hunion : ∑ g ∈ Fintype.piFinset b, ‖T (fun i ↦ u i (g i))‖ₑ[B] +
      ∑ g ∈ Fintype.piFinset c, ‖T (fun i ↦ u i (g i))‖ₑ[B] =
      ∑ g ∈ Fintype.piFinset s, ‖T (fun i ↦ u i (g i))‖ₑ[B] := by
    rw [hbdef, hcdef,
      Fintype.piFinset_update_eq_filter_piFinset_mem s i₀ Finset.sdiff_subset,
      Fintype.piFinset_update_singleton_eq_filter_piFinset_eq s i₀ hj₂]
    have hfil : ∀ f ∈ Fintype.piFinset s, (f i₀ ∈ s i₀ \ {j₂}) ↔ ¬ (f i₀ = j₂) := fun f hf ↦ by
      simp [Finset.mem_sdiff, Fintype.mem_piFinset.1 hf i₀]
    rw [Finset.filter_congr hfil, add_comm, Finset.sum_filter_add_sum_filter_not]
  calc ‖T (fun i ↦ ∑ k ∈ s i, u i k)‖ₑ[B]
      = ‖T (update (fun i ↦ ∑ k ∈ s i, u i k) i₀
          ((∑ k ∈ b i₀, u i₀ k) + (∑ k ∈ c i₀, u i₀ k)))‖ₑ[B] := by
        rw [← hsum₀, update_eq_self]
    _ ≤ ‖T (update (fun i ↦ ∑ k ∈ s i, u i k) i₀ (∑ k ∈ b i₀, u i₀ k))‖ₑ[B] +
        ‖T (update (fun i ↦ ∑ k ∈ s i, u i k) i₀ (∑ k ∈ c i₀, u i₀ k))‖ₑ[B] := hT _ _ _ _
    _ = ‖T (fun i ↦ ∑ k ∈ b i, u i k)‖ₑ[B] + ‖T (fun i ↦ ∑ k ∈ c i, u i k)‖ₑ[B] := by
        rw [hBeq, hCeq]
    _ ≤ (∑ g ∈ Fintype.piFinset b, ‖T (fun i ↦ u i (g i))‖ₑ[B]) +
        ∑ g ∈ Fintype.piFinset c, ‖T (fun i ↦ u i (g i))‖ₑ[B] := by
        gcongr
        · exact IH _ hbcard b hbne rfl u
        · exact IH _ hccard c hcne rfl u
    _ = _ := hunion

lemma IsEnormSubadditive.enorm_le_sum [DecidableEq ι] (hT : T.IsEnormSubadditive B)
    {κ : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] [∀ i, Nonempty (κ i)]
    (u : ∀ i, κ i → α i) :
    ‖T (fun i ↦ ∑ k, u i k)‖ₑ[B] ≤ ∑ g : (∀ i, κ i), ‖T (fun i ↦ u i (g i))‖ₑ[B] := by
  simpa using aux hT (fun _ ↦ Finset.univ) (fun _ ↦ Finset.univ_nonempty) rfl u

end MultisubadditiveMap

section AokiRolewicz

variable {α : Type*} [AddCommMonoid α]

/-- Aoki–Rolewicz: a quasinorm becomes subadditive once raised to a small enough power.
Here {name}`EQuasinorm.pow` is the quasinorm $`x ↦ ‖x‖^p`, so the conclusion is the
$`p`-triangle inequality $`‖x + y‖^p ≤ ‖x‖^p + ‖y‖^p`. -/
lemma EQuasinorm.exists_pow_subadditive (A : EQuasinorm α) :
    ∃ p ∈ Ioc (0 : ℝ) 1, ∀ x y : α, ‖x + y‖ₑ[A.pow p] ≤ ‖x‖ₑ[A.pow p] + ‖y‖ₑ[A.pow p] :=
  sorry

/-- {name}`EQuasinorm.exists_pow_subadditive` with the exponent packaged as the
$`ℓ^q`-exponent used in the `J`-method infimum below. -/
lemma EQuasinorm.exists_toReal_pow_subadditive (A : EQuasinorm α) :
    ∃ q : ℝ≥0∞, q ≠ 0 ∧ q ≠ ∞ ∧ q ≤ 1 ∧ ∀ x y : α,
      ‖x + y‖ₑ[A.pow q.toReal] ≤ ‖x‖ₑ[A.pow q.toReal] + ‖y‖ₑ[A.pow q.toReal] := by
  obtain ⟨p, ⟨hp0, hp1⟩, hp⟩ := A.exists_pow_subadditive
  refine ⟨ENNReal.ofReal p, by simp [hp0], by simp, ENNReal.ofReal_le_one.2 hp1, ?_⟩
  rw [ENNReal.toReal_ofReal hp0.le]
  exact hp

end AokiRolewicz

section JSummand

variable {α : Type*} [AddCommMonoid α]

/-- The `k`-th term of the sequence whose `ℓ^q`-norm is minimised in {name}`jInfNorm`.
Stated for a bare `EQuasinorm.Couple`: no subadditivity constant is involved. -/
def jSummand (A : EQuasinorm.Couple α) (θ : ℝ) (N : ℕ) (u : Fin (2 * N) → α)
    (k : Fin (2 * N)) : ℝ≥0∞ :=
  2 ^ (-θ * ((k : ℝ) - N)) * A.jNorm (2 ^ ((k : ℝ) - N)) (u k)

/-- Verbatim copy of {name}`jInfNorm` for a quasi-normed couple. -/
def jInfNormQ (A : EQuasinorm.Couple α) (θ : ℝ) (q : ℝ≥0∞) (x : α) : ℝ≥0∞ :=
  ⨅ (N : ℕ) (u : Fin (2 * N) → α) (_ : ∑ n, u n = x),
    eLpNorm (jSummand A θ N u) q Measure.count

/-- The `jInfNorm` of `Janson.lean` is the special case of {name}`jInfNormQ` in which both
subadditivity constants are `1`. -/
lemma jInfNorm_eq (A : Couple α) (θ : ℝ) (q : ℝ≥0∞) (x : α) :
    jInfNorm A θ q x = jInfNormQ A θ q x := rfl

@[simp]
lemma jSummand_zero (A : EQuasinorm.Couple α) (θ : ℝ) (N : ℕ) :
    jSummand A θ N 0 = 0 := by
  funext k
  simp [jSummand, EQuasinorm.jNorm]

/-- Nonempty type of finite decompositions of `x` with at least two terms; it indexes the
same family as {name}`jInfNorm`. -/
abbrev Decomp (α : Type*) [AddCommMonoid α] (x : α) : Type _ :=
  Σ N : ℕ, {u : Fin (2 * (N + 1)) → α // ∑ n, u n = x}

instance (x : α) : Nonempty (Decomp α x) :=
  ⟨0, fun k ↦ if k = 0 then x else 0, by simp [Fin.sum_univ_two]⟩

/-- {name}`jInfNormQ` as an infimum over the single index type {name}`Decomp`. -/
lemma jInfNormQ_eq_iInf_decomp (A : EQuasinorm.Couple α) (θ : ℝ) (q : ℝ≥0∞) (x : α) :
    jInfNormQ A θ q x =
      ⨅ d : Decomp α x, eLpNorm (jSummand A θ (d.1 + 1) d.2.1) q Measure.count := by
  rw [jInfNormQ, iInf_sigma]
  simp_rw [iInf_subtype]
  refine le_antisymm (le_iInf₂ fun N u ↦ le_iInf fun h ↦ iInf₂_le_of_le (N + 1) u
    (iInf_le _ h)) ?_
  refine le_iInf fun N ↦ le_iInf₂ fun u h ↦ ?_
  match N, u, h with
  | 0, u, h =>
    refine iInf₂_le_of_le 0 0 (iInf_le_of_le (by simpa using h) ?_)
    simp
  | (M + 1), u, h => exact iInf₂_le_of_le M u (iInf_le _ h)

end JSummand

section ENNRealAux

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ι → Type*} [∀ i, Nonempty (D i)]

/-- In `ℝ≥0∞` the infimum of a finite product dominates the product of the infima, provided
each infimum is finite. Finiteness cannot be dropped: `0 * ∞ = 0`, so with `F 1 d = 1/d` and
`F 2 d = ∞` the left-hand side is `∞` while the right-hand side is `0`. -/
lemma iInf_prod_le_prod_iInf (F : ∀ i, D i → ℝ≥0∞) (hfin : ∀ i, (⨅ d, F i d) ≠ ∞)
    (t : Finset ι) :
    ⨅ (g : ∀ i, D i), ∏ i ∈ t, F i (g i) ≤ ∏ i ∈ t, ⨅ d, F i d := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
    have hfinite : Nonempty {x : D a // F a x ≠ ∞} := by
      by_contra h
      simp only [not_nonempty_iff, isEmpty_subtype, not_not] at h
      exact hfin a (by simp [h])
    have hQ : (⨅ g : ∀ i, D i, ∏ i ∈ t, F i (g i)) ≠ ∞ :=
      ne_top_of_le_ne_top (ENNReal.prod_ne_top fun i _ ↦ hfin i) ih
    have hsub : (⨅ x : {x : D a // F a x ≠ ∞}, F a x) = ⨅ x, F a x := by
      refine le_antisymm (le_iInf fun x ↦ ?_) (le_iInf fun x ↦ iInf_le _ _)
      by_cases hx : F a x = ∞
      · rw [hx]; exact le_top
      · exact iInf_le (fun y : {x : D a // F a x ≠ ∞} ↦ F a y.1) ⟨x, hx⟩
    rw [Finset.prod_insert ha]
    calc ⨅ (g : ∀ i, D i), ∏ i ∈ insert a t, F i (g i)
        ≤ ⨅ (x : {x : D a // F a x ≠ ∞}) (g : ∀ i, D i), F a x * ∏ i ∈ t, F i (g i) := by
          refine le_iInf₂ fun x g ↦ (iInf_le _ (update g a x.1)).trans_eq ?_
          rw [Finset.prod_insert ha, update_self]
          congr 1
          exact Finset.prod_congr rfl fun i hi ↦ by
            rw [update_of_ne (by rintro rfl; exact ha hi)]
      _ = ⨅ (x : {x : D a // F a x ≠ ∞}), F a x * ⨅ (g : ∀ i, D i), ∏ i ∈ t, F i (g i) := by
          exact iInf_congr fun x ↦ (ENNReal.mul_iInf (by simp [x.2])).symm
      _ = (⨅ x : {x : D a // F a x ≠ ∞}, F a x) * ⨅ (g : ∀ i, D i), ∏ i ∈ t, F i (g i) := by
          exact (ENNReal.iInf_mul (by simp [hQ])).symm
      _ ≤ (⨅ d, F a d) * ∏ i ∈ t, ⨅ d, F i d := by rw [hsub]; gcongr

end ENNRealAux

/-! # The finite-decomposition estimate

Everything below is stated for bare {name}`EQuasinorm.Couple`s on the source side: no
subadditivity constant of the $`A_i` is ever used, so passing from seminorms to quasinorms
costs nothing there.

The target side is where the constant matters. The expansion {name}`MultisubadditiveMap.IsEnormSubadditive.enorm_le_sum`
splits $`T a` into $`∏_i 2N_i` terms, and a merely $`K`-subadditive norm gives
$`‖∑_{j≤n} x_j‖ ≤ K^{⌈\log_2 n⌉} ∑_j ‖x_j‖`, a factor $`n^{\log_2 K}` that blows up as the
decompositions get finer. What survives the iteration is the $`q`-triangle inequality
$`‖x+y‖^q ≤ ‖x‖^q + ‖y‖^q`, i.e. subadditivity of {name}`EQuasinorm.pow`, and by
{name}`EQuasinorm.exists_pow_subadditive` every quasinorm satisfies it for some $`q ∈ (0,1]`.
So the argument does go through for quasinorms, at the price of running it in $`ℓ^q` rather
than $`ℓ^1`; this is exactly Janson's Remark 9, and $`q = 1` recovers the seminorm case.
-/

section Core

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, AddCommGroup (α i)]
  {β : Type*} [AddMonoid β] [Preorder β] [Abs β]
  {T : MultisubadditiveMap α β} {A : (i : ι) → EQuasinorm.Couple (α i)} {B' : EQuasinorm β}
  {θ : ι → ℝ} {C q : ℝ≥0∞}

/-- The pointwise inequality of the note, applied to one cell of the decomposition grid. -/
lemma enorm_le_mul_prod_jSummand
    (hθ : ∀ i, θ i ∈ Icc (0 : ℝ) 1)
    (hC : ∀ a : (i : ι) → α i, ‖T a‖ₑ[B'] ≤
      C * ∏ i, ‖a i‖ₑ[(A i).fst] ^ (1 - θ i) * ‖a i‖ₑ[(A i).snd] ^ (θ i))
    {N : ι → ℕ} (u : ∀ i, Fin (2 * N i) → α i) (g : ∀ i, Fin (2 * N i)) :
    ‖T (fun i ↦ u i (g i))‖ₑ[B'] ≤ C * ∏ i, jSummand (A i) (θ i) (N i) (u i) (g i) := by
  refine (hC _).trans ?_
  gcongr with i
  rw [jSummand, show (-θ i * ((g i : ℝ) - N i)) = ((g i : ℝ) - N i) * (-θ i) by ring,
    ENNReal.rpow_mul]
  exact EQuasinorm.enorm_rpow_mul_enorm_rpow_le_rpow_neg_mul_jNorm (hθ i).1 (hθ i).2
    (by simp [ENNReal.rpow_eq_zero_iff]) (by simp [ENNReal.rpow_eq_top_iff])

/-- The finite-decomposition estimate: any finite decomposition of each `a i` bounds `‖T a‖`.
`hT` says that `B'` is `q`-subadditive along `T`, which is where the `p`-normed hypothesis of
the note enters; `q = 1` is the subadditive case. -/
lemma enorm_le_mul_prod_eLpNorm_jSummand (hq0 : q ≠ 0) (hq : q ≠ ∞)
    (hT : T.IsEnormSubadditive (B'.pow q.toReal))
    (hθ : ∀ i, θ i ∈ Icc (0 : ℝ) 1)
    (hC : ∀ a : (i : ι) → α i, ‖T a‖ₑ[B'] ≤
      C * ∏ i, ‖a i‖ₑ[(A i).fst] ^ (1 - θ i) * ‖a i‖ₑ[(A i).snd] ^ (θ i))
    {N : ι → ℕ} (hN : ∀ i, 0 < N i) (u : ∀ i, Fin (2 * N i) → α i) :
    ‖T (fun i ↦ ∑ k, u i k)‖ₑ[B'] ≤
      C * ∏ i, eLpNorm (jSummand (A i) (θ i) (N i) (u i)) q Measure.count := by
  have hp : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  have : ∀ i, Nonempty (Fin (2 * N i)) := fun i ↦ ⟨⟨0, by have := hN i; omega⟩⟩
  rw [← ENNReal.rpow_le_rpow_iff hp, ENNReal.mul_rpow_of_nonneg _ _ hp.le,
    ← ENNReal.prod_rpow_of_nonneg hp.le]
  calc ‖T (fun i ↦ ∑ k, u i k)‖ₑ[B'] ^ q.toReal
      ≤ ∑ g : (∀ i, Fin (2 * N i)), ‖T (fun i ↦ u i (g i))‖ₑ[B'] ^ q.toReal :=
        hT.enorm_le_sum u
    _ ≤ ∑ _g : (∀ i, Fin (2 * N i)),
        C ^ q.toReal * ∏ i, jSummand (A i) (θ i) (N i) (u i) (_g i) ^ q.toReal := by
        refine Finset.sum_le_sum fun g _ ↦ ?_
        rw [ENNReal.prod_rpow_of_nonneg hp.le, ← ENNReal.mul_rpow_of_nonneg _ _ hp.le]
        exact ENNReal.rpow_le_rpow (enorm_le_mul_prod_jSummand hθ hC u g) hp.le
    _ = C ^ q.toReal *
        ∑ g : (∀ i, Fin (2 * N i)), ∏ i, jSummand (A i) (θ i) (N i) (u i) (g i) ^ q.toReal := by
        rw [Finset.mul_sum]
    _ = C ^ q.toReal * ∏ i, ∑ k, jSummand (A i) (θ i) (N i) (u i) k ^ q.toReal := by
        rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    _ = _ := by simp_rw [eLpNorm_count_rpow_eq_sum hq0 hq]

lemma enorm_le_mul_prod_jInfNorm (hq0 : q ≠ 0) (hq : q ≠ ∞)
    (hT : T.IsEnormSubadditive (B'.pow q.toReal))
    (hθ : ∀ i, θ i ∈ Icc (0 : ℝ) 1) (hCfin : C ≠ ∞)
    (hC : ∀ a : (i : ι) → α i, ‖T a‖ₑ[B'] ≤
      C * ∏ i, ‖a i‖ₑ[(A i).fst] ^ (1 - θ i) * ‖a i‖ₑ[(A i).snd] ^ (θ i))
    (a : ∀ i, α i) (hfin : ∀ i, jInfNormQ (A i) (θ i) q (a i) ≠ ∞) :
    ‖T a‖ₑ[B'] ≤ C * ∏ i, jInfNormQ (A i) (θ i) q (a i) := by
  let F : ∀ i, Decomp (α i) (a i) → ℝ≥0∞ := fun i d ↦
    eLpNorm (jSummand (A i) (θ i) (d.1 + 1) d.2.1) q Measure.count
  have hJ : ∀ i, (⨅ d, F i d) = jInfNormQ (A i) (θ i) q (a i) :=
    fun i ↦ (jInfNormQ_eq_iInf_decomp ..).symm
  have hstep : ∀ g : (∀ i, Decomp (α i) (a i)), ‖T a‖ₑ[B'] ≤ C * ∏ i, F i (g i) := by
    intro g
    have h := enorm_le_mul_prod_eLpNorm_jSummand hq0 hq hT hθ hC (N := fun i ↦ (g i).1 + 1)
      (fun _ ↦ Nat.succ_pos _) (fun i ↦ (g i).2.1)
    rwa [show (fun i ↦ ∑ k, (g i).2.1 k) = a from funext fun i ↦ (g i).2.2] at h
  calc ‖T a‖ₑ[B'] ≤ ⨅ g : (∀ i, Decomp (α i) (a i)), C * ∏ i, F i (g i) := le_iInf hstep
    _ = C * ⨅ g : (∀ i, Decomp (α i) (a i)), ∏ i, F i (g i) :=
        (ENNReal.mul_iInf (by simp [hCfin])).symm
    _ ≤ C * ∏ i, ⨅ d, F i d := by
        gcongr
        exact iInf_prod_le_prod_iInf F (fun i ↦ (hJ i).symm ▸ hfin i) Finset.univ
    _ = C * ∏ i, jInfNormQ (A i) (θ i) q (a i) := by simp_rw [hJ]

end Core

section Omega

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, AddCommGroup (α i)]
  {β : Type*} [AddMonoid β] [Preorder β] [Abs β]
  {T : MultisubadditiveMap α β} {θ : ι → ℝ}

/-- Janson's Lemma 2, direction (ii) → (i), for arbitrary quasi-normed couples on the source
side and an arbitrary exponent `q` on the target side.

Nothing here uses that the `A i` are seminorms. On the target side the only hypothesis is `hT`,
which asks the quasinorm `B'` to be `q`-subadditive along `T`; by
{name}`EQuasinorm.exists_pow_subadditive` such a `q` always exists, so this is no restriction —
but the exponent is then forced on the source side too, through `hL1` (Lemma 1 with `q_i = q`).
This is Janson's Remark 9.

The finiteness guard in {name}`MultisubadditiveMap.IsBoundedFor` is what makes the conclusion
true as stated: without it the case `‖a j‖ = 0` together with `‖a i‖ = ∞` would force
`‖T a‖ = 0`, since `0 * ∞ = 0` in `ℝ≥0∞`. -/
theorem exists_enorm_kMethod_le {A : (i : ι) → EQuasinorm.Couple (α i)} {B' : EQuasinorm β}
    {q : ℝ≥0∞} (hq0 : q ≠ 0) (hq : q ≠ ∞)
    (hθ : ∀ i, θ i ∈ Icc (0 : ℝ) 1)
    (hT : T.IsEnormSubadditive (B'.pow q.toReal))
    (hL1 : ∀ i, ∃ c : ℝ≥0∞, c < ∞ ∧ ∀ x,
      jInfNormQ (A i) (θ i) q x ≤ c * ‖x‖ₑ[(A i).kMethod (θ i) q])
    (h : ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (a : (i : ι) → α i), ‖T a‖ₑ[B'] ≤
        C * ∏ i, ‖a i‖ₑ[(A i).fst] ^ (1 - θ i : ℝ) * ‖a i‖ₑ[(A i).snd] ^ (θ i : ℝ)) :
    ∃ C' : ℝ≥0∞, T.IsBoundedFor (fun i ↦ (A i).kMethod (θ i) q) B' C' := by
  obtain ⟨C, hCfin, hC⟩ := h
  choose C₁ hC₁ hC₁le using hL1
  refine ⟨C * ∏ i, C₁ i, ENNReal.mul_lt_top hCfin (ENNReal.prod_lt_top fun i _ ↦ hC₁ i),
    fun a ha ↦ ?_⟩
  have hfin : ∀ i, jInfNormQ (A i) (θ i) q (a i) ≠ ∞ := fun i ↦
    ((hC₁le i (a i)).trans_lt (ENNReal.mul_lt_top (hC₁ i) (ha i))).ne
  calc ‖T a‖ₑ[B']
      ≤ C * ∏ i, jInfNormQ (A i) (θ i) q (a i) :=
        enorm_le_mul_prod_jInfNorm hq0 hq hT hθ hCfin.ne hC a hfin
    _ ≤ C * ∏ i, C₁ i * ‖a i‖ₑ[(A i).kMethod (θ i) q] := by gcongr; exact hC₁le _ _
    _ = (C * ∏ i, C₁ i) * ∏ i, ‖a i‖ₑ[(A i).kMethod (θ i) q] := by
        rw [Finset.prod_mul_distrib, mul_assoc]

variable {A : (i : ι) → Couple (α i)} {B : Couple β} {cα₀ : ℝ} {cα : ι → ℝ}

/-- Membership in {name}`Ω`, with the exponents `q_i = q_0 = q` supplied by the `q`-subadditivity
of the target. -/
theorem mem_Ω_of_forall_enorm_le {q : ℝ≥0∞} (hq0 : q ≠ 0) (hq : q ≠ ∞)
    (hθ : ∀ i, θ i ∈ Ioo (0 : ℝ) 1)
    (hθ₀ : 0 ≤ cα₀ + ∑ i, cα i * θ i)
    (hT : T.IsEnormSubadditive
      ((B.kMethod (cα₀ + ∑ i, cα i * θ i) ∞).pow q.toReal))
    (h : ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (a : (i : ι) → α i),
      ‖T a‖ₑ[B.kMethod (cα₀ + ∑ i, cα i * θ i) ∞] ≤
        C * ∏ i, ‖a i‖ₑ[(A i).fst] ^ (1 - θ i : ℝ) * ‖a i‖ₑ[(A i).snd] ^ (θ i : ℝ)) :
    θ ∈ Ω T A B cα₀ cα := by
  obtain ⟨C', hC'⟩ := exists_enorm_kMethod_le hq0 hq
    (fun i ↦ Ioo_subset_Icc_self (hθ i)) hT
    (fun i ↦ jInfNorm_le_kNorm (A i) (θ i) (hθ i) q) h
  exact ⟨∞, fun _ ↦ q, hθ₀, C', hC'⟩

end Omega

import MultilinearInterpolation.Janson
import MultilinearInterpolation.AokiRolewicz

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
  [AddCommMonoid β] {M : Type*} [AddCommMonoid M] [Preorder M] [VNorm β M]
  [VectorNormed β M]
variable {T : MultisubadditiveMap α β} {B : EQuasinorm β}

/-! The expansion of {name}`MultisubadditiveMap.subadditive` over a finite grid. Stated for an
{name}`ESeminorm` target, where {name}`MultisubadditiveMap.enorm_update_add_le` turns the
modulus-level inequality of the structure into a genuine triangle inequality, so no constant is
ever incurred. -/

lemma enorm_update_sum_le [DecidableEq ι] (S : ESeminorm β) [S.toEQuasinorm.IsSolid]
    {κ : Type*} {s : Finset κ} (hs : s.Nonempty) (f : ∀ i, α i) (i : ι) (w : κ → α i) :
    ‖T (update f i (∑ n ∈ s, w n))‖ₑ[S] ≤ ∑ n ∈ s, ‖T (update f i (w n))‖ₑ[S] := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simp
  | cons a s ha hs ih =>
    rw [Finset.sum_cons, Finset.sum_cons]
    exact (T.enorm_update_add_le S f i (w a) _).trans (by gcongr)

private lemma aux [DecidableEq ι] (S : ESeminorm β) [S.toEQuasinorm.IsSolid]
    {κ : ι → Type*} [∀ i, DecidableEq (κ i)] {n : ℕ} :
    ∀ (s : ∀ i, Finset (κ i)), (∀ i, (s i).Nonempty) → (∑ i, (s i).card = n) →
    ∀ (u : ∀ i, κ i → α i),
    ‖T (fun i ↦ ∑ k ∈ s i, u i k)‖ₑ[S] ≤
      ∑ g ∈ Fintype.piFinset s, ‖T (fun i ↦ u i (g i))‖ₑ[S] := by
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
  have hunion : ∑ g ∈ Fintype.piFinset b, ‖T (fun i ↦ u i (g i))‖ₑ[S] +
      ∑ g ∈ Fintype.piFinset c, ‖T (fun i ↦ u i (g i))‖ₑ[S] =
      ∑ g ∈ Fintype.piFinset s, ‖T (fun i ↦ u i (g i))‖ₑ[S] := by
    rw [hbdef, hcdef,
      Fintype.piFinset_update_eq_filter_piFinset_mem s i₀ Finset.sdiff_subset,
      Fintype.piFinset_update_singleton_eq_filter_piFinset_eq s i₀ hj₂]
    have hfil : ∀ f ∈ Fintype.piFinset s, (f i₀ ∈ s i₀ \ {j₂}) ↔ ¬ (f i₀ = j₂) := fun f hf ↦ by
      simp [Finset.mem_sdiff, Fintype.mem_piFinset.1 hf i₀]
    rw [Finset.filter_congr hfil, add_comm, Finset.sum_filter_add_sum_filter_not]
  calc ‖T (fun i ↦ ∑ k ∈ s i, u i k)‖ₑ[S]
      = ‖T (update (fun i ↦ ∑ k ∈ s i, u i k) i₀
          ((∑ k ∈ b i₀, u i₀ k) + (∑ k ∈ c i₀, u i₀ k)))‖ₑ[S] := by
        rw [← hsum₀, update_eq_self]
    _ ≤ ‖T (update (fun i ↦ ∑ k ∈ s i, u i k) i₀ (∑ k ∈ b i₀, u i₀ k))‖ₑ[S] +
        ‖T (update (fun i ↦ ∑ k ∈ s i, u i k) i₀ (∑ k ∈ c i₀, u i₀ k))‖ₑ[S] :=
          T.enorm_update_add_le S _ _ _ _
    _ = ‖T (fun i ↦ ∑ k ∈ b i, u i k)‖ₑ[S] + ‖T (fun i ↦ ∑ k ∈ c i, u i k)‖ₑ[S] := by
        rw [hBeq, hCeq]
    _ ≤ (∑ g ∈ Fintype.piFinset b, ‖T (fun i ↦ u i (g i))‖ₑ[S]) +
        ∑ g ∈ Fintype.piFinset c, ‖T (fun i ↦ u i (g i))‖ₑ[S] := by
        gcongr
        · exact IH _ hbcard b hbne rfl u
        · exact IH _ hccard c hcne rfl u
    _ = _ := hunion

lemma enorm_le_sum [DecidableEq ι] (S : ESeminorm β) [S.toEQuasinorm.IsSolid]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] [∀ i, Nonempty (κ i)]
    (u : ∀ i, κ i → α i) :
    ‖T (fun i ↦ ∑ k, u i k)‖ₑ[S] ≤ ∑ g : (∀ i, κ i), ‖T (fun i ↦ u i (g i))‖ₑ[S] := by
  simpa using aux S (fun _ ↦ Finset.univ) (fun _ ↦ Finset.univ_nonempty) rfl u

/-- {name}`MultisubadditiveMap.enorm_le_sum` for a quasinorm `B` that is merely *equivalent* to a
solid {name}`ESeminorm`. The expansion is performed inside `S`, so the constant `c₁ * c₂` is paid
once on the way in and once on the way out: it comes from the equivalence alone and does **not**
grow with the number of summands. Iterating the quasinorm triangle inequality instead would give
`‖∑_{j ≤ n} x_j‖ ≤ K ^ ⌈log₂ n⌉ ∑_j ‖x_j‖`, a factor `n ^ (log₂ K)` that blows up as the
decompositions get finer. -/
lemma enorm_le_mul_sum [DecidableEq ι] (S : ESeminorm β) [S.toEQuasinorm.IsSolid] {c₁ c₂ : ℝ≥0∞}
    (h₁ : ∀ x : β, ‖x‖ₑ[B] ≤ c₁ * ‖x‖ₑ[S]) (h₂ : ∀ x : β, ‖x‖ₑ[S] ≤ c₂ * ‖x‖ₑ[B])
    {κ : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] [∀ i, Nonempty (κ i)]
    (u : ∀ i, κ i → α i) :
    ‖T (fun i ↦ ∑ k, u i k)‖ₑ[B] ≤
      c₁ * c₂ * ∑ g : (∀ i, κ i), ‖T (fun i ↦ u i (g i))‖ₑ[B] := by
  calc ‖T (fun i ↦ ∑ k, u i k)‖ₑ[B] ≤ c₁ * ‖T (fun i ↦ ∑ k, u i k)‖ₑ[S] := h₁ _
    _ ≤ c₁ * ∑ g : (∀ i, κ i), ‖T (fun i ↦ u i (g i))‖ₑ[S] := by
        gcongr; exact enorm_le_sum S u
    _ ≤ c₁ * ∑ g : (∀ i, κ i), c₂ * ‖T (fun i ↦ u i (g i))‖ₑ[B] := by
        gcongr with g; exact h₂ _
    _ = c₁ * c₂ * ∑ g : (∀ i, κ i), ‖T (fun i ↦ u i (g i))‖ₑ[B] := by
        rw [← Finset.mul_sum, ← mul_assoc]

end MultisubadditiveMap

section AokiRolewicz

variable {α : Type*}

/-- {name}`EQuasinorm.aokiRolewicz` is equivalent to the `p`-th power of the quasinorm it is
built from: its enorm is `⨅ ∑ ‖a'ⱼ‖ₑ[A] ^ p`, and the trivial decomposition already gives
`‖a‖ₑ[S] ≤ ‖a‖ₑ[A] ^ p`.

This is {name}`aokiRolewicz_pow_equiv_self` with the exponent corrected: as stated there,
`S.pow p ≈ A` would give `S ≈ A.pow p⁻¹`, whereas the construction yields `S ≈ A.pow p`. -/
lemma EQuasinorm.aokiRolewicz_equiv_pow [AddCommMonoid α] (A : EQuasinorm α) (p : ℝ)
    (hp : (2 * A.C) ^ p = 2) :
    (A.aokiRolewicz p hp).toEQuasinorm ≈ A.pow p :=
  sorry

/-- Raising a couple to a power rescales the `ℓ^q` exponent of the `K`-method but leaves `θ`
alone: `K(t, x; A₀^p, A₁^p) ≈ K(t ^ p⁻¹, x; A₀, A₁) ^ p`, and substituting `t = s ^ p` in the
defining integral turns `q` into `p * q`.

Not used below. It is the missing step for deducing the quasi-normed case of Janson's Lemma 2
from the semi-normed one via {name}`MultisubadditiveMap.isBoundedFor_iff_isBoundedFor_pow`,
which raises both sides of the boundedness inequality — and hence both the source and the
target norms — to the power `p`. -/
lemma EQuasinorm.pow_kMethod_equiv [AddMonoid α] (A₀ A₁ : EQuasinorm α) (θ : ℝ) {p : ℝ}
    (hp : 0 < p) (q : ℝ≥0∞) :
    (A₀.pow p).kMethod (A₁.pow p) θ q ≈ (A₀.kMethod A₁ θ (ENNReal.ofReal p * q)).pow p :=
  sorry

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
  ⟨0, fun k ↦ if k = 0 then x else 0, by simp⟩

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

The target side is where the constant matters. The expansion
{name}`MultisubadditiveMap.enorm_le_sum` splits $`T a` into $`∏_i 2N_i` terms, and it is stated
for an {name}`ESeminorm` target precisely so that no constant is incurred per step: there the
modulus-level {name}`MultisubadditiveMap.subadditive` field of the structure becomes a genuine
triangle inequality, by {name}`MultisubadditiveMap.enorm_update_add_le`.

A quasi-normed target reaches that expansion through
{name}`MultisubadditiveMap.enorm_le_mul_sum`, which asks only for a solid {name}`ESeminorm`
$`S` equivalent to $`B^q`. By {name}`EQuasinorm.aokiRolewicz_equiv_pow` such an $`S` always
exists for some $`q ∈ (0,1]`, so this is no restriction — but the exponent is then forced on the
source side too, and the argument runs in $`ℓ^q` rather than $`ℓ^1`. This is exactly Janson's
Remark 9, and $`q = 1` recovers the seminorm case.
-/

section Core

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, AddCommGroup (α i)]
  {β : Type*} [AddCommMonoid β] {M : Type*} [AddCommMonoid M] [Preorder M] [VNorm β M]
  [VectorNormed β M]
  {T : MultisubadditiveMap α β} {A : (i : ι) → EQuasinorm.Couple (α i)} {B' : EQuasinorm β}
  {θ : ι → ℝ} {C q c₁ c₂ : ℝ≥0∞}

omit [DecidableEq ι] [VectorNormed β M] in
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
The solid {name}`ESeminorm` `S`, equivalent to `B'` raised to the power `q.toReal` through `h₁`
and `h₂`, is where the `p`-normed hypothesis of the note enters; `S = B'` and `q = 1` is the
subadditive case. -/
lemma enorm_le_mul_prod_eLpNorm_jSummand (hq0 : q ≠ 0) (hq : q ≠ ∞)
    (S : ESeminorm β) [S.toEQuasinorm.IsSolid]
    (h₁ : ∀ x : β, ‖x‖ₑ[B'] ^ q.toReal ≤ c₁ * ‖x‖ₑ[S])
    (h₂ : ∀ x : β, ‖x‖ₑ[S] ≤ c₂ * ‖x‖ₑ[B'] ^ q.toReal)
    (hθ : ∀ i, θ i ∈ Icc (0 : ℝ) 1)
    (hC : ∀ a : (i : ι) → α i, ‖T a‖ₑ[B'] ≤
      C * ∏ i, ‖a i‖ₑ[(A i).fst] ^ (1 - θ i) * ‖a i‖ₑ[(A i).snd] ^ (θ i))
    {N : ι → ℕ} (hN : ∀ i, 0 < N i) (u : ∀ i, Fin (2 * N i) → α i) :
    ‖T (fun i ↦ ∑ k, u i k)‖ₑ[B'] ≤
      (c₁ * c₂) ^ (q.toReal)⁻¹ * C *
        ∏ i, eLpNorm (jSummand (A i) (θ i) (N i) (u i)) q Measure.count := by
  have hp : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  have : ∀ i, Nonempty (Fin (2 * N i)) := fun i ↦ ⟨⟨0, by have := hN i; omega⟩⟩
  rw [← ENNReal.rpow_le_rpow_iff hp, ENNReal.mul_rpow_of_nonneg _ _ hp.le,
    ENNReal.mul_rpow_of_nonneg _ _ hp.le, ENNReal.rpow_inv_rpow hp.ne',
    ← ENNReal.prod_rpow_of_nonneg hp.le]
  calc ‖T (fun i ↦ ∑ k, u i k)‖ₑ[B'] ^ q.toReal
      ≤ c₁ * c₂ * ∑ g : (∀ i, Fin (2 * N i)), ‖T (fun i ↦ u i (g i))‖ₑ[B'] ^ q.toReal :=
        MultisubadditiveMap.enorm_le_mul_sum (B := B'.pow q.toReal) S h₁ h₂ u
    _ ≤ c₁ * c₂ * ∑ _g : (∀ i, Fin (2 * N i)),
        C ^ q.toReal * ∏ i, jSummand (A i) (θ i) (N i) (u i) (_g i) ^ q.toReal := by
        gcongr with g
        rw [ENNReal.prod_rpow_of_nonneg hp.le, ← ENNReal.mul_rpow_of_nonneg _ _ hp.le]
        exact ENNReal.rpow_le_rpow (enorm_le_mul_prod_jSummand hθ hC u g) hp.le
    _ = c₁ * c₂ * (C ^ q.toReal *
        ∑ g : (∀ i, Fin (2 * N i)), ∏ i, jSummand (A i) (θ i) (N i) (u i) (g i) ^ q.toReal) := by
        rw [← Finset.mul_sum]
    _ = c₁ * c₂ * (C ^ q.toReal * ∏ i, ∑ k, jSummand (A i) (θ i) (N i) (u i) k ^ q.toReal) := by
        rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    _ = _ := by simp_rw [eLpNorm_count_rpow_eq_sum hq0 hq]; ring

lemma enorm_le_mul_prod_jInfNorm (hq0 : q ≠ 0) (hq : q ≠ ∞)
    (S : ESeminorm β) [S.toEQuasinorm.IsSolid] (hc₁ : c₁ ≠ ∞) (hc₂ : c₂ ≠ ∞)
    (h₁ : ∀ x : β, ‖x‖ₑ[B'] ^ q.toReal ≤ c₁ * ‖x‖ₑ[S])
    (h₂ : ∀ x : β, ‖x‖ₑ[S] ≤ c₂ * ‖x‖ₑ[B'] ^ q.toReal)
    (hθ : ∀ i, θ i ∈ Icc (0 : ℝ) 1) (hCfin : C ≠ ∞)
    (hC : ∀ a : (i : ι) → α i, ‖T a‖ₑ[B'] ≤
      C * ∏ i, ‖a i‖ₑ[(A i).fst] ^ (1 - θ i) * ‖a i‖ₑ[(A i).snd] ^ (θ i))
    (a : ∀ i, α i) (hfin : ∀ i, jInfNormQ (A i) (θ i) q (a i) ≠ ∞) :
    ‖T a‖ₑ[B'] ≤ (c₁ * c₂) ^ (q.toReal)⁻¹ * C * ∏ i, jInfNormQ (A i) (θ i) q (a i) := by
  have hDfin : (c₁ * c₂) ^ (q.toReal)⁻¹ * C ≠ ∞ :=
    (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
        (ENNReal.mul_ne_top hc₁ hc₂)) hCfin.lt_top).ne
  let F : ∀ i, Decomp (α i) (a i) → ℝ≥0∞ := fun i d ↦
    eLpNorm (jSummand (A i) (θ i) (d.1 + 1) d.2.1) q Measure.count
  have hJ : ∀ i, (⨅ d, F i d) = jInfNormQ (A i) (θ i) q (a i) :=
    fun i ↦ (jInfNormQ_eq_iInf_decomp ..).symm
  have hstep : ∀ g : (∀ i, Decomp (α i) (a i)),
      ‖T a‖ₑ[B'] ≤ (c₁ * c₂) ^ (q.toReal)⁻¹ * C * ∏ i, F i (g i) := by
    intro g
    have h := enorm_le_mul_prod_eLpNorm_jSummand hq0 hq S h₁ h₂ hθ hC (N := fun i ↦ (g i).1 + 1)
      (fun _ ↦ Nat.succ_pos _) (fun i ↦ (g i).2.1)
    rwa [show (fun i ↦ ∑ k, (g i).2.1 k) = a from funext fun i ↦ (g i).2.2] at h
  calc ‖T a‖ₑ[B']
      ≤ ⨅ g : (∀ i, Decomp (α i) (a i)), (c₁ * c₂) ^ (q.toReal)⁻¹ * C * ∏ i, F i (g i) :=
        le_iInf hstep
    _ = (c₁ * c₂) ^ (q.toReal)⁻¹ * C * ⨅ g : (∀ i, Decomp (α i) (a i)), ∏ i, F i (g i) :=
        (ENNReal.mul_iInf (by simp [hDfin])).symm
    _ ≤ (c₁ * c₂) ^ (q.toReal)⁻¹ * C * ∏ i, ⨅ d, F i d := by
        gcongr
        exact iInf_prod_le_prod_iInf F (fun i ↦ (hJ i).symm ▸ hfin i) Finset.univ
    _ = (c₁ * c₂) ^ (q.toReal)⁻¹ * C * ∏ i, jInfNormQ (A i) (θ i) q (a i) := by simp_rw [hJ]

end Core

section Omega

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, AddCommGroup (α i)]
  {β : Type*} [AddCommMonoid β] {M : Type*} [AddCommMonoid M] [Preorder M] [VNorm β M]
  [VectorNormed β M]
  {T : MultisubadditiveMap α β} {θ : ι → ℝ}

/-- Janson's Lemma 2, direction (ii) → (i), for arbitrary quasi-normed couples on the source
side and an arbitrary exponent `q` on the target side.

Nothing here uses that the `A i` are seminorms. On the target side the only hypothesis is `hS`,
which asks for a solid {name}`ESeminorm` equivalent to `B'` raised to the power `q.toReal`; by
{name}`EQuasinorm.aokiRolewicz_equiv_pow` such an `S` always exists, so this is no restriction —
but the exponent is then forced on the source side too, through `hL1` (Lemma 1 with `q_i = q`).
This is Janson's Remark 9.

The finiteness guard in {name}`MultisubadditiveMap.IsBoundedFor` is what makes the conclusion
true as stated: without it the case `‖a j‖ = 0` together with `‖a i‖ = ∞` would force
`‖T a‖ = 0`, since `0 * ∞ = 0` in `ℝ≥0∞`. -/
theorem exists_enorm_kMethod_le {A : (i : ι) → EQuasinorm.Couple (α i)} {B' : EQuasinorm β}
    {q : ℝ≥0∞} (hq0 : q ≠ 0) (hq : q ≠ ∞)
    (hθ : ∀ i, θ i ∈ Icc (0 : ℝ) 1)
    (S : ESeminorm β) [S.toEQuasinorm.IsSolid] (hS : S.toEQuasinorm ≈ B'.pow q.toReal)
    (hL1 : ∀ i, ∃ c : ℝ≥0∞, c < ∞ ∧ ∀ x,
      jInfNormQ (A i) (θ i) q x ≤ c * ‖x‖ₑ[(A i).kMethod (θ i) q])
    (h : ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (a : (i : ι) → α i), ‖T a‖ₑ[B'] ≤
        C * ∏ i, ‖a i‖ₑ[(A i).fst] ^ (1 - θ i : ℝ) * ‖a i‖ₑ[(A i).snd] ^ (θ i : ℝ)) :
    ∃ C' : ℝ≥0∞, T.IsBoundedFor (fun i ↦ (A i).kMethod (θ i) q) B' C' := by
  obtain ⟨C, hCfin, hC⟩ := h
  obtain ⟨⟨c₁, hc₁, h₁⟩, ⟨c₂, hc₂, h₂⟩⟩ := hS
  choose C₁ hC₁ hC₁le using hL1
  have hDfin : (c₁ * c₂) ^ (q.toReal)⁻¹ * C < ∞ :=
    ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
        (ENNReal.mul_ne_top hc₁.ne hc₂.ne)) hCfin
  refine ⟨(c₁ * c₂) ^ (q.toReal)⁻¹ * C * ∏ i, C₁ i,
    ENNReal.mul_lt_top hDfin (ENNReal.prod_lt_top fun i _ ↦ hC₁ i), fun a ha ↦ ?_⟩
  have hfin : ∀ i, jInfNormQ (A i) (θ i) q (a i) ≠ ∞ := fun i ↦
    ((hC₁le i (a i)).trans_lt (ENNReal.mul_lt_top (hC₁ i) (ha i))).ne
  calc ‖T a‖ₑ[B']
    _ ≤ (c₁ * c₂) ^ (q.toReal)⁻¹ * C * ∏ i, jInfNormQ (A i) (θ i) q (a i) :=
      enorm_le_mul_prod_jInfNorm hq0 hq S hc₁.ne hc₂.ne h₁ h₂ hθ hCfin.ne hC a hfin
    _ ≤ (c₁ * c₂) ^ (q.toReal)⁻¹ * C * ∏ i, C₁ i * ‖a i‖ₑ[(A i).kMethod (θ i) q] := by
      gcongr; exact hC₁le _ _
    _ = ((c₁ * c₂) ^ (q.toReal)⁻¹ * C * ∏ i, C₁ i) *
        ∏ i, ‖a i‖ₑ[(A i).kMethod (θ i) q] := by
      rw [Finset.prod_mul_distrib]; ring

variable {A : (i : ι) → Couple (α i)} {B : Couple β} {cα₀ : ℝ} {cα : ι → ℝ}

/-- Membership in {name}`Ω`, with the exponents `q_i = q_0 = q` supplied by the solid
{name}`ESeminorm` equivalent to the `q`-th power of the target. -/
theorem mem_Ω_of_forall_enorm_le {q : ℝ≥0∞} (hq0 : q ≠ 0) (hq : q ≠ ∞)
    (hθ : ∀ i, θ i ∈ Ioo (0 : ℝ) 1)
    (hθ₀ : 0 ≤ cα₀ + ∑ i, cα i * θ i)
    (S : ESeminorm β) [S.toEQuasinorm.IsSolid]
    (hS : S.toEQuasinorm ≈ (B.kMethod (cα₀ + ∑ i, cα i * θ i) ∞).pow q.toReal)
    (h : ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (a : (i : ι) → α i),
      ‖T a‖ₑ[B.kMethod (cα₀ + ∑ i, cα i * θ i) ∞] ≤
        C * ∏ i, ‖a i‖ₑ[(A i).fst] ^ (1 - θ i : ℝ) * ‖a i‖ₑ[(A i).snd] ^ (θ i : ℝ)) :
    θ ∈ Ω T A B cα₀ cα := by
  obtain ⟨C', hC'⟩ := exists_enorm_kMethod_le hq0 hq
    (fun i ↦ Ioo_subset_Icc_self (hθ i)) S hS
    (fun i ↦ jInfNorm_le_kNorm (A i) (θ i) (hθ i) q) h
  exact ⟨∞, fun _ ↦ q, hθ₀, C', hC'⟩

end Omega

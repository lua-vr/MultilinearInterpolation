/-
Copyright (c) 2026 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/

module

public import MultilinearInterpolation.EQuasinorm.Multisubadditive
public import MultilinearInterpolation.EQuasinorm.ESeminorm
public import MultilinearInterpolation.KMethod
public import MultilinearInterpolation.Janson
import VersoBlueprint
meta import VersoBlueprint

/-!
Stub of the proof of Janson's Lemma 1 ({name}`jInfNorm_le_kNorm`), following the fundamental
lemma of Bergh–Löfström (Lemma 3.3.2), with the series truncated to `2N` terms.

For `x ∈ Δ(Ā)`, `δ > 0` and `ν ∈ ℤ`, choose `x = a₀ ν + (x - a₀ ν)` with
`‖a₀ ν‖₀ + 2^ν ‖x - a₀ ν‖₁ ≤ K(2^ν, x) + δ`. The sequence `v` equal to `0` below `-N`,
to `a₀` on `[-N, N-2]` and to `x` from `N-1` on telescopes:
`x = ∑_{ν=-N}^{N-1} (v ν - v (ν-1))`. The interior pieces satisfy
`J(2^ν, u_ν) ≲ K(2^ν, x) + δ`; the two end pieces pick up an extra `2^{-N}‖x‖₁`, resp. `‖x‖₀`,
whose weighted contributions vanish as `N → ∞` because `0 < θ < 1`. Lemma 3.1.3
({name}`EQuasinorm.discreteKMethod_equiv_kmethod`) then passes to the continuous norm.

Compared with {name}`jInfNorm_le_kNorm`, two hypotheses are added:
* `x ∈ Δ(Ā)`. A finite sum of elements of `Δ(Ā)` lies in `Δ(Ā)`, so for `q ≠ 0`
  {name}`jInfNorm` is `∞` outside `Δ(Ā)`, while the `K`-norm need not be.
* Symmetry `‖-y‖ = ‖y‖`, used to estimate the differences `u_ν`.

For solid couples, {lit}`EQuasinorm.Couple.exists_fin_decomp_of_isSolid` gives a decomposition
without differences, so symmetry is not needed there.
-/

@[expose] public noncomputable section

open Set MeasureTheory EQuasinorm Filter Topology
open scoped ENNReal NNReal

namespace EQuasinorm.Couple

variable {α : Type*} [AddCommGroup α] (A : Couple α) {θ : ℝ} {q : ℝ≥0∞} {x : α}

/-- Both quasinorms of the couple are symmetric. -/
def IsSymm : Prop :=
  (∀ y : α, ‖-y‖ₑ[A.fst] = ‖y‖ₑ[A.fst]) ∧ ∀ y : α, ‖-y‖ₑ[A.snd] = ‖y‖ₑ[A.snd]

/-- Step 1: near-optimal decompositions at every dyadic level. -/
lemma exists_decomp_le_kNorm_add {δ : ℝ≥0∞} (hδ : δ ≠ 0) (x : α) :
    ∃ a₀ : ℤ → α, ∀ ν : ℤ,
      ‖a₀ ν‖ₑ[A.fst] + 2 ^ ν * ‖x - a₀ ν‖ₑ[A.snd] ≤ A.kNorm (2 ^ ν) x + δ := by
  have : ∀ ν : ℤ, ∃ y : α,
      ‖y‖ₑ[A.fst] + 2 ^ ν * ‖x - y‖ₑ[A.snd] ≤ A.kNorm (2 ^ ν) x + δ := by
    intro ν
    by_cases hK : A.kNorm (2 ^ ν) x = ∞
    · exact ⟨0, by simp [hK]⟩
    obtain ⟨x₀, x₁, rfl, h⟩ := exists_decomp_lt_of_lt_kNorm (ENNReal.lt_add_right hK hδ)
    exact ⟨x₀, by simpa using h.le⟩
  choose a₀ ha₀ using this
  exact ⟨a₀, ha₀⟩

/-- Subtraction-free finite decomposition for solid couples. Let $`x = y_ν + z_ν` for every
$`ν ∈ ℤ`, with $`y_ν = a_0(ν)` and $`z_ν = x - a_0(ν)`, and let $`N ≥ 1`. Then there are
$`u_{-N}, …, u_{N-1}` (the piece $`u_ν` sits at index $`k = ν + N`) with $`\sum_ν u_ν = x` and
* $`‖u_ν‖_0 ≤ ‖y_ν‖_0` for $`ν < N - 1`, and $`‖u_{N-1}‖_0 ≤ ‖x‖_0`;
* $`‖u_ν‖_1 ≤ ‖z_{ν-1}‖_1` for $`ν > -N`, and $`‖u_{-N}‖_1 ≤ ‖x‖_1`.

Proof. Put $`w_{-N-1} = x`. For $`ν = -N, …, N-2` we construct $`u_ν, w_ν` with
$$`w_{ν-1} = u_ν + w_ν,\quad |w_ν| ≤ |x|,\quad |w_ν| ≤ |z_ν|,\quad |u_ν| ≤ |y_ν|,\quad
|u_ν| ≤ |w_{ν-1}|.`
Suppose $`|w_{ν-1}| ≤ |x|`; for $`ν = -N` this is reflexivity. Since $`x = y_ν + z_ν`,
subadditivity of the modulus gives $`|w_{ν-1}| ≤ |x| ≤ |y_ν| + |z_ν|`. The Riesz property
{name}`VectorNormed.exists_decomp` applied to $`w_{ν-1}` gives $`w_{ν-1} = u_ν + w_ν` with
$`|u_ν| ≤ |y_ν|`, $`|w_ν| ≤ |z_ν|`, $`|u_ν| ≤ |w_{ν-1}|` and $`|w_ν| ≤ |w_{ν-1}|`; the last one
and transitivity give $`|w_ν| ≤ |x|`.

Put $`u_{N-1} = w_{N-2}`. Unfolding the recursion,
$`x = u_{-N} + w_{-N} = ⋯ = u_{-N} + ⋯ + u_{N-2} + w_{N-2} = \sum_{ν=-N}^{N-1} u_ν`.

Each norm bound follows from a modulus inequality by solidity:
* $`|u_ν| ≤ |y_ν|` gives $`‖u_ν‖_0 ≤ ‖y_ν‖_0`;
* for $`ν > -N`, $`|u_ν| ≤ |w_{ν-1}| ≤ |z_{ν-1}|` gives $`‖u_ν‖_1 ≤ ‖z_{ν-1}‖_1`;
* for $`ν = -N`, $`|u_{-N}| ≤ |w_{-N-1}| = |x|` gives $`‖u_{-N}‖_1 ≤ ‖x‖_1`;
* $`|w_{N-2}| ≤ |x|` gives $`‖u_{N-1}‖_0 ≤ ‖x‖_0`, and $`|w_{N-2}| ≤ |z_{N-2}|` gives
  $`‖u_{N-1}‖_1 ≤ ‖z_{N-2}‖_1`.
-/
lemma exists_fin_decomp_of_isSolid {M : Type*} [AddCommMonoid M] [Preorder M] [VNorm α M]
    [VectorNormed α M]
    [A.fst.IsSolid] [A.snd.IsSolid] (x : α) (a₀ : ℤ → α) {N : ℕ} (hN : 0 < N) :
    ∃ u : Fin (2 * N) → α, ∑ k, u k = x ∧ ∀ k : Fin (2 * N),
      let ν : ℤ := (k : ℕ) - N
      ‖u k‖ₑ[A.fst] ≤ (if ν = N - 1 then ‖x‖ₑ[A.fst] else ‖a₀ ν‖ₑ[A.fst]) ∧
      ‖u k‖ₑ[A.snd] ≤ (if ν = -N then ‖x‖ₑ[A.snd] else ‖x - a₀ (ν - 1)‖ₑ[A.snd]) := by
  sorry

/-- The truncation of `a₀` to `[-N, N-2]`, extended by `0` below and by `x` above. -/
def truncSeq (x : α) (a₀ : ℤ → α) (N : ℕ) (ν : ℤ) : α :=
  if ν < -N then 0 else if ν < N - 1 then a₀ ν else x

/-- The `k`-th piece of the finite decomposition of `x`; it sits at level `ν = k - N`. -/
def fundDecomp (x : α) (a₀ : ℤ → α) (N : ℕ) (k : Fin (2 * N)) : α :=
  truncSeq x a₀ N ((k : ℕ) - N) - truncSeq x a₀ N ((k : ℕ) - N - 1)

/-- Step 2: the pieces telescope to `x`. -/
lemma sum_fundDecomp {a₀ : ℤ → α} {N : ℕ} (hN : 0 < N) : ∑ k, fundDecomp x a₀ N k = x := by
  sorry

variable {A}

/-- Step 3: the pointwise `J`-estimate. Interior pieces use (1) at levels `ν` and `ν - 1`
together with monotonicity of `K(·, x)`; the end pieces `k = 0` and `k = 2N - 1` also use
`x ∈ Δ(Ā)`. -/
lemma jNorm_fundDecomp_le (hsymm : A.IsSymm) (hx₀ : ‖x‖ₑ[A.fst] ≠ ∞) (hx₁ : ‖x‖ₑ[A.snd] ≠ ∞)
    {δ : ℝ≥0∞} {a₀ : ℤ → α}
    (ha₀ : ∀ ν : ℤ, ‖a₀ ν‖ₑ[A.fst] + 2 ^ ν * ‖x - a₀ ν‖ₑ[A.snd] ≤ A.kNorm (2 ^ ν) x + δ)
    {N : ℕ} (k : Fin (2 * N)) :
    A.jNorm (2 ^ (((k : ℕ) : ℤ) - N)) (fundDecomp x a₀ N k) ≤
      3 * max A.fst.C A.snd.C * (A.kNorm (2 ^ (((k : ℕ) : ℤ) - N)) x + δ +
        (if (k : ℕ) = 0 then 2 ^ (-(N : ℤ)) * ‖x‖ₑ[A.snd] else 0) +
        (if (k : ℕ) = 2 * N - 1 then ‖x‖ₑ[A.fst] else 0)) := by
  sorry

/-- Step 4: the `ℓ^q`-estimate. The interior terms are dominated by the
{name}`EQuasinorm.discreteKMethod` norm; the constant `c` absorbs `3 max(C₀, C₁)` and the
quasi-triangle constant of `ℓ^q`. -/
lemma eLpNorm_fundDecomp_le (hθ : θ ∈ Ioo 0 1) (hsymm : A.IsSymm) :
    ∃ c : ℝ≥0∞, c < ∞ ∧ ∀ x : α, ‖x‖ₑ[A.fst] ≠ ∞ → ‖x‖ₑ[A.snd] ≠ ∞ →
    ∀ (δ : ℝ≥0∞) (a₀ : ℤ → α),
    (∀ ν : ℤ, ‖a₀ ν‖ₑ[A.fst] + 2 ^ ν * ‖x - a₀ ν‖ₑ[A.snd] ≤ A.kNorm (2 ^ ν) x + δ) →
    ∀ N : ℕ, 0 < N →
    eLpNorm (fun k : Fin (2 * N) ↦
        let n : ℝ := k - N
        2 ^ (-θ * n) * A.jNorm (2 ^ n) (fundDecomp x a₀ N k)) q Measure.count ≤
      c * (‖x‖ₑ[A.discreteKMethod θ q] +
        δ * eLpNorm (fun k : Fin (2 * N) ↦ (2 : ℝ≥0∞) ^ (-θ * ((k : ℝ) - N))) q Measure.count +
        2 ^ ((θ - 1) * N) * ‖x‖ₑ[A.snd] + 2 ^ (-θ * (N - 1)) * ‖x‖ₑ[A.fst]) := by
  sorry

omit [AddCommGroup α] in
/-- Step 5: the contributions of the end pieces vanish, since `0 < θ < 1`. -/
lemma tendsto_boundary_terms [AddCommMonoid α] {A : Couple α} (hθ : θ ∈ Ioo 0 1)
    (hx₀ : ‖x‖ₑ[A.fst] ≠ ∞) (hx₁ : ‖x‖ₑ[A.snd] ≠ ∞) :
    Tendsto (fun N : ℕ ↦ (2 : ℝ≥0∞) ^ ((θ - 1) * N) * ‖x‖ₑ[A.snd] +
      2 ^ (-θ * (N - 1)) * ‖x‖ₑ[A.fst]) atTop (𝓝 0) := by
  sorry

/-- Step 6: Lemma 1 with the discrete `K`-norm. Given `ε > 0`, choose `N` by
{name}`EQuasinorm.Couple.tendsto_boundary_terms`, then `δ` so small that the `δ`-term of
{name}`EQuasinorm.Couple.eLpNorm_fundDecomp_le` is below `ε` (the window has `2N` points),
and conclude with {name}`EQuasinorm.Couple.sum_fundDecomp` and
{name}`ENNReal.le_of_forall_pos_le_add`. -/
lemma jInfNorm_le_mul_discreteKMethod (hθ : θ ∈ Ioo 0 1) (hsymm : A.IsSymm) :
    ∃ c : ℝ≥0∞, c < ∞ ∧ ∀ x : α, ‖x‖ₑ[A.fst] ≠ ∞ → ‖x‖ₑ[A.snd] ≠ ∞ →
      jInfNorm A θ q x ≤ c * ‖x‖ₑ[A.discreteKMethod θ q] := by
  sorry

/-- Janson's Lemma 1 for `x ∈ Δ(Ā)` and symmetric quasinorms. -/
@[blueprint
  (proofUses := [EQuasinorm.discreteKMethod_equiv_kmethod])]
theorem jInfNorm_le_mul_kMethod (hθ : θ ∈ Ioo 0 1) (hsymm : A.IsSymm) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ x : α, ‖x‖ₑ[A.fst] ≠ ∞ → ‖x‖ₑ[A.snd] ≠ ∞ →
      jInfNorm A θ q x ≤ C * ‖x‖ₑ[A.kMethod θ q] := by
  obtain ⟨c, hc, h⟩ := jInfNorm_le_mul_discreteKMethod (q := q) hθ hsymm
  obtain ⟨-, ⟨c', hc', h'⟩⟩ :=
    EQuasinorm.discreteKMethod_equiv_kmethod (A₀ := A.fst) (A₁ := A.snd) (θ := θ) (q := q)
  refine ⟨c * c', ENNReal.mul_lt_top hc hc', fun x hx₀ hx₁ ↦ ?_⟩
  calc jInfNorm A θ q x ≤ c * ‖x‖ₑ[A.discreteKMethod θ q] := h x hx₀ hx₁
    _ ≤ c * (c' * ‖x‖ₑ[A.kMethod θ q]) := by gcongr; exact h' x
    _ = c * c' * ‖x‖ₑ[A.kMethod θ q] := (mul_assoc ..).symm

end EQuasinorm.Couple

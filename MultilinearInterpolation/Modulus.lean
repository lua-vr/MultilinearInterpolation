/-
Copyright (c) 2026 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/

module

public import MultilinearInterpolation.EQuasinorm.ESeminorm

/-!
# Moduli and solid quasinorms.

A modulus $`|\cdot| \colon β → M` takes values in an ordered monoid $`M`, e.g.
$`‖\cdot‖ₑ ∘ b ∈ γ → ℝ≥0∞` for $`b ∈ γ → ε`. A quasinorm on $`β` is solid if it is monotone
along $`|\cdot|`.
-/

open Verso.Genre Manual Informal InlineLean

@[expose] public noncomputable section

open EQuasinorm
open scoped ENNReal NNReal

variable {β M : Type*} [AddCommMonoid β]

/-- A modulus $`β → M`, with values in a second type $`M`. -/
class Modulus (β : Type*) (M : outParam Type*) where
  modulus : β → M

notation "|" e "|ₑ" => Modulus.modulus e

variable (β) in
/--
A decomposable modulus, following the lattice-normed spaces of Kantorovich (see Kusraev,
*Dominated Operators*, Ch. 2), with decomposability weakened to bounds by values of $`|\cdot|`.

todo: what about definition 3.5.1 in BL ("is of class")? a different possible approach would be to
quantify over all spaces that are of the class of the couple.
-/
@[blueprint]
class Modulus.IsDecomposable (M : outParam Type*) [AddCommMonoid M] [Preorder M] [Modulus β M] :
    Prop where
  /-- zero is small -/
  modulus_zero_le (x : β) : |(0 : β)|ₑ ≤ |x|ₑ
  /-- subadditivity -/
  modulus_add_le (x y : β) : |x + y|ₑ ≤ |x|ₑ + |y|ₑ
  /-- decomposability -/
  exists_decomp {x y₀ y₁ : β} (h : |x|ₑ ≤ |y₀|ₑ + |y₁|ₑ) :
    ∃ x₀ x₁, x = x₀ + x₁ ∧ |x₀|ₑ ≤ |y₀|ₑ ∧ |x₁|ₑ ≤ |y₁|ₑ ∧ |x₀|ₑ ≤ |x|ₑ ∧ |x₁|ₑ ≤ |x|ₑ

section Instances

variable {J : Type*} {γ : J → Type*} {N : J → Type*}

/-- A product carries the pointwise modulus. -/
instance Pi.instModulus [∀ j, Modulus (γ j) (N j)] : Modulus (∀ j, γ j) (∀ j, N j) :=
  ⟨fun f j ↦ |f j|ₑ⟩

@[simp]
lemma Pi.modulus_apply [∀ j, Modulus (γ j) (N j)] (f : ∀ j, γ j) (j : J) : |f|ₑ j = |f j|ₑ := rfl

instance Pi.instIsDecomposable [∀ j, AddCommMonoid (γ j)] [∀ j, AddCommMonoid (N j)]
    [∀ j, Preorder (N j)] [∀ j, Modulus (γ j) (N j)] [∀ j, Modulus.IsDecomposable (γ j) (N j)] :
    Modulus.IsDecomposable (∀ j, γ j) (∀ j, N j) where
  modulus_zero_le x j := Modulus.IsDecomposable.modulus_zero_le (x j)
  modulus_add_le f g j := Modulus.IsDecomposable.modulus_add_le (f j) (g j)
  exists_decomp h := by
    choose u v huv hu hv hu' hv' using fun j ↦ Modulus.IsDecomposable.exists_decomp (h j)
    exact ⟨u, v, funext huv, hu, hv, hu', hv'⟩

/-- The extended norm as a modulus. Not an instance: on a finite product, which carries the sup
norm, it would compete with {lit}`Pi.instModulus`. Enable it per type with
{lit}`instance : Modulus ε ℝ≥0∞ := .ofENorm ε`. -/
abbrev Modulus.ofENorm (ε : Type*) [ENorm ε] : Modulus ε ℝ≥0∞ := ⟨enorm⟩

/-- In a real normed space, the extended norm is decomposable: split $`x` proportionally,
$`x = c x + (1 - c) x` with $`c = \min(1, ‖y₀‖ / ‖x‖)`. -/
lemma Modulus.isDecomposable_ofENorm (E : Type*) [SeminormedAddCommGroup E] [NormedSpace ℝ E] :
    letI := Modulus.ofENorm E; Modulus.IsDecomposable E ℝ≥0∞ := by
  let := Modulus.ofENorm E
  refine ⟨fun x ↦ ?_, fun x y ↦ ?_, fun {x y₀ y₁} h ↦ ?_⟩
  · simp [Modulus.modulus, ← ofReal_norm]
  · simp only [Modulus.modulus, ← ofReal_norm]
    rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (norm_add_le x y)
  simp only [Modulus.modulus, ← ofReal_norm] at h ⊢
  rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  set c : ℝ := min 1 (‖y₀‖ / ‖x‖)
  have hc0 : 0 ≤ c := le_min zero_le_one (by positivity)
  have hc1 : c ≤ 1 := min_le_left ..
  have hcx : c * ‖x‖ ≤ ‖y₀‖ := by
    rcases (norm_nonneg x).eq_or_lt with hx | hx
    · simp [← hx]
    · exact (le_div_iff₀ hx).1 (min_le_right ..)
  have hcx' : (1 - c) * ‖x‖ ≤ ‖y₁‖ := by
    rcases min_choice 1 (‖y₀‖ / ‖x‖) with hc | hc <;> simp only [c, hc]
    · simp
    · rcases (norm_nonneg x).eq_or_lt with hx | hx
      · simp [← hx]
      · rw [sub_mul, div_mul_cancel₀ _ hx.ne']; linarith
  refine ⟨c • x, (1 - c) • x, by rw [← add_smul]; simp, ?_⟩
  simp only [norm_smul, Real.norm_of_nonneg hc0, Real.norm_of_nonneg (sub_nonneg.2 hc1),
    ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)]
  refine ⟨hcx, hcx', ?_, ?_⟩ <;> nlinarith [norm_nonneg x]

/-- A real number is measured by its extended norm. -/
instance Real.instModulus : Modulus ℝ ℝ≥0∞ := .ofENorm ℝ

@[simp] lemma Real.modulus_eq (x : ℝ) : |x|ₑ = ‖x‖ₑ := rfl

instance Real.instIsDecomposable : Modulus.IsDecomposable ℝ ℝ≥0∞ :=
  Modulus.isDecomposable_ofENorm ℝ

/-- A complex number is measured by its extended norm. -/
instance Complex.instModulus : Modulus ℂ ℝ≥0∞ := .ofENorm ℂ

@[simp] lemma Complex.modulus_eq (z : ℂ) : |z|ₑ = ‖z‖ₑ := rfl

instance Complex.instIsDecomposable : Modulus.IsDecomposable ℂ ℝ≥0∞ :=
  Modulus.isDecomposable_ofENorm ℂ

/-- An element of $`[0,∞]` is its own modulus. -/
instance ENNReal.instModulus : Modulus ℝ≥0∞ ℝ≥0∞ := .ofENorm ℝ≥0∞

@[simp] lemma ENNReal.modulus_eq (x : ℝ≥0∞) : |x|ₑ = x := enorm_eq_self x

instance ENNReal.instIsDecomposable : Modulus.IsDecomposable ℝ≥0∞ ℝ≥0∞ where
  modulus_zero_le _ := zero_le
  modulus_add_le _ _ := le_rfl
  exists_decomp {a b c} h := by
    simp only [ENNReal.modulus_eq] at h
    refine ⟨min a b, a - min a b, (add_tsub_cancel_of_le (min_le_left ..)).symm,
      min_le_right .., ?_, min_le_left .., tsub_le_self⟩
    simp only [ENNReal.modulus_eq]
    rcases le_total a b with h₁ | h₁
    · simp [min_eq_left h₁]
    · rw [min_eq_right h₁, tsub_le_iff_right]
      exact h.trans_eq (add_comm ..)

/-- Real-valued functions, with the pointwise extended norm. -/
example {X : Type*} : Modulus.IsDecomposable (X → ℝ) (X → ℝ≥0∞) := inferInstance

/-- $`[0,∞]`-valued functions, with the pointwise identity. -/
example {X : Type*} : Modulus.IsDecomposable (X → ℝ≥0∞) (X → ℝ≥0∞) := inferInstance

end Instances

variable [AddCommMonoid M] [Preorder M] [Modulus β M]

namespace EQuasinorm

/-- A quasinorm is solid if it is monotone along the modulus. -/
class IsSolid (B : EQuasinorm β) : Prop where
  solid {x y : β} : |x|ₑ ≤ |y|ₑ → ‖x‖ₑ[B] ≤ ‖y‖ₑ[B]

variable {A₀ A₁ B : EQuasinorm β} {t : ℝ≥0∞} {x y a b c : β}

/-- A modulus inequality $`|a| ≤ |b| + |c|` transfers to any solid quasinorm, up to its
subadditivity constant. -/
@[blueprint]
lemma IsSolid.enorm_le_mul_of_modulus_le [Modulus.IsDecomposable β M] [B.IsSolid]
    (h : |a|ₑ ≤ |b|ₑ + |c|ₑ) : ‖a‖ₑ[B] ≤ B.C * (‖b‖ₑ[B] + ‖c‖ₑ[B]) := by
  obtain ⟨u, v, huv, hu, hv, -⟩ := Modulus.IsDecomposable.exists_decomp h
  calc ‖a‖ₑ[B] = ‖u + v‖ₑ[B] := by rw [huv]
    _ ≤ B.C * (‖u‖ₑ[B] + ‖v‖ₑ[B]) := B.enorm_add_le_mul u v
    _ ≤ _ := by gcongr <;> exact IsSolid.solid ‹_›

/-- The intersection of a couple of solid quasinorms, with the norm $`J(t,-)`, is solid. -/
instance IsSolid.skewedInf [A₀.IsSolid] [A₁.IsSolid] : (A₀.skewedInf A₁ t).IsSolid where
  solid h := by
    refine max_le_max (IsSolid.solid h) ?_
    gcongr
    exact IsSolid.solid h

instance IsSolid.inf [A₀.IsSolid] [A₁.IsSolid] : (A₀ ⊓ A₁).IsSolid := IsSolid.skewedInf

/-- The supremum of a couple of solid quasinorms, with the norm $`J(K,-)`, is solid. -/
@[blueprint]
lemma kNorm_le_kNorm_of_modulus_le [Modulus.IsDecomposable β M] [A₀.IsSolid] [A₁.IsSolid]
    (h : |x|ₑ ≤ |y|ₑ) (t : ℝ≥0∞) : A₀.kNorm A₁ t x ≤ A₀.kNorm A₁ t y := by
  refine le_iInf₂ fun a ha ↦ ?_
  have hy : |y|ₑ ≤ |a.1|ₑ + |a.2|ₑ := ha ▸ Modulus.IsDecomposable.modulus_add_le a.1 a.2
  obtain ⟨x₀, x₁, hx, h₀, h₁, -⟩ := Modulus.IsDecomposable.exists_decomp (h.trans hy)
  refine (kNorm_le_of_decomp hx t).trans (add_le_add (IsSolid.solid h₀) ?_)
  gcongr
  exact IsSolid.solid h₁

/-- The sum of a couple of solid quasinorms, with the norm $`K(t,-)`, is solid. -/
instance IsSolid.skewedSup [Modulus.IsDecomposable β M] [A₀.IsSolid] [A₁.IsSolid] :
    (A₀.skewedSup A₁ t).IsSolid where
  solid h := kNorm_le_kNorm_of_modulus_le h t

instance IsSolid.sup [Modulus.IsDecomposable β M] [A₀.IsSolid] [A₁.IsSolid] : (A₀ ⊔ A₁).IsSolid :=
  IsSolid.skewedSup

end EQuasinorm

namespace ESeminorm

variable {A : ESeminorm β} {a b c : β}

/-- {lit}`EQuasinorm.IsSolid.enorm_le_mul_of_modulus_le` for an {lit}`ESeminorm`: since $`C = 1`,
the inequality is genuine subadditivity. -/
@[blueprint]
lemma enorm_le_of_modulus_le [Modulus.IsDecomposable β M] [A.toEQuasinorm.IsSolid]
    (h : |a|ₑ ≤ |b|ₑ + |c|ₑ) : ‖a‖ₑ[A] ≤ ‖b‖ₑ[A] + ‖c‖ₑ[A] := by
  simpa using EQuasinorm.IsSolid.enorm_le_mul_of_modulus_le (B := A.toEQuasinorm) h

end ESeminorm

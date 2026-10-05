/-
Copyright (c) 2026 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/

module

public import MultilinearInterpolation.EQuasinorm.ESeminorm

/-!
# Vector norms and solid quasinorms.

A vector norm $`|\cdot| \colon β → M` takes values in an ordered monoid $`M`, e.g.
$`‖\cdot‖ₑ ∘ b ∈ γ → ℝ≥0∞` for $`b ∈ γ → ε`. A quasinorm on $`β` is solid if it is monotone
along $`|\cdot|`.
-/

open Verso.Genre Manual Informal InlineLean

@[expose] public noncomputable section

open EQuasinorm
open scoped ENNReal NNReal

variable {β M : Type*} [AddCommMonoid β]

/-- A vector-valued norm $`β → M`. -/
class VNorm (β : Type*) (M : outParam Type*) where
  vnorm : β → M

notation "|" e "|ₑ" => VNorm.vnorm e

variable (β M) in
/--
A decomposable vector norm, following the lattice-normed spaces of Kantorovich (see Kusraev,
*Dominated Operators*, Ch. 2), with decomposability weakened to bounds by values of $`|\cdot|`.

todo: what about definition 3.5.1 in BL ("is of class")? a different possible approach would be to
quantify over all spaces that are of the class of the couple.
-/
@[blueprint]
class VectorNormed [AddCommMonoid M] [Preorder M] [VNorm β M] : Prop where
  /-- zero is small -/
  vnorm_zero_le (x : β) : |(0 : β)|ₑ ≤ |x|ₑ
  /-- subadditivity -/
  vnorm_add_le (x y : β) : |x + y|ₑ ≤ |x|ₑ + |y|ₑ
  /-- decomposability -/
  exists_decomp {x y₀ y₁ : β} (h : |x|ₑ ≤ |y₀|ₑ + |y₁|ₑ) :
    ∃ x₀ x₁, x = x₀ + x₁ ∧ |x₀|ₑ ≤ |y₀|ₑ ∧ |x₁|ₑ ≤ |y₁|ₑ ∧ |x₀|ₑ ≤ |x|ₑ ∧ |x₁|ₑ ≤ |x|ₑ

section Instances

variable {J : Type*} {γ : J → Type*} {N : J → Type*}

/-- A product carries the pointwise vector norm. -/
instance Pi.instVNorm [∀ j, VNorm (γ j) (N j)] : VNorm (∀ j, γ j) (∀ j, N j) :=
  ⟨fun f j ↦ |f j|ₑ⟩

@[simp]
lemma Pi.vnorm_apply [∀ j, VNorm (γ j) (N j)] (f : ∀ j, γ j) (j : J) : |f|ₑ j = |f j|ₑ := rfl

instance Pi.instVectorNormed [∀ j, AddCommMonoid (γ j)] [∀ j, AddCommMonoid (N j)]
    [∀ j, Preorder (N j)] [∀ j, VNorm (γ j) (N j)] [∀ j, VectorNormed (γ j) (N j)] :
    VectorNormed (∀ j, γ j) (∀ j, N j) where
  vnorm_zero_le x j := VectorNormed.vnorm_zero_le (x j)
  vnorm_add_le f g j := VectorNormed.vnorm_add_le (f j) (g j)
  exists_decomp h := by
    choose u v huv hu hv hu' hv' using fun j ↦ VectorNormed.exists_decomp (h j)
    exact ⟨u, v, funext huv, hu, hv, hu', hv'⟩

/-- A real number is measured by its extended norm. -/
instance Real.instVNorm : VNorm ℝ ℝ≥0∞ := ⟨fun x ↦ ‖x‖ₑ⟩

@[simp] lemma Real.vnorm_eq (x : ℝ) : |x|ₑ = ‖x‖ₑ := rfl

instance Real.instVectorNormed : VectorNormed ℝ ℝ≥0∞ where
  vnorm_zero_le x := by simp
  vnorm_add_le := enorm_add_le
  exists_decomp {a b c} h := by
    simp only [Real.vnorm_eq, Real.enorm_eq_ofReal_abs] at h ⊢
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _),
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
    refine ⟨max (min a |b|) (-|b|), a - max (min a |b|) (-|b|), by ring, ?_⟩
    simp only [ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)]
    grind

/-- An element of $`[0,∞]` is its own vector norm. -/
instance ENNReal.instVNorm : VNorm ℝ≥0∞ ℝ≥0∞ := ⟨id⟩

@[simp] lemma ENNReal.vnorm_eq (x : ℝ≥0∞) : |x|ₑ = x := rfl

instance ENNReal.instVectorNormed : VectorNormed ℝ≥0∞ ℝ≥0∞ where
  vnorm_zero_le _ := zero_le
  vnorm_add_le _ _ := le_rfl
  exists_decomp {a b c} h := by
    simp only [ENNReal.vnorm_eq] at h
    refine ⟨min a b, a - min a b, (add_tsub_cancel_of_le (min_le_left ..)).symm,
      min_le_right .., ?_, min_le_left .., tsub_le_self⟩
    simp only [ENNReal.vnorm_eq]
    rcases le_total a b with h₁ | h₁
    · simp [min_eq_left h₁]
    · rw [min_eq_right h₁, tsub_le_iff_right]
      exact h.trans_eq (add_comm ..)

/-- Real-valued functions, with the pointwise extended norm. -/
example {X : Type*} : VectorNormed (X → ℝ) (X → ℝ≥0∞) := inferInstance

/-- $`[0,∞]`-valued functions, with the pointwise identity. -/
example {X : Type*} : VectorNormed (X → ℝ≥0∞) (X → ℝ≥0∞) := inferInstance

end Instances

variable [AddCommMonoid M] [Preorder M] [VNorm β M]

namespace EQuasinorm

/-- A quasinorm is solid if it is monotone along the vector norm. -/
class IsSolid (B : EQuasinorm β) : Prop where
  solid {x y : β} : |x|ₑ ≤ |y|ₑ → ‖x‖ₑ[B] ≤ ‖y‖ₑ[B]

variable {A₀ A₁ B : EQuasinorm β} {t : ℝ≥0∞} {x y a b c : β}

/-- A vector norm inequality $`|a| ≤ |b| + |c|` transfers to any solid quasinorm, up to its
subadditivity constant. -/
@[blueprint]
lemma IsSolid.enorm_le_mul_of_vnorm_le [VectorNormed β M] [B.IsSolid]
    (h : |a|ₑ ≤ |b|ₑ + |c|ₑ) : ‖a‖ₑ[B] ≤ B.C * (‖b‖ₑ[B] + ‖c‖ₑ[B]) := by
  obtain ⟨u, v, huv, hu, hv, -⟩ := VectorNormed.exists_decomp h
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
lemma kNorm_le_kNorm_of_vnorm_le [VectorNormed β M] [A₀.IsSolid] [A₁.IsSolid]
    (h : |x|ₑ ≤ |y|ₑ) (t : ℝ≥0∞) : A₀.kNorm A₁ t x ≤ A₀.kNorm A₁ t y := by
  refine le_iInf₂ fun a ha ↦ ?_
  have hy : |y|ₑ ≤ |a.1|ₑ + |a.2|ₑ := ha ▸ VectorNormed.vnorm_add_le a.1 a.2
  obtain ⟨x₀, x₁, hx, h₀, h₁, -⟩ := VectorNormed.exists_decomp (h.trans hy)
  refine (kNorm_le_of_decomp hx t).trans (add_le_add (IsSolid.solid h₀) ?_)
  gcongr
  exact IsSolid.solid h₁

/-- The sum of a couple of solid quasinorms, with the norm $`K(t,-)`, is solid. -/
instance IsSolid.skewedSup [VectorNormed β M] [A₀.IsSolid] [A₁.IsSolid] :
    (A₀.skewedSup A₁ t).IsSolid where
  solid h := kNorm_le_kNorm_of_vnorm_le h t

instance IsSolid.sup [VectorNormed β M] [A₀.IsSolid] [A₁.IsSolid] : (A₀ ⊔ A₁).IsSolid :=
  IsSolid.skewedSup

end EQuasinorm

namespace ESeminorm

variable {A : ESeminorm β} {a b c : β}

/-- {lit}`EQuasinorm.IsSolid.enorm_le_mul_of_vnorm_le` for an {lit}`ESeminorm`: since $`C = 1`,
the inequality is genuine subadditivity. -/
@[blueprint]
lemma enorm_le_of_vnorm_le [VectorNormed β M] [A.toEQuasinorm.IsSolid]
    (h : |a|ₑ ≤ |b|ₑ + |c|ₑ) : ‖a‖ₑ[A] ≤ ‖b‖ₑ[A] + ‖c‖ₑ[A] := by
  simpa using EQuasinorm.IsSolid.enorm_le_mul_of_vnorm_le (B := A.toEQuasinorm) h

end ESeminorm

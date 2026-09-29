/-
Copyright (c) 2026 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/

module

public import MultilinearInterpolation.EQuasinorm.ESeminorm

/-!
# Moduli and solid quasinorms.
-/

open Verso.Genre Manual Informal InlineLean

@[expose] public noncomputable section

open EQuasinorm
open scoped ENNReal NNReal

variable {β : Type*} [AddCommMonoid β]

class Abs β where
  toFun : β → β

notation "|" e "|ₑ" => Abs.toFun e



-- [[denote:20260928T205504::*The construction]]
variable (β) in
/--
todo: this is a notion that we "made up". we should think if it's in the most reasonable form,
but for now it's assuming what we need.

it isolates some properties of partially ordered additive groups who are lattices that still work in
monoids.

The importance of this is that we want some properties to hold for all solid norms.

todo: what about definition 3.5.1 in BL ("is of class")? a different possible approach would be to
quantify over all spaces that are of the class of the couple.
-/
@[blueprint]
class Abs.IsModulus [Preorder β] [Abs β] : Prop where
  /-- subadditivity -/
  abs_add_le (x y : β) : |x + y|ₑ ≤ |x|ₑ + |y|ₑ
  /-- Riez property -/
  exists_decomp {x y₀ y₁ : β} (h : |x|ₑ ≤ |y₀|ₑ + |y₁|ₑ) :
    ∃ x₀ x₁, x = x₀ + x₁ ∧ |x₀|ₑ ≤ |y₀|ₑ ∧ |x₁|ₑ ≤ |y₁|ₑ ∧ |x₀|ₑ ≤ |x|ₑ ∧ |x₁|ₑ ≤ |x|ₑ

section Instances

variable {J : Type*} {γ : J → Type*}

/-- A product carries the pointwise modulus. -/
instance Pi.instAbs [∀ j, Abs (γ j)] : Abs (∀ j, γ j) := ⟨fun f j ↦ |f j|ₑ⟩

@[simp]
lemma Pi.absₑ_apply [∀ j, Abs (γ j)] (f : ∀ j, γ j) (j : J) : |f|ₑ j = |f j|ₑ := rfl

instance Pi.instIsModulus [∀ j, AddCommMonoid (γ j)] [∀ j, Preorder (γ j)] [∀ j, Abs (γ j)]
    [∀ j, Abs.IsModulus (γ j)] : Abs.IsModulus (∀ j, γ j) where
  abs_add_le f g j := Abs.IsModulus.abs_add_le (f j) (g j)
  exists_decomp h := by
    choose u v huv hu hv using fun j ↦ Abs.IsModulus.exists_decomp (h j)
    exact ⟨u, v, funext huv, hu, hv⟩

/-- The usual absolute value of a real number. -/
instance Real.instAbs : Abs ℝ := ⟨fun x ↦ |x|⟩

@[simp, grind =] lemma Real.absₑ_eq (x : ℝ) : |x|ₑ = |x| := rfl

instance Real.instIsModulus : Abs.IsModulus ℝ where
  abs_add_le := abs_add_le
  exists_decomp {a b c} h := by
    use max (min a |b|) (-|b|), a - max (min a |b|) (-|b|), by ring, by grind, by grind

/-- An element of $`[0,∞]` is its own modulus. -/
instance ENNReal.instAbs : Abs ℝ≥0∞ := ⟨id⟩

@[simp] lemma ENNReal.absₑ_eq (x : ℝ≥0∞) : |x|ₑ = x := rfl

instance ENNReal.instIsModulus : Abs.IsModulus ℝ≥0∞ where
  abs_add_le _ _ := le_rfl
  exists_decomp {a b c} h := by
    simp only [ENNReal.absₑ_eq] at h
    refine ⟨min a b, a - min a b, (add_tsub_cancel_of_le (min_le_left ..)).symm,
      min_le_right .., ?_⟩
    simp only [ENNReal.absₑ_eq]
    rcases le_total a b with h₁ | h₁
    · simp [min_eq_left h₁]
    · rw [min_eq_right h₁, tsub_le_iff_right]
      exact h.trans_eq (add_comm ..)

/-- Real-valued functions, with the pointwise absolute value. -/
example {X : Type*} : Abs.IsModulus (X → ℝ) := inferInstance

/-- $`[0,∞]`-valued functions, with the pointwise identity. -/
example {X : Type*} : Abs.IsModulus (X → ℝ≥0∞) := inferInstance

end Instances

variable [Abs β] [Preorder β]

namespace EQuasinorm

class IsSolid (B : EQuasinorm β) : Prop where
  solid {x y : β} : |x|ₑ ≤ |y|ₑ → ‖x‖ₑ[B] ≤ ‖y‖ₑ[B]

variable {A₀ A₁ B : EQuasinorm β} {t : ℝ≥0∞} {x y a b c : β}

/-- A modulus inequality $`|a| ≤ |b| + |c|` transfers to any solid quasinorm, up to its
subadditivity constant. -/
@[blueprint]
lemma IsSolid.enorm_le_mul_of_abs_le [Abs.IsModulus β] [B.IsSolid] (h : |a|ₑ ≤ |b|ₑ + |c|ₑ) :
    ‖a‖ₑ[B] ≤ B.C * (‖b‖ₑ[B] + ‖c‖ₑ[B]) := by
  obtain ⟨u, v, huv, hu, hv⟩ := Abs.IsModulus.exists_decomp h
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
lemma kNorm_le_kNorm_of_abs_le [Abs.IsModulus β] [A₀.IsSolid] [A₁.IsSolid]
    (h : |x|ₑ ≤ |y|ₑ) (t : ℝ≥0∞) : A₀.kNorm A₁ t x ≤ A₀.kNorm A₁ t y := by
  refine le_iInf₂ fun a ha ↦ ?_
  have hy : |y|ₑ ≤ |a.1|ₑ + |a.2|ₑ := ha ▸ Abs.IsModulus.abs_add_le a.1 a.2
  obtain ⟨x₀, x₁, hx, h₀, h₁⟩ := Abs.IsModulus.exists_decomp (h.trans hy)
  refine (kNorm_le_of_decomp hx t).trans (add_le_add (IsSolid.solid h₀) ?_)
  gcongr
  exact IsSolid.solid h₁

/-- The sum of a couple of solid quasinorms, with the norm $`K(t,-)`, is solid. -/
instance IsSolid.skewedSup [Abs.IsModulus β] [A₀.IsSolid] [A₁.IsSolid] :
    (A₀.skewedSup A₁ t).IsSolid where
  solid h := kNorm_le_kNorm_of_abs_le h t

instance IsSolid.sup [Abs.IsModulus β] [A₀.IsSolid] [A₁.IsSolid] : (A₀ ⊔ A₁).IsSolid :=
  IsSolid.skewedSup

end EQuasinorm

namespace ESeminorm

variable {A : ESeminorm β} {a b c : β}

/-- {lit}`EQuasinorm.IsSolid.enorm_le_mul_of_abs_le` for an {lit}`ESeminorm`: since $`C = 1`,
the inequality is genuine subadditivity. -/
@[blueprint]
lemma enorm_le_of_abs_le [Abs.IsModulus β] [A.toEQuasinorm.IsSolid] (h : |a|ₑ ≤ |b|ₑ + |c|ₑ) :
    ‖a‖ₑ[A] ≤ ‖b‖ₑ[A] + ‖c‖ₑ[A] := by
  simpa using EQuasinorm.IsSolid.enorm_le_mul_of_abs_le (B := A.toEQuasinorm) h

end ESeminorm

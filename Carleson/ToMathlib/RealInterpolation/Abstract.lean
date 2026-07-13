import Carleson.ToMathlib.RealInterpolation.Minkowski

/-!
Following
 *Interpolation Spaces, An Introduction* by  Jöran Bergh , Jörgen Löfström.
-/

noncomputable section

open ENNReal Set MeasureTheory
open scoped NNReal

variable {𝓐 : Type*} [AddMonoid 𝓐] {𝓑 : Type*} [AddMonoid 𝓑]

variable (𝓐) in
structure QuasiENorm where
  protected enorm : ENorm 𝓐
  protected C : ℝ≥0∞
  protected C_lt : C < ∞ := by finiteness
  protected enorm_zero : ‖(0 : 𝓐)‖ₑ = 0
  enorm_add_le_mul : ∀ x y : 𝓐, ‖x + y‖ₑ ≤ C * (‖x‖ₑ + ‖y‖ₑ)


-- Feel free to assume `θ ∈ Icc 0 1`, `1 ≤ q` and `q < ∞ → θ ∈ Ioo 0 1` whenever needed
variable {A A₀ A₁ A' A₀' A₁' : QuasiENorm 𝓐} {t s : ℝ≥0∞} {x y z : 𝓐} {θ : ℝ} {q : ℝ≥0∞}
  {B B₀ B₁ B' B₀' B₁' : QuasiENorm 𝓑} {C D : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞}

namespace QuasiENorm

attribute [simp] QuasiENorm.enorm_zero
attribute [aesop (rule_sets := [finiteness]) safe] QuasiENorm.C_lt max_lt

-- Todo: we need a delaborator for this.

notation "‖" e "‖ₑ[" A "]" => @enorm _ (QuasiENorm.enorm A) e

-- todo: make constant explicit
instance : LE (QuasiENorm 𝓐) :=
  ⟨fun A₀ A₁ => ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ x, ‖x‖ₑ[A₁] ≤ C * ‖x‖ₑ[A₀]⟩

instance : Preorder (QuasiENorm 𝓐) where
  le_refl A := ⟨1, by simp⟩
  le_trans A₀ A₁ A₂ := by
    intro ⟨C, h1C, h2C⟩ ⟨D, h1D, h2D⟩
    refine ⟨D * C, mul_ne_top h1D h1C, fun x ↦ ?_⟩
    calc ‖x‖ₑ[A₂] ≤ D * ‖x‖ₑ[A₁] := h2D x
      _ ≤ D * C * ‖x‖ₑ[A₀] := by
        rw [mul_assoc]
        gcongr
        apply h2C

-- the equivalence relation stating that two norms are equivalent
instance : Setoid (QuasiENorm 𝓐) := AntisymmRel.setoid _ (· ≤ ·)

-- example (h : A₀ ≈ A₁) : A₀ ≤ A₁ := h.le
-- example (h : A₀ ≈ A₁) : A₁ ≤ A₀ := h.ge

-- Two spaces are compatible if they can both be embedded into the same topological additive monoid.
-- Hopefully this is vacuous in our reformulation.
-- def Compatible (A₀ A₁ : QuasiENorm 𝓐) : Prop :=

/-- the submonoid of finite elements -/
def finiteElements (A : QuasiENorm 𝓐) : AddSubmonoid 𝓐 where
  carrier := { x | ‖x‖ₑ[A] < ∞ }
  zero_mem' := by simp
  add_mem' {x y} hx hy := by
    calc
      ‖x + y‖ₑ[A] ≤ A.C * (‖x‖ₑ[A] + ‖y‖ₑ[A]) := by apply enorm_add_le_mul
      _ < ∞ := by finiteness

example : ‖x + y‖ₑ[A] ≤ A.C * (‖x‖ₑ[A] + ‖y‖ₑ[A]) :=
  A.enorm_add_le_mul x y

instance : Min (QuasiENorm 𝓐) :=
  ⟨fun A₀ A₁ => {
    enorm := ⟨fun x ↦ max ‖x‖ₑ[A₀] ‖x‖ₑ[A₁]⟩
    C := max A₀.C A₁.C
    enorm_zero := by simp_rw [QuasiENorm.enorm_zero, max_self]
    enorm_add_le_mul x y :=
      calc
        max ‖x + y‖ₑ[A₀] ‖x + y‖ₑ[A₁] ≤
          max (A₀.C * (‖x‖ₑ[A₀] + ‖y‖ₑ[A₀])) (A₁.C * (‖x‖ₑ[A₁] + ‖y‖ₑ[A₁])) := by
            gcongr <;> apply enorm_add_le_mul
        _ ≤ max A₀.C A₁.C * max (‖x‖ₑ[A₀] + ‖y‖ₑ[A₀]) (‖x‖ₑ[A₁] + ‖y‖ₑ[A₁]) :=
            max_mul_mul_le_max_mul_max'
        _ ≤ max A₀.C A₁.C * (max ‖x‖ₑ[A₀] ‖x‖ₑ[A₁] + max ‖y‖ₑ[A₀] ‖y‖ₑ[A₁]) := by
            gcongr
            exact max_add_add_le_max_add_max }⟩

lemma inf_mono (h₀ : A₀ ≤ A₀') (h₁ : A₁ ≤ A₁') : A₀ ⊓ A₁ ≤ A₀' ⊓ A₁' := by
  sorry

lemma inf_equiv_inf (h₀ : A₀ ≈ A₀') (h₁ : A₁ ≈ A₁') : A₀ ⊓ A₁ ≈ A₀' ⊓ A₁' :=
  ⟨inf_mono h₀.le h₁.le, inf_mono h₀.ge h₁.ge⟩

/-- `K(t,x)` in Section 3.1. For `t = 1` this is the norm of `A₀ + A₁`. -/
def addNorm (A₀ A₁ : QuasiENorm 𝓐) (t : ℝ≥0∞) (x : 𝓐) : ℝ≥0∞ :=
  ⨅ (x₀ : 𝓐) (x₁ : 𝓐) (_h : x₀ + x₁ = x), ‖x₀‖ₑ[A₀] + t * ‖x₁‖ₑ[A₁]

/-- The addition `A₀ + A₁` equipped with the norm `K(t,-)` -/
def skewedAdd (A₀ A₁ : QuasiENorm 𝓐) (t : ℝ≥0∞) : QuasiENorm 𝓐 where
  enorm := ⟨addNorm A₀ A₁ t⟩
  C := A₀.C + A₁.C -- maybe
  enorm_zero := by
    simp_rw [← nonpos_iff_eq_zero]
    apply iInf₂_le_of_le 0 0
    simp
  enorm_add_le_mul x y := by
    sorry

lemma skewedAdd_mono (h₀ : A₀ ≤ A₀') (h₁ : A₁ ≤ A₁') :
    skewedAdd A₀ A₁ t ≤ skewedAdd A₀' A₁' t := by
  sorry

lemma skewedAdd_equiv_skewedAdd (h₀ : A₀ ≈ A₀') (h₁ : A₁ ≈ A₁') :
    skewedAdd A₀ A₁ t ≈ skewedAdd A₀' A₁' t :=
  ⟨skewedAdd_mono h₀.le h₁.le, skewedAdd_mono h₀.ge h₁.ge⟩

instance : Add (QuasiENorm 𝓐) :=
  ⟨fun A₀ A₁ ↦ A₀.skewedAdd A₁ 1⟩

lemma add_mono (h₀ : A₀ ≤ A₀') (h₁ : A₁ ≤ A₁') : A₀ + A₁ ≤ A₀' + A₁' :=
  skewedAdd_mono h₀ h₁

lemma add_equiv_add (h₀ : A₀ ≈ A₀') (h₁ : A₁ ≈ A₁') : A₀ + A₁ ≈ A₀' + A₁' :=
  skewedAdd_equiv_skewedAdd h₀ h₁

-- Part of Lemma 3.1.1
-- assume t ≠ ∞ if needed
lemma monotone_addNorm (hx : ‖x‖ₑ[A₀ + A₁] < ∞) : Monotone (addNorm A₀ A₁ · x) := by
  sorry

-- Part of Lemma 3.1.1 (if convenient: make the scalar ring `ℝ≥0`)
-- assume t ≠ ∞ if needed
lemma concave_addNorm (hx : ‖x‖ₑ[A₀ + A₁] < ∞) : ConcaveOn ℝ≥0∞ univ (addNorm A₀ A₁ · x) := by
  sorry

-- Part of Lemma 3.1.1
-- assume s ≠ 0, s ≠ ∞, t ≠ ∞ if needed
-- probably this is more useful if reformulated without division
lemma addNorm_le_mul (hx : ‖x‖ₑ[A₀ + A₁] < ∞) :
    addNorm A₀ A₁ t x ≤ max 1 (t / s) * addNorm A₀ A₁ s x := by

  sorry

/-- The functional `Φ` in Section 3.1. Todo: better name. Todo: generalize type of `f`?
If we put a σ-algebra + measure on `ℝ≥0∞` we can get rid of the `ofReal`s. -/
def functional (θ : ℝ) (q : ℝ≥0∞) (f : ℝ≥0∞ → ℝ≥0∞) : ℝ≥0∞ :=
  eLpNorm ((Ioi 0).indicator fun t ↦ ENNReal.ofReal t ^ (- θ) * f (ENNReal.ofReal t)) q
    (volume.withDensity fun t ↦ (ENNReal.ofReal t)⁻¹)

/- ‖-‖_{θ, q, K} in Section 3.1. -/
def KNorm (A₀ A₁ : QuasiENorm 𝓐) (θ : ℝ) (q : ℝ≥0∞) (x : 𝓐) : ℝ≥0∞ :=
  functional θ q (addNorm A₀ A₁ · x)

/-- The space K_{θ,q}(\bar{A}) in Section 3.1.
In the book, this is defined to only be submonoid of the elements with finite norm.
We could do that as well, but actually, since we allow for infinite norms, we can take all elements.
-/
def KMethod (A₀ A₁ : QuasiENorm 𝓐) (θ : ℝ) (q : ℝ≥0∞) : QuasiENorm 𝓐 where
  enorm := ⟨KNorm A₀ A₁ θ q⟩
  C := sorry
  C_lt := sorry
  enorm_zero := sorry
  enorm_add_le_mul := sorry

structure IsIntermediateSpace (A A₀ A₁ : QuasiENorm 𝓐) : Prop where
  inf_le : A₀ ⊓ A₁ ≤ A
  le_add : A ≤ A₀ + A₁

namespace IsIntermediateSpace

protected lemma equiv (hI : IsIntermediateSpace A A₀ A₁) (h : A ≈ A') (h₀ : A₀ ≈ A₀') (h₁ : A₁ ≈ A₁') :
  IsIntermediateSpace A' A₀' A₁' where
    inf_le := inf_equiv_inf h₀ h₁ |>.ge.trans hI.inf_le |>.trans h.le
    le_add := h.ge.trans hI.le_add |>.trans <| add_equiv_add h₀ h₁ |>.le

end IsIntermediateSpace

-- Todo: find better name?
-- question: how do we get real interpolation with a.e.-subadditivity:
-- probably this works if we apply it to L^p-spaces (i.e. quotients of functions)
structure IsSubadditiveOn (T : 𝓐 → 𝓑) (A : QuasiENorm 𝓐) (B : QuasiENorm 𝓑) (C D : ℝ≥0∞) :
    Prop where
  bounded : ∀ x, ‖T x‖ₑ[B] ≤ C * ‖x‖ₑ[A]
  subadditive : ∀ x y, ‖T (x + y)‖ₑ[B] ≤ D * (‖T x‖ₑ[B] + ‖T y‖ₑ[B])

-- `C = ‖T‖_{A, B}`
-- perhaps we don't have to let `C` and `D` depend on all other parameters.
structure AreInterpolationSpaces (A A₀ A₁ : QuasiENorm 𝓐) (B B₀ B₁ : QuasiENorm 𝓑)
    (C D : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞) : Prop where
  isIntermediateSpace_fst : IsIntermediateSpace A A₀ A₁
  isIntermediateSpace_snd : IsIntermediateSpace B B₀ B₁
  prop : ∀ C₀ D₀ C₁ D₁ (T : 𝓐 → 𝓑), IsSubadditiveOn T A₀ B₀ C₀ D₀ → IsSubadditiveOn T A₁ B₁ C₁ D₁ →
    IsSubadditiveOn T A B (C C₀ D₀ C₁ D₁) (D C₀ D₀ C₁ D₁)

/-- `T` is of exponent `θ` w.r.t. constant `E` if `C ≤ E * C₀ ^ (1 - θ) * C₁ ^ θ` -/
def IsOfExponent (C : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞) (θ : ℝ) (E : ℝ≥0∞) : Prop :=
  ∀ C₀ D₀ C₁ D₁, C C₀ D₀ C₁ D₁ ≤ E * C₀ ^ (1 - θ) * C₁ ^ θ

/-- `T` is exact of exponent `θ` -/
def IsExactOfExponent (C : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞) (θ : ℝ) : Prop :=
  IsOfExponent C θ 1

/-- `T` is exact -/
def IsExact (C : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞) : Prop :=
  ∀ C₀ D₀ C₁ D₁, C C₀ D₀ C₁ D₁ ≤ max C₀ C₁


namespace AreInterpolationSpaces

protected lemma equiv (hI : AreInterpolationSpaces A A₀ A₁ B B₀ B₁ C D)
    (h : A ≈ A') (h₀ : A₀ ≈ A₀') (h₁ : A₁ ≈ A₁') (h' : B ≈ B') (h₀' : B₀ ≈ B₀') (h₁' : B₁ ≈ B₁') :
  AreInterpolationSpaces A' A₀' A₁' B' B₀' B₁' C D where
    isIntermediateSpace_fst := hI.isIntermediateSpace_fst.equiv h h₀ h₁
    isIntermediateSpace_snd := hI.isIntermediateSpace_snd.equiv h' h₀' h₁'
    prop := sorry

end AreInterpolationSpaces


/-- The boundedness constant for the K-method. -/
def C_KMethod (θ : ℝ) (q C₀ D₀ C₁ D₁ : ℝ≥0∞) : ℝ≥0∞ := sorry

/-- The subadditivity constant for the K-method. -/
def D_KMethod (θ : ℝ) (q C₀ D₀ C₁ D₁ : ℝ≥0∞) : ℝ≥0∞ := sorry

/-- Theorem 3.1.2: The K-method in an interpolation functor. -/
lemma areInterpolationSpaces_kmethod : AreInterpolationSpaces
    (KMethod A₀ A₁ θ q) A₀ A₁ (KMethod B₀ B₁ θ q) B₀ B₁ (C_KMethod θ q) (D_KMethod θ q) := by
  sorry

/-- Part of Theorem 3.1.2 -/
lemma isExactOfExponent_kmethod : IsExactOfExponent (C_KMethod θ q) θ := by
  sorry

/-- The constant of inequality (6). -/
def γKMethod' (θ : ℝ) (q : ℝ≥0∞) : ℝ≥0∞ := sorry

/-- Part of Theorem 3.1.2 -/
lemma addNorm_le_knorm (hx : ‖x‖ₑ[A₀ + A₁] < ∞) :
    addNorm A₀ A₁ t x ≤ γKMethod' θ q * t ^ θ * KNorm A₀ A₁ θ q x  := by
  sorry

-- Todo: ⊓, +, IsIntermediateSpace, AreInterpolationSpaces respect ≈

/-- Theorem 3.1.2: If intermediate spaces are equivalent to the ones obtained by the K-method,
then this gives rise to an interpolation space. -/
lemma areInterpolationSpaces_of_le_kmethod
    (hA : A ≈ KMethod A₀ A₁ θ q) (hB : B ≈ KMethod B₀ B₁ θ q) :
    AreInterpolationSpaces A A₀ A₁ B B₀ B₁ (C_KMethod θ q) (D_KMethod θ q) :=
  areInterpolationSpaces_kmethod.equiv hA.symm .rfl .rfl hB.symm .rfl .rfl


end QuasiENorm

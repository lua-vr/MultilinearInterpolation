module

public import Mathlib.Analysis.Fourier.AddCircle

/-! # Key definitions and setup for the Carleson project

This file contains the basic definitions to state the main theorems from the Carleson formalization
project: Theorem 1.0.1 (classical Carleson), Theorem 1.1.1 (metric space Carleson) and
Theorem 1.1.2 (linearised metric Carleson).

These are intentionally put in a very low-level file to enable running the comparator tool.

## Main definitions

- `MeasureTheory.DoublingMeasure`: A metric space with a measure with some nice propreties,
including a doubling condition. This is called a "doubling metric measure space" in the blueprint.
- `FunctionDistances`: class stating that continuous functions have distances associated to
every ball.
- `IsOneSidedKernel K` states that `K` is a one-sided Calderon-Zygmund kernel.
- `KernelProofData`: Data common through most of chapters 2-7. These contain the minimal axioms
for `kernel-summand`'s proof.

-/

@[expose] public noncomputable section

open MeasureTheory Measure Metric Complex Set ENNReal
open scoped NNReal

open Real in
/-- The Nᵗʰ partial Fourier sum of `f : ℝ → ℂ` for `N : ℕ`. -/
def partialFourierSum (N : ℕ) (f : ℝ → ℂ) (x : ℝ) : ℂ := ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
    fourierCoeffOn Real.two_pi_pos f n * fourier n (x : AddCircle (2 * π))

/- Basic definitions not specific to this project: they will be added to Mathlib soon -/
section BasicDefinitions

variable {X E : Type*}

/-- The "volume function" `V`. Preferably use `vol` instead. -/
protected def Real.vol [PseudoMetricSpace X] [MeasureSpace X] (x y : X) : ℝ :=
  volume.real (ball x (dist x y))

def Set.Annulus.oo [PseudoMetricSpace X] (x : X) (r R : ℝ) := {y | dist x y ∈ Ioo r R}

def Set.EAnnulus.oo [PseudoMetricSpace X] (x : X) (r R : ℝ≥0∞) := {y | edist x y ∈ Ioo r R}

/-- The inhomogeneous Lipschitz norm on a ball. -/
def iLipENorm {𝕜 X : Type*} [NormedField 𝕜] [PseudoMetricSpace X]
  (φ : X → 𝕜) (x₀ : X) (R : ℝ) : ℝ≥0∞ :=
  (⨆ x ∈ ball x₀ R, ‖φ x‖ₑ) +
  ENNReal.ofReal R * ⨆ (x ∈ ball x₀ R) (y ∈ ball x₀ R) (_ : x ≠ y), ‖φ x - φ y‖ₑ / edist x y

variable {𝕜 X : Type*} {A : ℕ} [_root_.RCLike 𝕜] [PseudoMetricSpace X] in
/-- The local oscillation of two functions w.r.t. a set `E`. This is `d_E` in the blueprint. -/
def localOscillation (E : Set X) (f g : C(X, 𝕜)) : ℝ≥0∞ :=
  ⨆ z ∈ E ×ˢ E, ENNReal.ofReal ‖f z.1 - g z.1 - f z.2 + g z.2‖

variable {X E : Type*} [MeasurableSpace X] {f g : X → E}
  {μ : Measure X} [TopologicalSpace E] [ENorm E] [Zero E] in
/-- Bounded measurable function $g$ on $X$ supported on a set of finite measure -/
@[fun_prop]
structure BoundedFiniteSupport (f : X → E) (μ : Measure X := by volume_tac) : Prop where
  memLp_top : MemLp f ∞ μ
  measure_support_lt : μ (Function.support f) < ∞

/-- A weaker version of `HasStrongType`. This is the same as `HasStrongType` if `T` is continuous
w.r.t. the L^2 norm, but weaker in general. -/
def MeasureTheory.HasBoundedStrongType
    {ε₁ ε₂ : Type*} [ENorm ε₁] [ENorm ε₂] [TopologicalSpace ε₁] [TopologicalSpace ε₂] [Zero ε₁]
    {α α' : Type*} {_x : MeasurableSpace α} {_x' : MeasurableSpace α'}
    (T : (α → ε₁) → (α' → ε₂))
    (p p' : ℝ≥0∞) (μ : Measure α) (ν : Measure α') (c : ℝ≥0∞) : Prop :=
  ∀ f : α → ε₁, BoundedFiniteSupport f μ →
    AEStronglyMeasurable (T f) ν ∧ eLpNorm (T f) p' ν ≤ c * eLpNorm f p μ

/-- A doubling measure is a measure on a metric space with the condition that doubling
the radius of a ball only increases the volume by a constant factor, independent of the ball. -/
class MeasureTheory.Measure.IsDoubling {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    (μ : Measure X) (A : outParam ℝ≥0) : Prop where
  measure_ball_two_le_same : ∀ (x : X) r, μ (ball x (2 * r)) ≤ A * μ (ball x r)
export IsDoubling (measure_ball_two_le_same)

/-- A metric space with a measure with some nice propreties, including a doubling condition.
This is called a "doubling metric measure space" in the blueprint.
`A` will usually be `2 ^ a`. -/
class MeasureTheory.DoublingMeasure (X : Type*) (A : outParam ℝ≥0) [PseudoMetricSpace X] extends
    CompleteSpace X, LocallyCompactSpace X,
    MeasureSpace X, BorelSpace X,
    IsLocallyFiniteMeasure (volume : Measure X),
    Measure.IsDoubling (volume : Measure X) A, NeZero (volume : Measure X) where

end BasicDefinitions

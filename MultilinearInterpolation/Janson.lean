import MultilinearInterpolation.Basic

noncomputable section

/-!
Following
 *On interpolation of multi-linear operators* by Svante Janson.
-/

noncomputable section

open ENNReal Set MeasureTheory
open scoped NNReal

open QuasiENorm

variable (k : ℕ) (A : Fin k → Couple) (B : Couple)

def strangeNorm (θ r : ℝ) (q : ℝ≥0) : QuasiENorm B.carrier where
  enorm :=
    sInf {
      ‖ (fun (n : Fin (2 * N)) ↦ r^(- θ * (n - N)) * minNorm B.fst B.snd : WithLp _ _) ‖
            | N}
  C := sorry
  C_lt := sorry
  enorm_zero := sorry
  enorm_add_le_mul := sorry



lemma interpolation_norm_equiv (r : ℝ) (hr : 0 < r ∧ r ≠ 1) :
  A

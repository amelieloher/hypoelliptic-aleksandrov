module

public import HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamilyLocality

/-!
# Squared L2 energy of a finite parabolic weak-derivative family
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamily

open MeasureTheory
open scoped BigOperators ENNReal

/-- The finite sum of squared restricted `L²` norms of all selected
derivatives. -/
noncomputable def squaredL2Norm
    {d L : ℕ} {U : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}
    (F : ParabolicWeakDerivativeFamily d L U u) : ℝ :=
  ∑ beta : ParabolicDerivativeIndex d L,
    (ENNReal.toReal
      (eLpNorm (F.representative beta) 2 (timeVelocityVolumeOn U))) ^ 2

/-- The squared finite-family `L²` norm is nonnegative. -/
theorem squaredL2Norm_nonneg
    {d L : ℕ} {U : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}
    (F : ParabolicWeakDerivativeFamily d L U u) :
    0 ≤ squaredL2Norm F := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Each squared component norm is bounded by the squared finite-family
norm. -/
theorem component_sq_le_squaredL2Norm
    {d L : ℕ} {U : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}
    (F : ParabolicWeakDerivativeFamily d L U u)
    (beta : ParabolicDerivativeIndex d L) :
    (ENNReal.toReal
      (eLpNorm (F.representative beta) 2 (timeVelocityVolumeOn U))) ^ 2 ≤
      squaredL2Norm F := by
  unfold squaredL2Norm
  exact Finset.single_le_sum (fun gamma _ => sq_nonneg
    (ENNReal.toReal
      (eLpNorm (F.representative gamma) 2 (timeVelocityVolumeOn U))))
    (Finset.mem_univ beta)

/-- The literal representative formula agrees with the squared norm of any
`L²` quotient built from any proof certificate. -/
theorem component_sq_eq_norm_toLp_sq
    {d L : ℕ} {U : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}
    (F : ParabolicWeakDerivativeFamily d L U u)
    (beta : ParabolicDerivativeIndex d L)
    (h : ParabolicMemLpOn U 2 (F.representative beta)) :
    (ENNReal.toReal
      (eLpNorm (F.representative beta) 2 (timeVelocityVolumeOn U))) ^ 2 =
      ‖h.toLp (F.representative beta)‖ ^ 2 := by
  rw [Lp.norm_toLp]

/-- The literal finite-family formula agrees with the sum of the squared
`Lp` norms obtained from the family's stored membership certificates. -/
theorem squaredL2Norm_eq_sum_norm_toLp_sq
    {d L : ℕ} {U : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}
    (F : ParabolicWeakDerivativeFamily d L U u) :
    squaredL2Norm F =
      ∑ beta : ParabolicDerivativeIndex d L,
        ‖(F.memLp beta).toLp (F.representative beta)‖ ^ 2 := by
  unfold squaredL2Norm
  apply Finset.sum_congr rfl
  intro beta _
  exact component_sq_eq_norm_toLp_sq F beta (F.memLp beta)

/-- Restricting a family to a smaller raw carrier cannot increase its
squared finite-family `L²` norm. -/
theorem squaredL2Norm_restrict_le
    {d L : ℕ} {U V : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}
    (F : ParabolicWeakDerivativeFamily d L U u) (hVU : V ⊆ U) :
    squaredL2Norm (F.restrict hVU) ≤ squaredL2Norm F := by
  unfold squaredL2Norm
  refine Finset.sum_le_sum fun beta _ => ?_
  have hnorm :
      ENNReal.toReal
          (eLpNorm (F.representative beta) 2 (timeVelocityVolumeOn V)) ≤
        ENNReal.toReal
          (eLpNorm (F.representative beta) 2 (timeVelocityVolumeOn U)) := by
    exact ENNReal.toReal_mono (F.memLp beta).eLpNorm_ne_top
      (eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hVU))
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg hnorm 2

end HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamily

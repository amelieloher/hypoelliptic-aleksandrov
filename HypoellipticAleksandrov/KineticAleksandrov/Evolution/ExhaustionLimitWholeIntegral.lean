module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitWholeUniform
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCauchyParameters
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Integral convergence for actual expanding-ball solutions -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov Set Filter MeasureTheory
open scoped Topology MatrixOrder

section Data

variable {n : ℕ} {lam Lam Lb : ℝ} {B : FullKineticCoefficient n}
variable {b : PDE.Vec n → PDE.Vec n} (hlam : 0 < lam)
variable (hB : HasEverywhereLoewnerBounds lam Lam B) (hb : HasEuclideanLipschitzDrift Lb b)
variable {ε τ α S0 C : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C)
variable (F : BoundedBorel (EvolutionAmbientState n)) (hFC : ∀ q, |F q| ≤ C)
variable (r : ℕ → ℝ) (hrlim : Tendsto r atTop atTop) (v : ℕ → KineticPoint n → ℝ)
variable (hv : ∀ j, IsClassicalViscousTerminalSolution (PDE.euclideanBall 0 (r j))
  (fun _ => 0) B b ε τ F (v j))
include hlam hB hb hε hε1 hC hFC hrlim hv

/-- Integration against a continuous test on a fixed bounded whole-space cylinder
commutes with the actual expanding-ball limit. -/
theorem tendsto_setIntegral_mul_wholeSpace_ball_solutions
    (φ : KineticPoint n → ℝ) (hφ : Continuous φ) :
    Tendsto (fun j => ∫ p in movingClosedSlab univ (fun _ => 0) α τ ∩
      {p | radialSq p ≤ S0 ^ 2}, v j p * φ p) atTop
      (𝓝 (∫ p in movingClosedSlab univ (fun _ => 0) α τ ∩ {p | radialSq p ≤ S0 ^ 2},
        limUnder atTop (fun j => v j p) * φ p)) := by
  let K := movingClosedSlab univ (fun _ : ℝ => (0 : PDE.Vec n)) α τ ∩
    {p | radialSq p ≤ S0 ^ 2}
  have hK : IsCompact K := isCompact_movingClosedSlab_inter continuous_const α τ S0
  have hU := (tendstoUniformlyOn_wholeSpace_ball_solutions (α := α) (S0 := S0)
    hlam hB hb hε hε1 hC F hFC r hrlim v hv).1
  have hnear : ∀ᶠ j : ℕ in atTop, |S0| < r j :=
    hrlim.eventually (eventually_gt_atTop |S0|)
  have hclosed (j : ℕ) (hj : |S0| < r j) :
      K ⊆ evolutionPastClosedCylinder (PDE.euclideanBall 0 (r j)) (fun _ => 0) τ :=
    fun p hp => ⟨hp.1.2.1, subset_closure (mem_movingBall_of_radialSq_le
      (abs_nonneg S0) hj (by simpa only [sq_abs] using (show radialSq p ≤ S0 ^ 2 from hp.2)))⟩
  apply tendsto_integral_filter_of_dominated_convergence (fun p => C * |φ p|)
  · exact hnear.mono fun j hj => ((hv j).2.1.mono (hclosed j hj) |>.mul
      hφ.continuousOn).aestronglyMeasurable hK.measurableSet
  · refine hnear.mono fun j hj => ?_
    filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
    have hbnd := classical_abs_le_const (PDE.isOpen_euclideanBall 0 (r j)) continuous_const
      hlam hB hb hε hε1 (hv j) hFC p (hclosed j hj hp)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hbnd (abs_nonneg _)
  · exact (continuous_const.mul hφ.abs).continuousOn.integrableOn_compact hK
  · filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
    exact (hU.tendsto_at hp).mul tendsto_const_nhds

end Data

end HypoellipticAleksandrov.KineticAleksandrov

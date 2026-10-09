module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionGreenBarrier
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Spatial exponential supersolutions for source localization -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Parabolic
open SectionTwo Evolution

/-- A proper scalar spatial weight. -/
def reconstructionSpatialWeight (x : ℝ) : ℝ := Real.exp x + Real.exp (-x)

/-- Native spatial supersolution with a backward exponential time factor. -/
def reconstructionSpatialBarrier (B T : ℝ) (p : Point) : ℝ :=
  Real.exp (B * (T - p.time)) * reconstructionSpatialWeight (p.velocity 0)

/-- The spatial weight is globally smooth. -/
theorem reconstructionSpatialWeight_smooth :
    ContDiff ℝ (⊤ : ℕ∞) reconstructionSpatialWeight :=
  contDiff_id.exp.add contDiff_id.neg.exp

/-- The spatial barrier is globally smooth in native product coordinates. -/
theorem reconstructionSpatialBarrier_smooth (B T : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (rawLift (reconstructionSpatialBarrier B T)) :=
  (contDiff_const.mul (contDiff_const.sub contDiff_fst)).exp.mul
    (reconstructionSpatialWeight_smooth.comp
      ((contDiff_apply ℝ ℝ (0 : Fin 1)).comp contDiff_snd.snd))

/-- The spatial barrier has the required slice regularity. -/
theorem reconstructionSpatialBarrier_regular (B T : ℝ) (p : Point) :
    IsSliceRegularAt (reconstructionSpatialBarrier B T) p :=
  IsSliceRegularAt.of_contDiffAt
    ((reconstructionSpatialBarrier_smooth B T).of_le (by simp)).contDiffAt

/-- The spatial barrier is continuous. -/
theorem reconstructionSpatialBarrier_continuous (B T : ℝ) :
    Continuous (reconstructionSpatialBarrier B T) :=
  (reconstructionSpatialBarrier_smooth B T).continuous.comp
    (KineticPoint.homeomorphProd 1).continuous

private theorem spatial_weight_deriv (x : ℝ) :
    HasDerivAt reconstructionSpatialWeight (Real.exp x - Real.exp (-x)) x := by
  simpa [reconstructionSpatialWeight] using!
    (hasDerivAt_id x).exp.add ((hasDerivAt_id x).neg.exp)

/-- The operator of the spatial barrier uses only bounded transport speed. -/
theorem reconstructionSpatialBarrier_operator (a : ℝ → ℝ → ℝ) (B T : ℝ) (p : Point) :
    transportedForwardOperator (evolutionCoefficient a) (identityDrift 1)
      (reconstructionSpatialBarrier B T) p =
        Real.exp (B * (T - p.time)) *
          (-B * reconstructionSpatialWeight (p.velocity 0) +
            p.position 0 * (Real.exp (p.velocity 0) - Real.exp (-p.velocity 0))) := by
  have ht : kineticTimeDerivative (reconstructionSpatialBarrier B T) p =
      (-B * Real.exp (B * (T - p.time))) * reconstructionSpatialWeight (p.velocity 0) := by
    have h := (((hasDerivAt_const p.time T).sub (hasDerivAt_id p.time)).const_mul B).exp
    have hh := h.mul_const (reconstructionSpatialWeight (p.velocity 0))
    change HasDerivAt (fun t => reconstructionSpatialBarrier B T
      ⟨t, p.position, p.velocity⟩) _ p.time at hh
    rw [kineticTimeDerivative, hh.deriv]
    simp only [Pi.sub_apply, id_eq, zero_sub]
    ring
  have hg : kineticVelocityGradient (reconstructionSpatialBarrier B T) p =
      fun _ => Real.exp (B * (T - p.time)) *
        (Real.exp (p.velocity 0) - Real.exp (-p.velocity 0)) := by
    ext i
    have h := ((spatial_weight_deriv (p.velocity 0)).const_mul
      (Real.exp (B * (T - p.time)))).comp_hasFDerivAt p.velocity
        (hasFDerivAt_apply (𝕜 := ℝ) 0 p.velocity)
    change fderiv ℝ (fun z : PDE.Vec 1 => reconstructionSpatialBarrier B T
      ⟨p.time, p.position, z⟩) p.velocity (PDE.basisVec i) = _
    have hd : fderiv ℝ (fun z : PDE.Vec 1 => reconstructionSpatialBarrier B T
        ⟨p.time, p.position, z⟩) p.velocity =
        (Real.exp (B * (T - p.time)) *
          (Real.exp (p.velocity 0) - Real.exp (-p.velocity 0))) •
            ContinuousLinearMap.proj 0 := by
      simpa only [Function.comp_def, reconstructionSpatialBarrier] using! h.fderiv
    rw [hd]
    fin_cases i
    simp [PDE.basisVec]
  have hh : diffusedHessian (reconstructionSpatialBarrier B T) p = 0 := by
    rw [diffusedHessian_eq_sliceHessian]
    change sliceHessian (fun _ : PDE.Vec 1 =>
      Real.exp (B * (T - p.time)) * reconstructionSpatialWeight (p.velocity 0)) p.position = 0
    exact sliceHessian_const _ p.position
  rw [transportedForwardOperator_apply, ht, hg, hh]
  simp only [fullKineticCoefficientAt, matrixContraction,
    Matrix.zero_apply, PDE.vecDot, Fin.sum_univ_one, identityDrift, id_eq, mul_zero, add_zero]
  ring

/-- The absolute endpoint maximum bounds every velocity in the closed interval. -/
theorem reconstruction_interval_abs_le (H : Interval) {v : ℝ}
    (hv : H.lo ≤ v ∧ v ≤ H.hi) : |v| ≤ max |H.lo| |H.hi| := by
  apply abs_le.mpr
  have hl := neg_abs_le H.lo
  have hh := le_abs_self H.hi
  have hm := le_max_left |H.lo| |H.hi|
  have hn := le_max_right |H.lo| |H.hi|
  constructor <;> linarith only [hl, hh, hm, hn, hv.1, hv.2]

/-- The spatial supersolution absorbs the proper exponential forcing on the native strip. -/
theorem reconstructionSpatialBarrier_operator_le (a : ℝ → ℝ → ℝ) (H : Interval)
    (T : ℝ) (p : Point)
    (hp : p ∈ evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T) :
    transportedForwardOperator (evolutionCoefficient a) (identityDrift 1)
      (reconstructionSpatialBarrier (max |H.lo| |H.hi| + 1) T) p ≤
        -reconstructionSpatialWeight (p.velocity 0) := by
  let V := max |H.lo| |H.hi|
  have hV : 0 ≤ V := (abs_nonneg H.lo).trans (le_max_left _ _)
  have hv : H.lo ≤ p.position 0 ∧ p.position 0 ≤ H.hi := by
    have hi : p.position ∈ intervalDomain H := by
      simpa only [mem_movingDomain_iff, PDE.mem_translateSet_iff_sub_mem, sub_zero] using hp.2
    exact intervalDomain_closure_bounds H (subset_closure hi)
  have hvb := abs_le.mp (reconstruction_interval_abs_le H hv)
  have hplus := mul_le_mul_of_nonneg_right hvb.2 (Real.exp_pos (p.velocity 0)).le
  have hminus := mul_le_mul_of_nonneg_right hvb.1 (Real.exp_pos (-p.velocity 0)).le
  have htr : p.position 0 * (Real.exp (p.velocity 0) - Real.exp (-p.velocity 0)) ≤
      V * reconstructionSpatialWeight (p.velocity 0) := by
    unfold reconstructionSpatialWeight
    nlinarith only [hplus, hminus]
  have hw : 0 ≤ reconstructionSpatialWeight (p.velocity 0) :=
    add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have hex : 1 ≤ Real.exp ((V + 1) * (T - p.time)) :=
    Real.one_le_exp_iff.mpr (mul_nonneg (by linarith only [hV]) (sub_nonneg.mpr hp.1.le))
  rw [reconstructionSpatialBarrier_operator]
  calc
    _ ≤ Real.exp ((V + 1) * (T - p.time)) *
        (-(V + 1) * reconstructionSpatialWeight (p.velocity 0) +
          V * reconstructionSpatialWeight (p.velocity 0)) :=
      mul_le_mul_of_nonneg_left (add_le_add_right htr _) (Real.exp_pos _).le
    _ = -(Real.exp ((V + 1) * (T - p.time)) *
        reconstructionSpatialWeight (p.velocity 0)) := by ring
    _ ≤ -reconstructionSpatialWeight (p.velocity 0) := by
      simpa only [one_mul] using neg_le_neg (mul_le_mul_of_nonneg_right hex hw)

/-- Actual Green occupation has a finite proper spatial exponential moment. -/
theorem reconstruction_green_spatial_weight_bound
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ)) :
    ∫⁻ p, ENNReal.ofReal (reconstructionSpatialWeight (p.position 0))
        ∂stripGreenOfKernel H E.2 T e ≤
      ENNReal.ofReal (Real.exp ((max |H.lo| |H.hi| + 1) * (T - e.1.time)) *
        reconstructionSpatialWeight (e.1.position 0)) := by
  exact reconstruction_green_lintegral_le_barrier hH hlam hLam A H E hE T e
    (fun p => reconstructionSpatialWeight (p.velocity 0))
    (reconstructionSpatialBarrier (max |H.lo| |H.hi| + 1) T)
    (reconstructionSpatialWeight_smooth.comp
      ((contDiff_apply ℝ ℝ (0 : Fin 1)).comp contDiff_snd.snd))
    (fun p => add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    (reconstructionSpatialBarrier_continuous _ _)
    (reconstructionSpatialBarrier_regular _ _)
    (fun p _ => mul_nonneg (Real.exp_pos _).le
      (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le))
    (reconstructionSpatialBarrier_operator_le A.a H T)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

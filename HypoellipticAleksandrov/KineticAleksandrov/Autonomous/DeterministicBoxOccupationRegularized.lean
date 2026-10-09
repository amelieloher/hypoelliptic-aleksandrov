module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsBarrierGreenFatou
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsVelocityBound
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsWeightBasic
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.DeterministicBoxOccupationEndpoint

/-! # Actual regularized Bellman occupation, with every cutoff input discharged -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov MeasureTheory Set Filter
open scoped ENNReal

/-- The actual position-regularized homogeneous Bellman barrier satisfies occupation Green.
No modulus, joint regularity, bounded jet or Green identity is taken as a premise. -/
theorem deterministic_regularized_barrier_green
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam alpha c : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    {phi : Z → ℝ} (h : IsBellmanHomogeneous alpha phi)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hc : 0 < c)
    (hbound : ∀ q ∈ bellmanPuncturedSet, ∀ b ∈ Icc lam Lam,
      c * bellmanGauge q ^ (alpha - 2) ≤ bellmanOperator b phi q)
    (eta : ℝ → ℝ) (heta : IsNonnegativeUnitSmoothMollifier eta)
    (A : SmoothAutonomous lam Lam) (z : Z) (T : NNReal) (hT : 0 < (T : ℝ)) (Y : ℝ) :
    let E := fullSpaceEvolution hH hLE hlam hLam A
    let Phi := positionConvolution eta (bellmanOriginExtension phi)
    ENNReal.ofReal c *
      (∫⁻ q, ENNReal.ofReal (positionConvolution eta
        (fun w => bellmanGauge w ^ (alpha - 2)) (q.1 - Y, q.2))
          ∂physicalOccupationMeasure E z T) ≤
      ENNReal.ofReal ((∫ q, Phi (q.1 - Y, q.2) ∂kernelXV E T z) - Phi (z.1 - Y, z.2)) := by
  let E := fullSpaceEvolution hH hLE hlam hLam A
  let Phi := positionConvolution eta (bellmanOriginExtension phi)
  let f := fun q : Z => Phi (q.1 - Y, q.2)
  let w := fun q : Z => positionConvolution eta
    (fun u => bellmanGauge u ^ (alpha - 2)) (q.1 - Y, q.2)
  have hE := fullSpaceEvolution_spec hH hLE hlam hLam A
  let : IsProbabilityMeasure (kernelXV E T z) := ⟨kernelXV_mass_one hlam A E hE T z⟩
  have hPhi := barrier_position_regularization_joint h ha ha1 eta heta
  have hf : ContDiff ℝ 2 f := hPhi.comp
    ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd)
  obtain ⟨D, hD, hm⟩ := BarrierRegularization.barrier_coordinate_modulus h ha ha1
  have hconvmod := positionConvolution_modulus eta heta (bellmanOriginExtension phi)
    (h.origin_extension_continuous ha) alpha D hD hm
  have hfm (q u : Z) : |f q - f u| ≤
      D * (|q.1 - u.1| ^ (alpha / 3) + |q.2 - u.2| ^ alpha) := by
    have he : q.1 - Y - (u.1 - Y) = q.1 - u.1 := by ring
    simpa only [f, Prod.fst, Prod.snd, he] using hconvmod (q.1 - Y, q.2) (u.1 - Y, u.2)
  obtain ⟨Bv, hBv, hbv⟩ := barrier_smoothed_velocity_bounded h ha ha1 eta heta
  have hfbv (q : Z) : |deriv (fun v => f (q.1, v)) q.2| ≤ Bv := hbv (q.1 - Y, q.2)
  have hw : Measurable w := (positionConvolution_measurable eta heta.1.continuous.measurable
    _ (bellmanGauge_continuous.measurable.pow_const _)).comp
      ((measurable_fst.sub measurable_const).prodMk measurable_snd)
  have hwn (q : Z) : 0 ≤ w q := integral_nonneg
    (fun X => mul_nonneg (heta.2.2.1 _) (Real.rpow_nonneg (bellmanGauge_nonneg _) _))
  have hfbound (q : Z) : c * w q ≤ physicalSpatialOperator A.a f q :=
    (barrier_position_regularization_of_positive_degree ha ha1 h hbound eta heta).2 A Y q
  have hdiff := (deterministic_barrier_endpoint_of_modulus hH hLE hlam hLam alpha D
    ha.le ha1.le hD Phi hPhi.continuous hconvmod A z T Y).1
  have hfi : Integrable f (kernelXV E T z) := by
    convert hdiff.add (integrable_const (Phi (z.1 - Y, z.2))) using 1
    funext q
    simp only [Pi.add_apply, f]
    rw [show q.1 - Y = -Y + q.1 by ring]
    ring
  exact barrier_green_cutoff_removal hH hlam hLam A E hE f hf alpha D Bv
    ha.le ha1.le hD hBv hfm hfbv c hc w hw hwn hfbound Y z T hT hfi

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

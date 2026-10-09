module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceLimits
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripGreenSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripMassComparison
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenPotentialsGeometry
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.JointQueryBorelCutoffSequence

/-! # Quadratic mass by interior smooth exhaustion and bounded comparison -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Filter
open SectionTwo TheoremA
open scoped Topology ENNReal

/-- Finite-horizon quadratic mass follows from actual compact interior sources by exhaustion. -/
theorem stripGreenOfRealization_quadratic_mass
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ)) :
    stripGreenOfKernel H E.2 T e univ ≤
      ENNReal.ofReal ((e.1.velocity 0 - H.lo) * (H.hi - e.1.velocity 0) / (2 * lam)) := by
  let D := evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T
  let U := (KineticPoint.equivProd 1).symm ⁻¹' D
  have hD : IsOpen D := isOpen_duhamelCylinder
    (γ := fun _ => 0) (isOpen_of_isAdmissibleEvolutionDomain (intervalDomain_admissible H))
    continuous_const T
  have hU : IsOpen U := hD.preimage (KineticPoint.homeomorphProd 1).symm.continuous
  obtain ⟨χ, hχ, hb, -, hcover⟩ := exists_increasing_smooth_interior_cutoffs hU
  let g (n : ℕ) : Point → ℝ := χ n ∘ KineticPoint.equivProd 1
  have hgc (n : ℕ) : HasCompactSupport (g n) :=
    (hχ n).2.1.comp_homeomorph (KineticPoint.homeomorphProd 1)
  have hgs (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (rawLift (g n)) := (hχ n).1
  have hgcont (n : ℕ) : Continuous (g n) :=
    (hχ n).1.continuous.comp (KineticPoint.homeomorphProd 1).continuous
  have hgD (n : ℕ) : tsupport (g n) ⊆ D := by
    intro p hp
    have hx := (tsupport_comp_subset_preimage (χ n)
      (KineticPoint.homeomorphProd 1).continuous) hp
    have hu := (hχ n).2.2 hx
    change (KineticPoint.equivProd 1).symm (KineticPoint.equivProd 1 p) ∈ D at hu
    simpa only [Equiv.symm_apply_apply] using hu
  let F (n : ℕ) : BoundedBorel Point :=
    ⟨g n ∘ sectionTwoPoint,
      (hgcont n).measurable.comp (continuous_sectionTwoPoint 1).measurable,
      ⟨1, zero_le_one, fun p => by
        change |χ n (KineticPoint.equivProd 1 (sectionTwoPoint p))| ≤ 1
        rw [abs_of_nonneg (hb n _).1]
        exact (hb n _).2⟩⟩
  have hlim : ∀ᵐ p ∂stripGreenOfKernel H E.2 T e,
      Tendsto (fun n => F n p) atTop (𝓝 ((1 : BoundedBorel Point) p)) := by
    filter_upwards [stripGreenOfKernel_ae_mem_stripPast H E.2 T e] with p hp
    have hnp : sectionTwoPoint p ∈ D := by
      refine ⟨hp.1, ?_⟩
      apply PDE.mem_translateSet_iff_sub_mem.mpr
      simpa only [sub_zero, intervalDomain, PDE.mem_oneDimensionalAxisBox_iff,
        PDE.vecOneCoordinate, sectionTwoPoint, Interval.carrier] using hp.2
    have hnU : KineticPoint.equivProd 1 (sectionTwoPoint p) ∈ U := by
      simpa only [U, mem_preimage, Equiv.symm_apply_apply] using hnp
    obtain ⟨N, hN⟩ := hcover _ hnU
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    exact (hN n hn).symm
  have hI := stripPotentialOfKernel_tendsto H E.2 T e F 1 1
    (fun n p => by
      change |χ n (KineticPoint.equivProd 1 (sectionTwoPoint p))| ≤ 1
      rw [abs_of_nonneg (hb n _).1]
      exact (hb n _).2) hlim
  let q := (e.1.velocity 0 - H.lo) * (H.hi - e.1.velocity 0) / (2 * lam)
  have hbound (n : ℕ) : stripPotentialOfKernel H E.2 T (F n) e ≤ q := by
    have heT : e.1.time < T := WithTop.coe_lt_coe.mp e.2.1
    let p := sectionTwoPoint e.1
    have hp : p ∈ D := ⟨heT, (stripPoleState H T e).2.1⟩
    have hcmp := strip_duhamel_le_quadratic hH hlam hLam A H E hE T (g n)
      (fun p => (hb n _).1) (fun p => (hb n _).2) (hgs n) (hgc n) (hgD n) p hp
    have hpot := duhamelPotential_eq_greenMeasure E.2 (intervalDomain_measurable H)
      continuous_const T (g n) (fun p => (hb n _).1) (hgcont n) (hgc n)
      e.1.time heT (stripPoleState H T e)
    have hIeq : stripPotentialOfKernel H E.2 T (F n) e = duhamelPotential E.2 T (g n) p := by
      rw [stripPotentialOfKernel, stripGreenOfKernel,
        integral_map (measurable_elapsedPhysicalPoint _ _).aemeasurable
          (F n).measurable.aestronglyMeasurable]
      exact hpot.symm
    rw [hIeq]
    simpa only [stripQuadraticBarrier_eq, q, p, sectionTwoPoint] using hcmp
  have hreal : (stripGreenOfKernel H E.2 T e).real univ ≤ q := by
    have hc : stripPotentialOfKernel H E.2 T (1 : BoundedBorel Point) e =
        (stripGreenOfKernel H E.2 T e).real univ := by
      simp [stripPotentialOfKernel, integral_const, smul_eq_mul]
    rw [hc] at hI
    exact le_of_tendsto hI (Eventually.of_forall hbound)
  rw [← ENNReal.ofReal_toReal (measure_ne_top (stripGreenOfKernel H E.2 T e) univ)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- The canonical autonomous measure obeys the exact finite-horizon quadratic bound. -/
theorem stripGreen_finite_quadratic_mass
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (T : ℝ)
    (e : StripPole H (T : WithTop ℝ)) :
    stripGreen hH hLE hlam hLam A H T e univ ≤
      ENNReal.ofReal ((e.1.velocity 0 - H.lo) * (H.hi - e.1.velocity 0) / (2 * lam)) :=
  stripGreenOfRealization_quadratic_mass hH hlam hLam A H _
    (stripEvolution_spec hH hLE hlam hLam A H) T e

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

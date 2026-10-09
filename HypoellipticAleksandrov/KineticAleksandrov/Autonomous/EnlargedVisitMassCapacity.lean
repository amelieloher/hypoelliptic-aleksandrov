module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitsPieces
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.IntegratedVelocity
import Mathlib.Tactic

/-! # Full-space bounds used in the enlarged-strip quadratic count -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory HypoellipticAleksandrov

/-- Inserting time in scalar physical coordinates is measurable. -/
theorem measurable_enlargedTerminalPoint (b : ℝ) :
    Measurable (enlargedTerminalPoint b) := by
  exact (KineticPoint.measurable_equivProd_symm 1).comp
    (measurable_const.prodMk
      ((Measurable.of_eval fun _ => measurable_fst).prodMk
        (Measurable.of_eval fun _ => measurable_snd)))

/-- The physical spacetime map for elapsed occupation is measurable. -/
theorem measurable_enlargedOccupationPoint (P : Point) :
    Measurable (fun tz : ℝ × Z => enlargedTerminalPoint (P.time + tz.1) tz.2) := by
  exact (KineticPoint.measurable_equivProd_symm 1).comp
    ((measurable_const.add measurable_fst).prodMk
      ((Measurable.of_eval fun _ => measurable_fst.comp measurable_snd).prodMk
        (Measurable.of_eval fun _ => measurable_snd.comp measurable_snd)))

/-- Full-space terminal measures have mass at most one. -/
theorem enlargedFullSpaceTerminal_mass_le_one
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (P : Point) (b : ℝ) :
    enlargedFullSpaceTerminal hH hLE hlam hLam A P b univ ≤ 1 := by
  change ((kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal (b - P.time))
    (P.position 0, P.velocity 0)).map (enlargedTerminalPoint b)) univ ≤ 1
  rw [Measure.map_apply (measurable_enlargedTerminalPoint b)
    MeasurableSet.univ, preimage_univ]
  exact kernelXV_mass_le_one _ _ _

/-- Full-space occupation of a physical velocity band is its elapsed probability integral. -/
theorem enlargedFullSpaceOccupation_band_eq
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (P : Point) (T r : ℝ) :
    enlargedFullSpaceOccupation hH hLE hlam hLam A P T {p | |p.velocity 0| ≤ 3 * r} =
      ∫⁻ t in Ioc 0 T, kernelXV (fullSpaceEvolution hH hLE hlam hLam A)
        (Real.toNNReal t) (P.position 0, P.velocity 0) {w | |w.2| ≤ 3 * r} := by
  have hB : MeasurableSet {p : Point | |p.velocity 0| ≤ 3 * r} :=
    measurableSet_le (continuous_abs.measurable.comp
      ((continuous_apply 0).comp continuous_velocity).measurable) measurable_const
  change (((volume.restrict (Ioc 0 T)) ⊗ₘ
    physicalElapsedKernel (fullSpaceEvolution hH hLE hlam hLam A)
      (P.position 0, P.velocity 0)).map
        (fun tz => enlargedTerminalPoint (P.time + tz.1) tz.2)) _ = _
  rw [Measure.map_apply (measurable_enlargedOccupationPoint P) hB,
    Measure.compProd_apply (hB.preimage (measurable_enlargedOccupationPoint P))]
  rfl

/-- The source velocity occupation bound is independent of the outer waiting interval. -/
theorem enlargedFullSpaceOccupation_band_le
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (P : Point) (T r : ℝ)
    (hT : 0 < T) (hr : 0 < r) :
    enlargedFullSpaceOccupation hH hLE hlam hLam A P T {p | |p.velocity 0| ≤ 3 * r} ≤
      ENNReal.ofReal ((64 * r / lam) * Real.sqrt (2 * Lam * T)) := by
  rw [enlargedFullSpaceOccupation_band_eq]
  simp_rw [← velocityBandProbability_eq_kernelXV]
  rw [← restrict_Ioo_eq_restrict_Ioc,
    ← velocityGreenRaw_band_eq_lintegral _ hT]
  exact velocityGreenRaw_band_mass_le hH hlam hLam A _
    (fullSpaceEvolution_spec hH hLE hlam hLam A) hr hT _

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EntranceDensityReal
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EntranceSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMass
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitTime

/-! # The literal entrance-density theorem on the clipped cylinder

Source: companion paper, (8.21). The counting and domination
estimates are used as proved; no analytic premise replaces their conclusions.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open scoped ENNReal

/-- The source core Green density has the exact radius and entrance-count scaling. -/
theorem entrance_density
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (q : ℝ) (hq : 1 < q ∧ q < 3 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock)
      (Z0 : Point) (R : ℝ) (hR : 0 < R) (P : Point)
      (hP : P ∈ forwardCylinder Z0 R hR)
      (_hcore : (c.core ∩ (capacityCylinderInterval Z0 R hR).carrier).Nonempty),
      enlargedDensityBound
        ((stripGreen hH hLE hlam hLam A (capacityCylinderInterval Z0 R hR)
          (Z0.time + R ^ 2) (capacityCylinderPole Z0 P R hR hP)).restrict
            {p | p.velocity 0 ∈ c.core}) (densityObservationStrip Z0 R hR) q
        (C * c.r ^ (6 / q - 4) * (1 + R / c.r) ^ (1 / q)) := by
  obtain ⟨B, hB, hb⟩ := exists_visitStartsQ_mass_constant hlam hLam
  obtain ⟨M, hM, hm⟩ := visit_short_time_mass hlam hLam
  obtain ⟨C, hC, hc⟩ := entrance_density_from_counts hH hLE hlam hLam q hq B M hB hM
  refine ⟨C, hC, ?_⟩
  intro A c Z0 R hR P hP _hcore
  have : SigmaFinite (volume : Measure Point) := density_volume_sigmaFinite
  let nu := visitStartsQ hH hLE hlam hLam A c Z0 R hR P hP
  have : IsFiniteMeasure nu := visitStartsQ_isFiniteMeasure hH hLE hlam hLam A c Z0 R hR P hP
  have hnu : ∀ᵐ e ∂nu, e.velocity 0 ∈ c.active :=
    (entrance_visitStartsQ_ae_closedEntrance hH hLE hlam hLam A c Z0 R hR P hP).mono
      (fun _ h => visitClosedEntrance_subset_active c h)
  have hshort (k : ℤ) : nu (entranceTimeBin c.r k) ≤ ENNReal.ofReal M := by
    simpa only [entranceTimeBin, add_mul, one_mul] using
      hm hH hLE A c Z0 R hR P hP ((k : ℝ) * c.r ^ 2)
  obtain ⟨G, hGm, hG0, hGd, hGp, hGn⟩ := hc A c nu (1 + R / c.r)
    (by positivity [c.positive]) hnu (hb hH hLE A c Z0 R hR P hP) hshort
  let Q := {p : Point | p.velocity 0 ∈ c.core}
  let mu := (stripGreen hH hLE hlam hLam A (capacityCylinderInterval Z0 R hR)
    (Z0.time + R ^ 2) (capacityCylinderPole Z0 P R hR hP)).restrict Q
  have hdom := core_green_le_visitGreen hH hLE hlam hLam A c Z0 R hR P hP
  have hbridge := entrance_coreAllTimeGreen_eq hH hLE hlam hLam A c nu
  have hmajor : mu ≤ enlargedActiveGreen hH hLE hlam hLam A c nu :=
    (hdom.trans_eq (congrArg (fun rho : Measure Point => rho.restrict Q) hbridge)).trans
      Measure.restrict_le_self
  have : IsFiniteMeasure (enlargedActiveGreen hH hLE hlam hLam A c nu) :=
    enlargedActiveGreen_isFiniteMeasure hH hLE hlam hLam A c nu
  have : IsFiniteMeasure mu := isFiniteMeasure_of_le _ hmajor
  have hle : mu ≤ volume.withDensity (fun p => ENNReal.ofReal (G p)) :=
    hmajor.trans_eq hGd
  obtain ⟨g, hgm, hg0, hgd, hgp, hgn⟩ :=
    density_of_le_withDensity volume mu G hGm hG0 (ENNReal.ofReal q) hGp hle
  let D := densityObservationStrip Z0 R hR
  have hD : MeasurableSet D :=
    (continuous_time.measurable measurableSet_Ioi).inter
      ((continuous_time.measurable measurableSet_Iio).inter
        (isOpen_Ioo.measurableSet.preimage
          ((continuous_apply 0).comp continuous_velocity).measurable))
  have hmu : ∀ᵐ p ∂mu, p ∈ D :=
    ae_restrict_of_ae (entrance_cylinderGreen_ae_observation hH hLE hlam hLam A Z0 R hR P hP)
  have hr := Measure.restrict_eq_self_of_ae_mem hmu
  have hden : mu = (volume.restrict D).withDensity (fun p => ENNReal.ofReal (g p)) :=
    hr.symm.trans ((congrArg (fun rho : Measure Point => rho.restrict D) hgd).trans
      (restrict_withDensity hD (fun p => ENNReal.ofReal (g p))))
  refine ⟨g, ⟨hgm, hg0, hden⟩, hgp.restrict D, ?_⟩
  have hn := (eLpNorm_restrict_le g (ENNReal.ofReal q) volume D).trans hgn
  exact (ENNReal.toReal_mono hGp.ne_top hn).trans hGn

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripSlab
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripIntervalBoundary

/-! # Exact nested exit decomposition on arbitrary compact ambient probes -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- The actual larger exit mixture restarted from the smaller internal boundary. -/
def nestedIntervalRestartExit
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : Interval) (sMinus T : ℝ)
    (e : StripPole H1 (T : WithTop ℝ)) : Measure Point :=
  (nestedIntervalRestartPoles hH hLE hlam hLam A H1 H2 sMinus T e).bind
    (stripExit hH hLE hlam hLam A H2 T)

/-- The actual restarted exit mixture is finite. -/
instance nestedIntervalRestartExit_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : Interval) (sMinus T : ℝ)
    (e : StripPole H1 (T : WithTop ℝ)) :
    IsFiniteMeasure (nestedIntervalRestartExit hH hLE hlam hLam A H1 H2 sMinus T e) := by
  constructor
  unfold nestedIntervalRestartExit
  rw [Measure.bind_apply MeasurableSet.univ
    (stripExit_measurable hH hLE hlam hLam A H2 T).aemeasurable]
  simp only [stripExit_mass_one, lintegral_const, one_mul]
  exact measure_lt_top _ _

/-- Every compact probe satisfies the literal larger-exit equals outer-exit plus restart
  identity. -/
theorem nestedIntervalExit_probe_identity
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : Interval)
    (hsub : H1.carrier ⊆ H2.carrier) (sMinus T : ℝ)
    (e : StripPole H1 (T : WithTop ℝ)) (he : sMinus < e.1.time)
    (f : exitProbeSubmodule) :
    (∫ p, exitProbePhysical f p ∂stripExit hH hLE hlam hLam A H2 T
      (nestedPoleInclusion H1 H2 hsub T e)) =
      (∫ p, exitProbePhysical f p ∂(stripExit hH hLE hlam hLam A H1 T e).restrict
        (reconstructionExit H2 sMinus T)) +
      ∫ p, exitProbePhysical f p
        ∂nestedIntervalRestartExit hH hLE hlam hLam A H1 H2 sMinus T e := by
  obtain ⟨u, hc, hb, htrace, hrep, hid⟩ := exists_nested_exit_potential
    hH hLE hlam hLam A H1 H2 hsub sMinus T e he f
  let μ := stripExit hH hLE hlam hLam A H1 T e
  let τ := nestedIntervalRestartPoles hH hLE hlam hLam A H1 H2 sMinus T e
  have hi := nestedSlab_integrable H2 sMinus T μ u
    (nested_exit_ae_larger_slab hH hLE hlam hLam A H1 H2 hsub sMinus T e he.le) hc hb
  have hsplit := congrArg (fun ρ : Measure Point => ∫ p, u p ∂ρ)
    (nestedIntervalExit_boundary_split hH hLE hlam hLam A H1 H2 hsub sMinus T e he)
  have hsum := integral_add_measure
    (hi.restrict (s := reconstructionExit H2 sMinus T))
    (hi.restrict (s := nestedIntervalInternalExit H1 H2 sMinus T))
  have houter : (∫ p, u p ∂μ.restrict (reconstructionExit H2 sMinus T)) =
      ∫ p, exitProbePhysical f p ∂μ.restrict (reconstructionExit H2 sMinus T) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (measurableSet_nestedIntervalExit H2 sMinus T)] with p hp
    apply htrace
    rcases hp with hp | hp
    · exact Or.inl hp
    · exact Or.inr ⟨by linarith [hp.1], hp.2⟩
  have hmap : (∫ p, u p ∂μ.restrict (nestedIntervalInternalExit H1 H2 sMinus T)) =
      ∫ ep, u ep.1 ∂τ := by
    rw [← nestedIntervalRestartPoles_map hH hLE hlam hLam A H1 H2 sMinus T e]
    exact (MeasurableEmbedding.subtype_coe (measurableSet_nestedIntervalPole H2 T)).integral_map u
  have hvalues : (∫ ep, u ep.1 ∂τ) = ∫ ep,
      ∫ p, exitProbePhysical f p ∂stripExit hH hLE hlam hLam A H2 T ep ∂τ := by
    apply integral_congr_ae
    filter_upwards [nestedIntervalRestartPoles_ae_time_gt
      hH hLE hlam hLam A H1 H2 sMinus T e] with ep hep
    exact hrep ep hep.le
  have hbind := nested_integral_bind τ (stripExit hH hLE hlam hLam A H2 T)
    (stripExit_measurable hH hLE hlam hLam A H2 T) (exitProbePhysical f)
    (nestedProbe_integrable A f
      (nestedIntervalRestartExit hH hLE hlam hLam A H1 H2 sMinus T e))
  exact hid.trans (hsplit.trans (hsum.trans (congrArg₂ (· + ·) houter
    (hmap.trans (hvalues.trans hbind.symm)))))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

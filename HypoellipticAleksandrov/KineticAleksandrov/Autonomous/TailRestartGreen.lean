module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TailRestartAction

/-! # Exact Green restart from the surviving terminal measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov SectionTwo ProbabilityTheory
open scoped ENNReal

/-- The physical Green integrand is Borel in positive elapsed time. -/
theorem tailGreen_integrand_measurable (H : Interval)
    (K : MovingFiberKernel (intervalDomain H) (fun _ => 0)) (s : ℝ)
    (z : EvolutionState (intervalDomain H) (fun _ => 0) s)
    (F : Point → ℝ≥0∞) (hF : Measurable F) :
    Measurable (fun tau : ElapsedTime ⊤ => ∫⁻ w,
      F (elapsedPhysicalPoint s (tau, w)) ∂K.master (elapsedQuery s z tau)) := by
  let k := elapsedKernel K s ⊤
  have : IsFiniteKernel k := by dsimp [k, elapsedKernel]; infer_instance
  have hm : Measurable (fun q :
      (EvolutionState (intervalDomain H) (fun _ => 0) s × ElapsedTime ⊤) ×
        EvolutionAmbientState 1 => F (elapsedPhysicalPoint s (q.1.2, q.2))) :=
    hF.comp ((measurable_elapsedPhysicalPoint s ⊤).comp
      (measurable_fst.snd.prodMk measurable_snd))
  exact (hm.lintegral_kernel_prod_right' (κ := k)).comp
    (measurable_const.prodMk measurable_id)

/-- Every strict Green tail equals the actual native terminal mixture of restarted Greens. -/
theorem tailRestart_green_identity {lam Lam : ℝ}
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (e : StripPole H ⊤) (t : ℝ) (ht : 0 ≤ t) :
    (stripGreenOfKernel H E.2 ⊤ e).restrict {p | e.1.time + t < p.time} =
      (E.2.fiberKernel (intervalDomain_measurable H) e.1.time (e.1.time + t)
        (le_add_of_nonneg_right ht) (stripPoleState H ⊤ e)).bind
          (fun a => stripGreenOfKernel H E.2 ⊤ (tailRestartPole H (e.1.time + t) a)) := by
  let r := e.1.time + t
  let z := stripPoleState H ⊤ e
  let nu := E.2.fiberKernel (intervalDomain_measurable H) e.1.time r
    (le_add_of_nonneg_right ht) z
  have : IsFiniteMeasure nu :=
    ⟨(E.2.fiberKernel_mass_le_one (intervalDomain_measurable H)
      e.1.time r (le_add_of_nonneg_right ht) z).trans_lt ENNReal.one_lt_top⟩
  have hk : Measurable (fun a =>
      stripGreenOfKernel H E.2 ⊤ (tailRestartPole H r a)) :=
    (Measure.measurable_measure.mpr (fun B hB =>
      stripGreenOfKernel_infinite_measurable_apply H E.2 B hB)).comp
        (measurable_tailRestartPole H r)
  apply Measure.ext_of_lintegral
  intro F hF
  have hL : MeasurableSet {p : Point | e.1.time + t < p.time} :=
    continuous_time.measurable measurableSet_Ioi
  rw [← lintegral_indicator hL,
    stripGreenOfKernel_spec H E.2 ⊤ e _ (hF.indicator hL)]
  have hi := tailGreen_integrand_measurable H E.2 e.1.time z F hF
  have heq : (fun tau : ElapsedTime ⊤ => ∫⁻ w,
      {p : Point | e.1.time + t < p.time}.indicator F
        (elapsedPhysicalPoint e.1.time (tau, w))
        ∂E.2.master (elapsedQuery e.1.time z tau)) =
      {tau : ElapsedTime ⊤ | t < tau.1}.indicator
        (fun tau => ∫⁻ w, F (elapsedPhysicalPoint e.1.time (tau, w))
          ∂E.2.master (elapsedQuery e.1.time z tau)) := by
    funext tau
    by_cases hh : t < tau.1
    · have hh' : e.1.time + t < e.1.time + tau.1 := by linarith
      simp only [Set.indicator, Set.mem_ofPred_eq, elapsedPhysicalPoint, hh, hh', ite_true]
    · have hh' : ¬e.1.time + t < e.1.time + tau.1 := by simpa using hh
      simp only [Set.indicator, Set.mem_ofPred_eq, elapsedPhysicalPoint,
        hh, hh', ite_false, lintegral_zero]
  change (∫⁻ tau, (fun tau : ElapsedTime ⊤ => ∫⁻ w,
    {p : Point | e.1.time + t < p.time}.indicator F
      (elapsedPhysicalPoint e.1.time (tau, w))
      ∂E.2.master (elapsedQuery e.1.time z tau)) tau ∂elapsedVolume ⊤) = _
  rw [heq, lintegral_indicator (show MeasurableSet {tau : ElapsedTime ⊤ | t < tau.1}
      from measurable_subtype_coe measurableSet_Ioi),
    ← tailElapsedShift_map t ht, lintegral_map hi (measurable_tailElapsedShift t ht)]
  have hc : (∫⁻ tau : ElapsedTime ⊤, ∫⁻ w,
      F (elapsedPhysicalPoint e.1.time (tailElapsedShift t ht tau, w))
      ∂E.2.master (elapsedQuery e.1.time z (tailElapsedShift t ht tau))
      ∂elapsedVolume ⊤) =
      ∫⁻ tau : ElapsedTime ⊤, ∫⁻ a, ∫⁻ w, F ⟨r + tau.1, w.2, w.1⟩
        ∂E.2.master (tailRestartQuery H r (tau, a)) ∂nu ∂elapsedVolume ⊤ := by
    apply lintegral_congr
    intro tau
    have hh := tailRestart_master_lintegral A H E hE e.1.time r (r + tau.1)
      (le_add_of_nonneg_right ht) (le_add_of_nonneg_right tau.2.1.le) z F hF
    have htau : e.1.time + (t + tau.1) = r + tau.1 := by dsimp [r]; ring
    simpa only [elapsedPhysicalPoint, tailElapsedShift, elapsedQuery, htau,
      tailRestartQuery, nu] using hh
  rw [hc, tailRestart_action_swap H E.2 r nu F hF]
  exact (Measure.lintegral_bind hk.aemeasurable hF.aemeasurable).symm

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

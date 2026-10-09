module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BelowFourBandArrivalKernel

/-! # Removing the starting-velocity restriction by actual first arrival and Minkowski -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

/-- The actual core Green measure inherits a uniform entrance-pole bound by first arrival. -/
theorem belowFour_first_arrival
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (H : Interval) (s T q K : ℝ)
    (hq : 1 < q) (hK : 0 ≤ K)
    (hstart : ∀ ep : StripPole H (T : WithTop ℝ), s ≤ ep.1.time →
      ep.1.velocity 0 ∈ closure c.entrance →
      ∃ G : Point → ℝ, Measurable G ∧ (∀ z, 0 ≤ G z) ∧
        (stripGreen hH hLE hlam hLam A H T ep).restrict {z | z.velocity 0 ∈ c.core} =
          volume.withDensity (fun z => ENNReal.ofReal (G z)) ∧
        MemLp G (ENNReal.ofReal q) volume ∧
        (eLpNorm G (ENNReal.ofReal q) volume).toReal ≤ K)
    (e : StripPole H (T : WithTop ℝ)) (he : s < e.1.time) :
    ∃ G : Point → ℝ, Measurable G ∧ (∀ z, 0 ≤ G z) ∧
      (stripGreen hH hLE hlam hLam A H T e).restrict {z | z.velocity 0 ∈ c.core} =
        volume.withDensity (fun z => ENNReal.ofReal (G z)) ∧
      MemLp G (ENNReal.ofReal q) volume ∧
      (eLpNorm G (ENNReal.ofReal q) volume).toReal ≤ K := by
  by_cases hvel : e.1.velocity 0 ∈ closure c.entrance
  · exact hstart e he.le hvel
  obtain ⟨W, hv, hsub, hdisj, hface⟩ := belowFour_waiting_interval c H (e.1.velocity 0) e.2.2 hvel
  let ew : StripPole W (T : WithTop ℝ) := ⟨e.1, e.2.1, hv⟩
  let tau := nestedIntervalRestartPoles hH hLE hlam hLam A W H s T ew
  let k := belowFour_coreGreenKernel hH hLE hlam hLam A c H T
  have hbound : ∀ᵐ ep ∂tau, ∃ G : Point → ℝ,
      Measurable G ∧ (∀ z, 0 ≤ G z) ∧
      k ep = volume.withDensity (fun z => ENNReal.ofReal (G z)) ∧
      MemLp G (ENNReal.ofReal q) volume ∧ (eLpNorm G (ENNReal.ofReal q) volume).toReal ≤ K := by
    filter_upwards [belowFour_restart_ae_internal hH hLE hlam hLam A W H s T ew] with ep hp
    exact hstart ep hp.1.le (hface _ hp.2.2.1 hp.2.2.2)
  obtain ⟨G, hG, hG0, hGd, hGp, hGn⟩ := belowFour_density_subprobability_mixture tau k q K hq hK
    (belowFour_restart_mass_le_one hH hLE hlam hLam A W H s T ew he.le) hbound
  have hC : MeasurableSet {z : Point | z.velocity 0 ∈ c.core} :=
    isClosed_Icc.measurableSet.preimage ((continuous_apply 0).comp continuous_velocity).measurable
  have hz : (stripGreen hH hLE hlam hLam A W T ew).restrict {z | z.velocity 0 ∈ c.core} = 0 := by
    apply Measure.restrict_eq_zero.mpr
    have hp := stripGreenOfKernel_ae_mem_stripPast W (stripEvolution hH hLE hlam hLam A W).2 T ew
    have hzero := ae_iff.mp (hp.mono (fun z hz => hz.2))
    exact le_antisymm ((measure_mono (show {z : Point | z.velocity 0 ∈ c.core} ⊆
      {z | z.velocity 0 ∉ W.carrier} from
        fun z hc hw => disjoint_left.mp hdisj hw hc)).trans_eq hzero) zero_le
  have hid := nestedIntervalGreen_identity hH hLE hlam hLam A W H hsub s T ew he
  have hep : nestedPoleInclusion W H hsub T ew = e := Subtype.ext rfl
  rw [hep] at hid
  have hr : (nestedIntervalRestartGreen hH hLE hlam hLam A W H s T ew).restrict
      {z | z.velocity 0 ∈ c.core} = k ∘ₘ tau := by
    exact nested_bind_restrict tau _
      (Measure.measurable_measure.mpr (fun B hB =>
        stripGreen_measurable_apply hH hLE hlam hLam A H T B hB)) _ hC
  have hm : (stripGreen hH hLE hlam hLam A H T e).restrict {z | z.velocity 0 ∈ c.core} =
      k ∘ₘ tau := by
    rw [hid, Measure.restrict_add, hz, zero_add, hr]
  exact ⟨G, hG, hG0, hm.trans hGd, hGp, hGn⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

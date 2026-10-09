module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BelowFourBandArrival

/-! # The exact improved core-band proposition from its named source predecessors

The enlarged-strip source measure supplies the core-start estimate. Actual
nested-strip first arrival removes its entrance-velocity restriction. The
result remains conditional on the four unproved analytic predecessor Props
and the clock-pushforward proposition, with only the hypotheses hH/hLE.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory Filter
open scoped ENNReal

/-- The band proposition follows from its direct predecessors. -/
theorem below_four_band_of_predecessors (hpush : PushforwardStatement)
    (htail : RestartTailStatement) (hvisits : PositionVisitsStatement)
    (hmasses : PositionVisitMassesStatement) (hcore : CoreDominationStatement) :
    BelowFourBandStatement := by
  intro hH hLE lam Lam hlam hLam alpha q ha hq
  obtain ⟨C, hC, hd⟩ := below_four_core_start_band hpush htail hvisits hmasses hcore
    hH hLE hlam hLam alpha q ha hq
  refine ⟨C, hC, ?_⟩
  intro A c Z₀ R hR P hP hc hr
  let H := capacityCylinderInterval Z₀ R hR
  let T := Z₀.time + R ^ 2
  let e := capacityCylinderPole Z₀ P R hR hP
  let K := (C * R ^ (6 - 4 * q) *
    (c.r / R) ^ (4 - 3 * q + (1 - alpha) * (q - 1))) ^ (1 / q)
  have hK : 0 ≤ K := Real.rpow_nonneg
    (mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg hR.le _))
      (Real.rpow_nonneg (div_pos c.positive hR).le _)) _
  have hstart (ep : StripPole H (T : WithTop ℝ)) (hs : Z₀.time ≤ ep.1.time)
      (hv : ep.1.velocity 0 ∈ closure c.entrance) := hd A c H Z₀.time R hR ep hs hv hc hr
  obtain ⟨G, hG, hG0, hGd, hGp, hGn⟩ := belowFour_first_arrival hH hLE hlam hLam A c H
    Z₀.time T q K hq.1 hK hstart e hP.1
  let mu := (stripGreen hH hLE hlam hLam A H T e).restrict {z | z.velocity 0 ∈ c.core}
  let D := densityObservationStrip Z₀ R hR
  have hD : MeasurableSet D :=
    (isOpen_lt continuous_const continuous_time).measurableSet.inter
      ((isOpen_lt continuous_time continuous_const).measurableSet.inter
        (isOpen_Ioo.measurableSet.preimage
          ((continuous_apply 0).comp continuous_velocity).measurable))
  have hpast := stripGreenOfKernel_ae_mem_stripPast H (stripEvolution hH hLE hlam hLam A H).2 T e
  let ei : StripPole H ⊤ := ⟨e.1, WithTop.coe_lt_top _, e.2.2⟩
  have hfuture := (stripGreen_infinite_ae_future_carrier hH hLE hlam hLam A H ei).filter_mono
    (stripGreen_mono hH hLE hlam hLam A H H Subset.rfl T ⊤ le_top e).absolutelyContinuous.ae_le
  have hmu : ∀ᵐ z ∂mu, z ∈ D := by
    filter_upwards [ae_restrict_of_ae hpast, ae_restrict_of_ae hfuture] with z hz ht
    exact ⟨hP.1.trans ht.1, hz.1, hz.2⟩
  have hm : mu.restrict D = mu := Measure.restrict_eq_self_of_ae_mem hmu
  have hdensity : mu = (volume.restrict D).withDensity (fun z => ENNReal.ofReal (G z)) := by
    rw [← hm]
    dsimp only [mu]
    rw [hGd, restrict_withDensity hD]
  refine ⟨G, hG, hG0, hdensity, hGp.restrict D, ?_⟩
  exact (ENNReal.toReal_mono hGp.ne (eLpNorm_restrict_le G (ENNReal.ofReal q) volume D)).trans hGn

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

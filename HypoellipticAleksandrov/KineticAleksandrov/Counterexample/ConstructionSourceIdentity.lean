module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionOperatorConvergence
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionPlateau
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.BarrierPackedJets
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionExtensionSupport

/-! # Identification of the full extended source with the raw cutoff source -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory Set HypoellipticAleksandrov.Parabolic

/-- On the profile domain the extended source is exactly the raw cutoff source, with no
extra multiplier terms. The same jointly selected flattened jets occur on both sides. -/
theorem construction_extendedSource_eq_raw_on_profile {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R m t : ℝ) (hm : m < R ^ 2)
    (hmargin : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < m)
    (q : XV d) (hq : profileFunction h q < 1) :
    constructionExtendedSource h r mu R m (profileMatrix h) ⟨t, q.1, q.2⟩ =
      timeCutoffSourceRepresentative h r mu R ⟨t, q.1, q.2⟩ := by
  have hj := construction_extended_jets_eq_raw_on_profile h r mu R m t hm hmargin
    ((spatialCoordinateCLE d).symm q) (by
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using hq)
  simp only [constructionExtendedSource, constructionExtendedNativeGradient,
    constructionExtendedNativeHessian, hj.1, hj.2]
  have hq' : (q.1, q.2) ∈ {y | profileFunction h y < 1} := hq
  simp only [constructionExtendedTimeJet, indicator_of_mem hq',
    timeCutoffProfile_timeDerivative, timeCutoffSourceRepresentative,
    spatialPackedCutoffGradient, spatialPackedCutoffVelocityHessian,
    spatialPackedGradient, Fin.addCases_left,
    spatialPackedBarrier_positionGradient, spatialPackedBarrier_velocityHessian,
    spatialPackedBarrier,
    ContinuousLinearEquiv.apply_symm_apply, sub_zero, barrier_velocityGradient,
    barrier_velocityHessian, Pi.sub_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [spatialPackedBarrier_velocityGradient,
    ContinuousLinearEquiv.apply_symm_apply, Prod.mk.eta]

/-- The full extended source is the raw source inside the profile domain and zero outside,
almost everywhere at every fixed time. -/
theorem construction_extendedSource_eq_indicator_ae {d : ℕ} (hd : 1 ≤ d)
    {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r mu R m : ℝ)
    (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R) (hm : m < R ^ 2)
    (hscale : 2 * Real.rpow r alpha ≤ 1)
    (hmargin : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < m) (t : ℝ) :
    (fun q : XV d => constructionExtendedSource h r mu R m (profileMatrix h)
        ⟨t, q.1, q.2⟩) =ᵐ[volume]
      {q | profileFunction h q < 1}.indicator
        (fun q => timeCutoffSourceRepresentative h r mu R ⟨t, q.1, q.2⟩) := by
  have hj := construction_ae_native _
    (construction_extended_jets_zero_outside_profile hd ha ha1 h r mu R m hr hmu hR hm
      hscale (fun q hq => (hmargin q hq).le) t)
  filter_upwards [hj] with q hq
  change constructionExtendedSource h r mu R m (profileMatrix h) ⟨t, q.1, q.2⟩ =
    {y | profileFunction h y < 1}.indicator
      (fun y => timeCutoffSourceRepresentative h r mu R ⟨t, y.1, y.2⟩) q
  by_cases hprof : profileFunction h q < 1
  · have hmem : q ∈ {y | profileFunction h y < 1} := hprof
    rw [indicator_of_mem hmem]
    exact construction_extendedSource_eq_raw_on_profile h r mu R m t hm hmargin q hprof
  · have hn : 1 ≤ profileFunction h
        (spatialCoordinateCLE d ((spatialCoordinateCLE d).symm q)) := by
      simpa only [ContinuousLinearEquiv.apply_symm_apply] using (not_lt.mp hprof)
    have hh := hq hn
    have hmem : q ∉ {y | profileFunction h y < 1} := hprof
    rw [indicator_of_notMem hmem]
    simp only [constructionExtendedSource, constructionExtendedTimeJet,
      constructionExtendedNativeGradient, constructionExtendedNativeHessian, Prod.mk.eta,
      indicator_of_notMem hmem, hh.1, hh.2, PDE.vecDot, matrixContraction,
      mul_zero, Finset.sum_const_zero, add_zero, sub_zero]

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

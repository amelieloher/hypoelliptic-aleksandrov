module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionMollifiedJets

/-! # Almost-everywhere convergence of the selected spatial jets -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Filter MeasureTheory
open scoped Topology Convolution

/-- The concrete normalized kernels recover every locally integrable native scalar field. -/
theorem construction_spatialMollify_tendsto_ae {d : ℕ} (f : XV d → ℝ)
    (hf : LocallyIntegrable f volume) :
    ∀ᵐ q ∂volume, Tendsto
      (fun n => spatialMollify (standardMollifierSequence n) f q) atTop (𝓝 (f q)) := by
  exact ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    standardMollifierSequence_rOut_tendsto
    (Eventually.of_forall standardMollifierSequence_radius_ratio) hf

/-- At each time the selected first and second representatives are recovered simultaneously. -/
theorem construction_selected_jets_tendsto_ae {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r) (mu R m t : ℝ) :
    ∀ᵐ q ∂volume,
      (∀ i : Fin (d + d), Tendsto
        (fun n => spatialMollify (standardMollifierSequence n)
          (fun y => constructionExtendedNativeGradient h r mu R m t y i) q)
        atTop (𝓝 (constructionExtendedNativeGradient h r mu R m t q i))) ∧
      (∀ i k : Fin d, Tendsto
        (fun n => spatialMollify (standardMollifierSequence n)
          (fun y => constructionExtendedNativeHessian h r mu R m t y i k) q)
        atTop (𝓝 (constructionExtendedNativeHessian h r mu R m t q i k))) := by
  have hg (i : Fin (d + d)) := construction_spatialMollify_tendsto_ae
    (fun y => constructionExtendedNativeGradient h r mu R m t y i)
    (construction_locallyIntegrable_native _
      (construction_extendedGradient_locallyIntegrable h r hr mu R m t i))
  have hh (i k : Fin d) := construction_spatialMollify_tendsto_ae
    (fun y => constructionExtendedNativeHessian h r mu R m t y i k)
    (construction_locallyIntegrable_native _
      (construction_extendedHessian_locallyIntegrable h r hr mu R m t i k))
  exact (ae_all_iff.mpr hg).and (ae_all_iff.mpr fun i => ae_all_iff.mpr (hh i))

/-- The actual mollified spatial first and second derivatives converge to the selected jets. -/
theorem construction_actual_jets_tendsto_ae {d : ℕ} (hd : 1 ≤ d)
    {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r mu R m : ℝ)
    (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R) (hm : m < R ^ 2)
    (hscale : 2 * Real.rpow r alpha ≤ 1)
    (hmargin : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 ≤ m) (t : ℝ) :
    ∀ᵐ q ∂volume,
      (∀ i : Fin (d + d), Tendsto
        (fun n => fderiv ℝ (spatialMollify (standardMollifierSequence n) (fun y =>
          zeroExtendedProfile (profileFunction h) alpha r mu R ⟨t, y.1, y.2⟩)) q
            (spatialCoordinateCLE d (PDE.basisVec i)))
        atTop (𝓝 (constructionExtendedNativeGradient h r mu R m t q i))) ∧
      (∀ i k : Fin d, Tendsto
        (fun n => dvv (spatialMollify (standardMollifierSequence n) (fun y =>
          zeroExtendedProfile (profileFunction h) alpha r mu R ⟨t, y.1, y.2⟩)) q i k)
        atTop (𝓝 (constructionExtendedNativeHessian h r mu R m t q i k))) := by
  filter_upwards [construction_selected_jets_tendsto_ae h r hr mu R m t] with q hq
  constructor
  · intro i
    simpa only [construction_mollified_first_jet hd ha ha1 h r mu R m hr hmu hR hm
      hscale hmargin] using hq.1 i
  · intro i k
    simpa only [construction_mollified_second_velocity_jet hd ha ha1 h r mu R m hr hmu hR hm
      hscale hmargin] using hq.2 i k

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.KillingComparison
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.OccupationDensity

/-! # Scalar comparison with the whole-space evolution

The scalar equation is independent of the kinetic drift. This comparison preserves
its coefficient field and does not identify two different kinetic drift fields.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay
open HypoellipticAleksandrov.KineticAleksandrov.Occupation

/-- Nonnegative smooth interior tests have smaller interval transition integral. -/
theorem interval_scalar_test_le_whole {a c lam Lam σ τ : ℝ}
    (hac : a < c) (hστ : σ < τ) (B : CoefficientField 1)
    (hB : IsSectionTwoCoefficient lam Lam B)
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (hp : HasParabolicMarginalBundle (PDE.oneDimensionalAxisBox a c) stationary hJ
      (zIndependentCoefficient B) K)
    (Kw : MovingFiberKernel (wholeSpace 1) (fun _ => (0 : PDE.Vec 1)))
    (hpw : HasParabolicMarginalBundle (wholeSpace 1) (fun _ => (0 : PDE.Vec 1)) MeasurableSet.univ
      (zIndependentCoefficient B) Kw)
    (φ : PDE.Vec 1 → ℝ) (hφs : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (hφJ : tsupport φ ⊆ PDE.oneDimensionalAxisBox a c)
    (hφ0 : ∀ v, 0 ≤ φ v) (v : PDE.Vec 1)
    (hv : v ∈ movingDomain (PDE.oneDimensionalAxisBox a c) stationary σ) :
    (∫ w, φ w ∂P K hJ (scalarQuery σ τ hστ.le v hv)) ≤
      ∫ w, φ w ∂Kw.firstMarginal (wholeSpaceQuery σ τ hστ.le v 0) := by
  obtain ⟨M, hM⟩ := hφs.continuous.bounded_above_of_compact_support hφc
  let F : BoundedBorel (PDE.Vec 1) :=
    ⟨φ, hφs.continuous.measurable, ⟨max M 0, le_max_right _ _, fun w =>
      (show |φ w| ≤ M from by simpa only [Real.norm_eq_abs] using hM w).trans
        (le_max_left _ _)⟩⟩
  obtain ⟨Q, _, _, _, _, _, hrepr, _, _, _, hsolve⟩ := hp (fun _ _ _ _ => rfl)
  obtain ⟨Qw, hfirstw, _, hposw, _, _, hreprw, _, _, _, hsolvew⟩ :=
    hpw (fun _ _ _ _ => rfl)
  obtain ⟨V, hV, heval, _⟩ := hsolve τ F
    ⟨hφs, hφc, by simpa only [movingDomain_stationary] using hφJ⟩
  obtain ⟨U, hU, hevalw, _⟩ := hsolvew τ F
    ⟨hφs, hφc, fun _ _ => by simp only [movingDomain_wholeSpace, mem_univ]⟩
  have hUn : ∀ p : TimeVelocity 1, p.1 ≤ τ → 0 ≤ U p := by
    intro p ht
    rw [hevalw p.1 ht ⟨p.2, by simp only [movingDomain_wholeSpace, mem_univ]⟩]
    exact hposw p.1 τ ht (terminalPositionDatum F) (fun w => hφ0 w.1) _
  have hcmp := interval_terminal_comparison hac hστ hB.1 B hB F V U hV
    (hU.2.1.mono fun p hp => ⟨hp.1.2, by
      simp only [movingDomain_wholeSpace, closure_univ, mem_univ]⟩)
    (fun p hp => (hU.2.2.1 p ⟨hp.1.2, by
      simp only [movingDomain_wholeSpace, mem_univ]⟩).contDiffAt
      (by
        simpa only [ParabolicProbe.scalarPastOpenCylinder, movingDomain_wholeSpace, mem_univ,
          and_true, preimage, Iio, mem_ofPred_eq] using
          (isOpen_Iio.preimage continuous_fst).mem_nhds hp.1.2)
      |>.of_le (by norm_num))
    (fun p hp => (hU.2.2.2.1 p ⟨hp.1.2, by
      simp only [movingDomain_wholeSpace, mem_univ]⟩).le)
    (fun w _ => (hU.2.2.2.2.1 (τ, w) ⟨rfl, by
      simp only [movingDomain_wholeSpace, closure_univ, mem_univ]⟩).ge)
    (fun p hp => hUn p hp.1.2) v (subset_closure (by
      simpa only [movingDomain_stationary] using hv))
  rw [heval σ hστ.le ⟨v, hv⟩, hrepr] at hcmp
  rw [hevalw σ hστ.le ⟨v, by simp only [movingDomain_wholeSpace, mem_univ]⟩, hreprw] at hcmp
  have hi := integral_map (μ := parabolicMarginalKernel K hJ σ τ hστ.le ⟨v, hv⟩)
    measurable_subtype_coe.aemeasurable hφs.continuous.measurable.aestronglyMeasurable
  have hiw := integral_map (μ := parabolicMarginalKernel Kw MeasurableSet.univ σ τ
      hστ.le ⟨v, by simp only [movingDomain_wholeSpace, mem_univ]⟩)
    measurable_subtype_coe.aemeasurable hφs.continuous.measurable.aestronglyMeasurable
  change (∫ w, φ w ∂Measure.map Subtype.val
    (parabolicMarginalKernel K hJ σ τ hστ.le ⟨v, hv⟩)) ≤ _
  rw [hi]
  have hmap := Kw.map_fiberFirstMarginal_eq_firstMarginal MeasurableSet.univ σ τ
    hστ.le (evolutionStateOfPosition (wholeSpace 1) (fun _ => (0 : PDE.Vec 1)) σ
      ⟨v, by simp only [movingDomain_wholeSpace, mem_univ]⟩ 0)
  have hfirstw' := hfirstw σ τ hστ.le
    ⟨v, by simp only [movingDomain_wholeSpace, mem_univ]⟩ 0
  rw [← hfirstw'] at hmap
  change (∫ w, φ w.1 ∂parabolicMarginalKernel K hJ σ τ hστ.le ⟨v, hv⟩) ≤
    ∫ w, φ w ∂Kw.firstMarginal
      (evolutionQueryOfState (wholeSpace 1) (fun _ => (0 : PDE.Vec 1)) σ τ hστ.le
        (evolutionStateOfPosition (wholeSpace 1) (fun _ => (0 : PDE.Vec 1)) σ
          ⟨v, by simp only [movingDomain_wholeSpace, mem_univ]⟩ 0))
  rw [← hmap, hiw]
  exact hcmp

end HypoellipticAleksandrov.KineticAleksandrov.Interval

module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinPrimalFixedTestLimit

/-!
# Arbitrary-test reverse-time Galerkin limit identity

This module extends the common-subsequence identity from the dense
range of actual Galerkin vectors to every spatial `H¹₀` Hilbert test.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal Matrix Matrix.Norms.Elementwise MatrixOrder RealInnerProductSpace
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ} {Ω : Set (PDE.Vec d)}
variable
  (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam)
  (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
  (a : CoefficientField d)
  (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
  (haSmooth : IsSmoothOnNeighborhood
    (fun z : TimeVelocity d => a z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hbSmooth : IsSmoothOnNeighborhood
    (fun z : TimeVelocity d => b z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hcSmooth : IsSmoothOnNeighborhood
    (fun z : TimeVelocity d => c z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hFSmooth : IsSmoothOnNeighborhood
    (fun z : TimeVelocity d => F z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hLower : ∀ z : TimeVelocity d,
    z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
      lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
  (hcNonpos : ∀ z : TimeVelocity d,
    z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0)

/-- The quotient-level reverse-time identity against an arbitrary spatial test. -/
def reverseTimeGalerkinPrimal_arbitrary_test_identity_prop
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (U : ReverseTimeL2V hΩ (r₁ - r₀))
    (v : H10HilbertGraph hΩ)
    (eta : ReverseTimeScalarTest (r₁ - r₀)) : Prop :=
  reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
      (reverseTimeSeparatedVTestOfMemLp hΩ eta.deriv
        (eta.memLp_deriv ∞) v)
      (reverseTimeGelfandCLM hΩ (r₁ - r₀) U) =
    -reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
        (reverseTimeSeparatedVTest hΩ eta v)
        (reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth) +
      reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
        (reverseTimeSeparatedVTest hΩ eta v)
        (reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded
          a b c haSmooth hbSmooth hcSmooth U)

/-- One common weakly convergent Galerkin subsequence satisfies the identity
for every spatial test and every scalar time test. -/
theorem exists_strictMono_tendsto_clm_reverseTimeGalerkinPrimal_arbitraryTests
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ∃ (U : ReverseTimeL2V hΩ (r₁ - r₀)) (φ : ℕ → ℕ),
      StrictMono φ ∧
      (∀ ell : ReverseTimeL2V hΩ (r₁ - r₀) →L[ℝ] ℝ,
        Tendsto
          (fun n => ell
            (reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
              a b c F haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos
              (φ n) initial))
          atTop (𝓝 (ell U))) ∧
      ∀ (v : H10HilbertGraph hΩ)
        (eta : ReverseTimeScalarTest (r₁ - r₀)),
        reverseTimeGalerkinPrimal_arbitrary_test_identity_prop
          r₀ r₁ h₀₁ hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth U v eta := by
  obtain ⟨U, φ, hφ, hclm, hfixed⟩ :=
    exists_strictMono_tendsto_clm_reverseTimeGalerkinPrimal_fixedTests
      r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial
  refine ⟨U, φ, hφ, hclm, ?_⟩
  intro v eta
  have hvClosure : v ∈ closure (Set.range (galerkinVector hΩ)) := by
    rw [(denseRange_galerkinVector hΩ).closure_range]
    exact Set.mem_univ v
  obtain ⟨vN, hvN, hv⟩ := mem_closure_iff_seq_limit.mp hvClosure
  choose k hk using hvN
  let G := reverseTimeGelfandCLM hΩ (r₁ - r₀) U
  let S := reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth
  let A := reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth U
  let mass : H10HilbertGraph hΩ → ℝ := fun w =>
    reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
      (reverseTimeSeparatedVTestOfMemLp hΩ eta.deriv (eta.memLp_deriv ∞) w) G
  let source : H10HilbertGraph hΩ → ℝ := fun w =>
    reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
      (reverseTimeSeparatedVTest hΩ eta w) S
  let form : H10HilbertGraph hΩ → ℝ := fun w =>
    reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
      (reverseTimeSeparatedVTest hΩ eta w) A
  have hMass : Tendsto (fun n => mass (vN n)) atTop (𝓝 (mass v)) := by
    change Tendsto
      (fun n => reverseTimeDualPairingCLM hΩ (r₁ - r₀) G
        (reverseTimeSeparatedVTestOfMemLp hΩ eta.deriv (eta.memLp_deriv ∞) (vN n)))
      atTop
      (𝓝 (reverseTimeDualPairingCLM hΩ (r₁ - r₀) G
        (reverseTimeSeparatedVTestOfMemLp hΩ eta.deriv (eta.memLp_deriv ∞) v)))
    exact (reverseTimeDualPairingCLM hΩ (r₁ - r₀) G).continuous.tendsto _ |>.comp
      (tendsto_reverseTimeSeparatedVTestOfMemLp hΩ eta.deriv
        (eta.memLp_deriv ∞) hv)
  have hSource : Tendsto (fun n => source (vN n)) atTop (𝓝 (source v)) := by
    change Tendsto
      (fun n => reverseTimeDualPairingCLM hΩ (r₁ - r₀) S
        (reverseTimeSeparatedVTest hΩ eta (vN n)))
      atTop
      (𝓝 (reverseTimeDualPairingCLM hΩ (r₁ - r₀) S
        (reverseTimeSeparatedVTest hΩ eta v)))
    exact (reverseTimeDualPairingCLM hΩ (r₁ - r₀) S).continuous.tendsto _ |>.comp
      (tendsto_reverseTimeSeparatedVTest hΩ eta hv)
  have hForm : Tendsto (fun n => form (vN n)) atTop (𝓝 (form v)) := by
    change Tendsto
      (fun n => reverseTimeDualPairingCLM hΩ (r₁ - r₀) A
        (reverseTimeSeparatedVTest hΩ eta (vN n)))
      atTop
      (𝓝 (reverseTimeDualPairingCLM hΩ (r₁ - r₀) A
        (reverseTimeSeparatedVTest hΩ eta v)))
    exact (reverseTimeDualPairingCLM hΩ (r₁ - r₀) A).continuous.tendsto _ |>.comp
      (tendsto_reverseTimeSeparatedVTest hΩ eta hv)
  have hFixed : ∀ n, mass (vN n) = -source (vN n) + form (vN n) := by
    intro n
    simpa only [reverseTimeGalerkinPrimal_fixed_test_identity_prop, mass, source, form, G, S,
      A, hk n] using hfixed (k n) eta
  have hRight : Tendsto (fun n => -source (vN n) + form (vN n)) atTop
      (𝓝 (-source v + form v)) :=
    hSource.neg.add hForm
  have hLimit : mass v = -source v + form v :=
    tendsto_nhds_unique_of_eventuallyEq hMass hRight (Eventually.of_forall hFixed)
  simpa only [reverseTimeGalerkinPrimal_arbitrary_test_identity_prop, mass, source, form, G,
    S, A] using hLimit

end HypoellipticAleksandrov.Parabolic.Dirichlet

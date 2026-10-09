module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ConeSupportCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundaryMeasureCanonical
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonLinear

/-! # Boundary values are ordered by bounded smooth supersolutions -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic SectionTwo TheoremA

/-- Smooth physical differences obey the literal operator subtraction identity. -/
theorem cone_forward_sub {d : ℕ} (B : CoefficientField d)
    {D : Set (KineticPoint d)} (hD : IsOpen D) (u v : KineticPoint d → ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ (KineticPoint.equivProd d).symm)
      ((KineticPoint.equivProd d) '' D))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (v ∘ (KineticPoint.equivProd d).symm)
      ((KineticPoint.equivProd d) '' D)) (P : KineticPoint d) (hP : P ∈ D) :
    forwardKineticOperator (ofTimeVelocityCoefficient B) (fun Q => u Q - v Q) P =
      forwardKineticOperator (ofTimeVelocityCoefficient B) u P -
        forwardKineticOperator (ofTimeVelocityCoefficient B) v P := by
  have hur := boundary_swapped_slice_regular hD hu (sectionTwoPoint P) hP
  have hvr := boundary_swapped_slice_regular hD hv (sectionTwoPoint P) hP
  rw [forwardKineticOperator_eq_lop_identity B (fun Q => u Q - v Q),
    forwardKineticOperator_eq_lop_identity B u, forwardKineticOperator_eq_lop_identity B v]
  change transportedForwardOperator (zIndependentCoefficient B) (identityDrift d)
    (fun Q => (u ∘ sectionTwoPoint) Q - (v ∘ sectionTwoPoint) Q) (sectionTwoPoint P) = _
  simpa only [viscousTransportedOperator_zero, lop] using!
    (viscousTransportedOperator_sub (B := zIndependentCoefficient B)
      (b := identityDrift d) (ε := 0) hur hvr)

/-- A bounded smooth supersolution dominates the actual boundary-solution value. -/
theorem cone_boundarySolution_le_supersolution
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)
    (a T : ℝ) (haT : a < T) (φ v : KineticPoint d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) (φ ∘ (KineticPoint.equivProd d).symm))
    (hc : HasCompactSupport φ)
    (hv : ContDiff ℝ (⊤ : ℕ∞) (v ∘ (KineticPoint.equivProd d).symm))
    (hb : ∃ M : ℝ, ∀ P ∈ localClosedStrip a T v₀ R, |v P| ≤ M)
    (hop : ∀ P ∈ localStrip a T v₀ R,
      forwardKineticOperator (ofTimeVelocityCoefficient B) v P ≤ 0)
    (htr : ∀ P ∈ localTrace a T v₀ R, φ P ≤ v P) :
    ∀ P ∈ localClosedStrip a T v₀ R,
      ballBoundarySolution hH hLE hd hlam hLam B hB v₀ hR a T φ P ≤ v P := by
  let E := ballBoundarySolution hH hLE hd hlam hLam B hB v₀ hR a T φ
  obtain ⟨hs, he, hEc, hEt⟩ :=
    ballBoundarySolution_smooth_traces hH hLE hd hlam hLam B hB v₀ hR a T haT φ hφ hc
  obtain ⟨C, hC⟩ := ballBoundarySolution_bounded hH hLE hd hlam hLam B hB v₀ hR
    a T haT φ hφ hc
  obtain ⟨M, hM⟩ := hb
  have hvc := boundary_probe_continuous v hv
  have hm := cone_bounded_subsolution_comparison B hB a T haT v₀ R
    (fun P => E P - v P) (hs.sub hv.contDiffOn) (fun P hP => by
      rw [cone_forward_sub B (isOpen_localStrip a T v₀ R) E v hs hv.contDiffOn P hP,
        he P hP]
      exact sub_nonneg.mpr (hop P hP))
    (hEc.sub hvc.continuousOn)
    ⟨C + M, fun P hP => (abs_sub (E P) (v P)).trans
      (add_le_add (hC P hP) (hM P hP))⟩ 0 (fun P hP => by
        rw [show E P = φ P from hEt hP]
        exact sub_nonpos.mpr (htr P hP))
  intro P hP
  exact sub_nonpos.mp (hm P hP)

end HypoellipticAleksandrov.KineticAleksandrov.LocalA

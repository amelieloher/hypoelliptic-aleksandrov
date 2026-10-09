module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundaryFunctionalGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonNodes
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierBound

/-! # Bounded subsolution comparison on the full physical strip -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory SectionTwo Evolution TheoremA Parabolic
open scoped Topology

/-- A bounded smooth subsolution is ordered by its terminal and lateral traces. -/
theorem cone_bounded_subsolution_comparison {d : ℕ} {lam Lam : ℝ}
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (a T : ℝ) (haT : a < T) (v₀ : PDE.Vec d) (R : ℝ)
    (u : KineticPoint d → ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ (KineticPoint.equivProd d).symm)
      ((KineticPoint.equivProd d) '' localStrip a T v₀ R))
    (he : ∀ P ∈ localStrip a T v₀ R,
      0 ≤ forwardKineticOperator (ofTimeVelocityCoefficient B) u P)
    (hc : ContinuousOn u (localClosedStrip a T v₀ R))
    (hb : ∃ M : ℝ, ∀ P ∈ localClosedStrip a T v₀ R, |u P| ≤ M)
    (c : ℝ) (htr : ∀ P ∈ localTrace a T v₀ R, u P ≤ c) :
    ∀ P ∈ localClosedStrip a T v₀ R, u P ≤ c := by
  obtain ⟨M, hM⟩ := hb
  have hopen : ∀ P ∈ localStrip a T v₀ R, u P ≤ c := by
    intro P hP
    let s := (a + P.time) / 2
    have has : a < s := by dsimp [s]; linarith only [hP.1]
    have hsP : s < P.time := by dsimp [s]; linarith only [hP.1]
    have hmclosed : MapsTo sectionTwoPoint
        (movingClosedSlab (PDE.euclideanBall v₀ R) (fun _ => 0) s T)
        (localClosedStrip a T v₀ R) := by
      intro Q hQ
      refine ⟨has.le.trans hQ.1, hQ.2.1, ?_⟩
      simpa only [mem_closure_movingDomain_iff, sub_zero, sectionTwoPoint] using hQ.2.2
    have hmactive : MapsTo sectionTwoPoint
        (movingActiveSlab (PDE.euclideanBall v₀ R) (fun _ => 0) s T)
        (localStrip a T v₀ R) := by
      intro Q hQ
      refine ⟨has.trans_le hQ.1, hQ.2.1, ?_⟩
      simpa only [mem_movingDomain_iff, PDE.mem_translateSet_iff_sub_mem, sub_zero,
        sectionTwoPoint] using hQ.2.2
    have hreg (Q : KineticPoint d)
        (hQ : Q ∈ movingActiveSlab (PDE.euclideanBall v₀ R) (fun _ => 0) s T) :
        IsSliceRegularAt (u ∘ sectionTwoPoint) Q :=
      boundary_swapped_slice_regular (isOpen_localStrip a T v₀ R) hu Q (hmactive hQ)
    have hmax := growth_comparison (PDE.isOpen_euclideanBall v₀ R) continuous_const
      hB.1 (sectionTwoCoefficient_fullBounds lam Lam B hB).2.2
      (identityDrift_bounds d).1 (le_refl 0) zero_le_one
      (a := s) (T := T) (u := fun Q => u (sectionTwoPoint Q) - c)
      ⟨M + |c|, fun Q hQ => by
        have hbQ := le_of_abs_le (hM _ (hmclosed hQ))
        have hcc := neg_le_abs c
        linarith only [hbQ, hcc]⟩
      ((hc.comp (continuous_sectionTwoPoint d).continuousOn hmclosed).sub continuousOn_const)
      (fun Q hQ => (hreg Q hQ).sub (IsSliceRegularAt.const c Q))
      (fun Q hQ => by
        change 0 ≤ viscousTransportedOperator (zIndependentCoefficient B) (identityDrift d) 0
          (fun Q => (u ∘ sectionTwoPoint) Q - (fun _ : KineticPoint d => c) Q) Q
        rw [viscousTransportedOperator_sub (hreg Q hQ) (IsSliceRegularAt.const c Q),
          viscousTransportedOperator_zero, viscousTransportedOperator_const]
        have hop := he _ (hmactive hQ)
        rw [forwardKineticOperator_eq_lop_identity] at hop
        change 0 ≤ transportedForwardOperator (zIndependentCoefficient B) (identityDrift d)
          (u ∘ sectionTwoPoint) Q at hop
        simpa only [sub_zero] using hop)
      (fun Q hQ hqt => by
        apply sub_nonpos.mpr
        apply htr
        refine Or.inl ⟨hqt, ?_⟩
        exact (hmclosed hQ).2.2)
      (fun Q hQ hqv => by
        apply sub_nonpos.mpr
        apply htr
        refine Or.inr ⟨(hmclosed hQ).1, (hmclosed hQ).2.1, ?_⟩
        simpa only [movingDomain, PDE.translateSet_zero, sectionTwoPoint] using hqv)
    have hQ : sectionTwoPoint P ∈
        movingClosedSlab (PDE.euclideanBall v₀ R) (fun _ => 0) s T := by
      refine ⟨hsP.le, hP.2.1.le, ?_⟩
      simpa only [mem_closure_movingDomain_iff, sub_zero, sectionTwoPoint] using
        subset_closure hP.2.2
    exact sub_nonpos.mp (hmax _ hQ)
  have hcl := le_on_closure hopen
    (by rwa [closure_localStrip haT]) continuousOn_const
  intro P hP
  exact hcl (by rwa [closure_localStrip haT])

end HypoellipticAleksandrov.KineticAleksandrov.LocalA

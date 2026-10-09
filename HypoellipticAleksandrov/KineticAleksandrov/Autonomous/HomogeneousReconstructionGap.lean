module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionNative

/-! # Comparison of smooth homogeneous solutions against a genuine spatial tail barrier -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set HypoellipticAleksandrov Parabolic
open SectionTwo TheoremA Evolution

/-- Growth comparison controls a homogeneous solution gap by its actual exit discrepancy. -/
theorem reconstruction_homogeneous_gap_le_barrier
    {lam Lam : ℝ} (hlam : 0 < lam) (A : SmoothAutonomous lam Lam)
    (H : Interval) (lower T : ℝ) (e : StripPole H (T : WithTop ℝ)) (he : lower < e.1.time)
    (u v : Point → ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ (KineticPoint.equivProd 1).symm)
      (KineticPoint.equivProd 1 '' reconstructionStrip H lower T))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (v ∘ (KineticPoint.equivProd 1).symm)
      (KineticPoint.equivProd 1 '' reconstructionStrip H lower T))
    (huop : ∀ p ∈ reconstructionStrip H lower T, forwardScalarOperator A.a u p = 0)
    (hvop : ∀ p ∈ reconstructionStrip H lower T, forwardScalarOperator A.a v p = 0)
    (huc : ContinuousOn u (reconstructionStrip H lower T ∪ reconstructionExit H lower T))
    (hvc : ContinuousOn v (reconstructionStrip H lower T ∪ reconstructionExit H lower T))
    (Mu Mv : ℝ)
    (hub : ∀ p ∈ reconstructionClosedSlab H e.1.time T, |u p| ≤ Mu)
    (hvb : ∀ p ∈ reconstructionClosedSlab H e.1.time T, |v p| ≤ Mv)
    (eps : ℝ) (q : Point → ℝ) (hqc : Continuous q)
    (hqr : ∀ p, IsSliceRegularAt q p) (hqn : ∀ p, 0 ≤ q p)
    (hqo : ∀ p ∈ evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T,
      transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1) q p ≤ 0)
    (hbd : ∀ p ∈ stripClosedExit H T, e.1.time ≤ p.time →
      u p - v p ≤ eps + q (sectionTwoPoint p)) :
    u e.1 - v e.1 ≤ eps + q (sectionTwoPoint e.1) := by
  let a := e.1.time
  have hact : ∀ p ∈ movingActiveSlab (intervalDomain H) (fun _ => 0) a T,
      sectionTwoPoint p ∈ reconstructionStrip H lower T := by
    intro p hp
    refine ⟨he.trans_le hp.1, hp.2.1, ?_⟩
    simpa only [mem_movingDomain_iff, PDE.mem_translateSet_iff_sub_mem, sub_zero,
      intervalDomain, PDE.mem_oneDimensionalAxisBox_iff, PDE.vecOneCoordinate, Interval.carrier,
      sectionTwoPoint] using hp.2.2
  have hslab : ∀ p ∈ movingClosedSlab (intervalDomain H) (fun _ => 0) a T,
      sectionTwoPoint p ∈ reconstructionClosedSlab H a T := by
    intro p hp
    change a ≤ p.time ∧ p.time ≤ T ∧ p.position 0 ∈ Icc H.lo H.hi
    exact ⟨hp.1, hp.2.1, intervalDomain_closure_bounds H (by
      simpa only [mem_closure_movingDomain_iff, sub_zero] using hp.2.2)⟩
  have hur (p : Point) (hp : p ∈ movingActiveSlab (intervalDomain H) (fun _ => 0) a T) :=
    reconstruction_physical_slice_regular H lower T u hu p (hact p hp)
  have hvr (p : Point) (hp : p ∈ movingActiveSlab (intervalDomain H) (fun _ => 0) a T) :=
    reconstruction_physical_slice_regular H lower T v hv p (hact p hp)
  have huc' := huc.comp (continuous_sectionTwoPoint 1).continuousOn
    (reconstruction_closedSlab_mapsTo H he)
  have hvc' := hvc.comp (continuous_sectionTwoPoint 1).continuousOn
    (reconstruction_closedSlab_mapsTo H he)
  have hmax := growth_comparison
    (isOpen_of_isAdmissibleEvolutionDomain (intervalDomain_admissible H)) continuous_const
    hlam (evolutionCoefficient_bounds A) (identityDrift_bounds 1).1
    (le_refl 0) zero_le_one (a := a) (T := T)
    (u := fun p => (u (sectionTwoPoint p) - v (sectionTwoPoint p) - eps) - q p)
    ⟨Mu + Mv + |eps|, fun p hp => by
      have h1 := (le_abs_self _).trans (hub _ (hslab p hp))
      have h2 := (neg_le_abs _).trans (hvb _ (hslab p hp))
      have h3 := neg_le_abs eps
      have h4 := hqn p
      linarith⟩
    (((huc'.sub hvc').sub continuousOn_const).sub hqc.continuousOn)
    (fun p hp => ((hur p hp).sub (hvr p hp) |>.sub (IsSliceRegularAt.const eps p)).sub (hqr p))
    (fun p hp => by
      change 0 ≤ viscousTransportedOperator (evolutionCoefficient A.a) (identityDrift 1) 0
        (fun y => ((u ∘ sectionTwoPoint) y - (v ∘ sectionTwoPoint) y -
          (fun _ : Point => eps) y) - q y) p
      rw [viscousTransportedOperator_sub
        ((hur p hp).sub (hvr p hp) |>.sub (IsSliceRegularAt.const eps p)) (hqr p),
        viscousTransportedOperator_sub ((hur p hp).sub (hvr p hp)) (IsSliceRegularAt.const eps p),
        viscousTransportedOperator_sub (hur p hp) (hvr p hp),
        viscousTransportedOperator_zero, viscousTransportedOperator_zero,
        reconstruction_scalar_operator_swap, reconstruction_scalar_operator_swap,
        huop _ (hact p hp), hvop _ (hact p hp), viscousTransportedOperator_const,
        viscousTransportedOperator_zero]
      have hh := hqo p ⟨hp.2.1, hp.2.2⟩
      linarith)
    (fun p hp hpt => by
      have hvel := intervalDomain_closure_bounds H (by
        simpa only [mem_closure_movingDomain_iff, sub_zero] using hp.2.2)
      have hh := hbd (sectionTwoPoint p) (Or.inl ⟨hpt, hvel⟩) hp.1
      change (u (sectionTwoPoint p) - v (sectionTwoPoint p) - eps) - q p ≤ 0
      rw [sectionTwoPoint_involutive] at hh
      linarith)
    (fun p hp hpf => by
      have hvel := reconstruction_interval_frontier_eq H (by
        simpa only [movingDomain, PDE.translateSet_zero] using hpf)
      have hh := hbd (sectionTwoPoint p) (Or.inr ⟨hp.2.1, hvel⟩) hp.1
      rw [sectionTwoPoint_involutive] at hh
      linarith)
  have hp : sectionTwoPoint e.1 ∈ movingClosedSlab (intervalDomain H) (fun _ => 0) a T :=
    ⟨le_rfl, (WithTop.coe_lt_coe.mp e.2.1).le, subset_closure (stripPoleState H T e).2.1⟩
  have hh := hmax _ hp
  rw [sectionTwoPoint_involutive] at hh
  linarith

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

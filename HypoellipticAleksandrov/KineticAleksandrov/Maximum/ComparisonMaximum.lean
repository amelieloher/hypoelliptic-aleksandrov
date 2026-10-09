module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonFaces
import Mathlib.Topology.Order.Compact
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCalculus

/-! # The classical operator at a closed-cylinder maximum outside the exit faces -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov.Parabolic Filter Set
open scoped Topology

/-- The velocity of a non-exit point is strictly inside the velocity ball. -/
theorem comparison_velocity_interior {d : ℕ}
    (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) {P : KineticPoint d}
    (hP : P ∈ closure (forwardCylinder Z₀ R hR))
    (hnot : P ∉ exitBoundary Z₀ R hR) :
    P.velocity ∈ PDE.euclideanBall Z₀.velocity R := by
  have hb := (closure_forwardCylinder_bounds Z₀ R hR hP).2.2
  change PDE.vecNormSq (P.velocity - Z₀.velocity - 0) ≤ R ^ 2 at hb
  simp only [sub_zero] at hb
  change PDE.vecNormSq (P.velocity - Z₀.velocity) < R ^ 2
  apply lt_of_le_of_ne hb
  intro heq
  apply hnot ((mem_exitBoundary_iff Z₀ P R hR).2 ⟨hP,Or.inr (Or.inl ?_)⟩)
  exact heq

/-- At a non-exit closed-cylinder maximum, transport plus diffusion is nonpositive.
Only the source anisotropic regularity on an open neighbourhood is used. -/
theorem comparison_operator_nonpos_at_max {d : ℕ}
    (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    {D : Set (KineticPoint d)} (hD : IsOpen D)
    (hQD : closure (forwardCylinder Z₀ R hR) ⊆ D)
    {u : KineticPoint d → ℝ} (hu : IsKineticC112On u D)
    (A : FullKineticCoefficient d) {P : KineticPoint d}
    (hP : P ∈ closure (forwardCylinder Z₀ R hR))
    (hnot : P ∉ exitBoundary Z₀ R hR)
    (hmax : IsMaxOn u (closure (forwardCylinder Z₀ R hR)) P)
    (hA : (A P.time P.position P.velocity).PosSemidef) :
    forwardKineticOperator A u P ≤ 0 := by
  have htransport := hasDerivAt_freeTransport hD hu (hQD hP)
  obtain ⟨η,hη,hstay⟩ := comparison_freeTransport_stays Z₀ R hR hP hnot
  have hmaxTransport : ∀ᶠ h in 𝓝 (0 : ℝ), 0 ≤ h →
      u ⟨P.time + h,P.position + h • P.velocity,P.velocity⟩ ≤
        u ⟨P.time + 0,P.position + (0 : ℝ) • P.velocity,P.velocity⟩ := by
    filter_upwards [Iio_mem_nhds hη] with h hh hhn
    simpa only [mem_ofPred_eq,add_zero,zero_smul] using hmax (hstay h hhn hh)
  have ht := deriv_nonpos_of_future_localMax htransport.differentiableAt hmaxTransport
  rw [htransport.deriv] at ht
  have hv : IsLocalMax (fun v => u ⟨P.time,P.position,v⟩) P.velocity := by
    have hpv := comparison_velocity_interior Z₀ R hR hP hnot
    filter_upwards [(PDE.isOpen_euclideanBall Z₀.velocity R).mem_nhds hpv] with v hv
    apply hmax
    rw [comparison_closure_forwardCylinder_eq]
    have hb := closure_forwardCylinder_bounds Z₀ R hR hP
    change (Z₀.time ≤ P.time ∧ P.time ≤ Z₀.time + R ^ 2) ∧
      relativePosition Z₀ P ∈ PDE.euclideanClosedBall 0 (R ^ 3) ∧
      v - Z₀.velocity ∈ PDE.euclideanClosedBall 0 R
    refine ⟨hb.1,hb.2.1,?_⟩
    have hclosed := PDE.euclideanBall_subset_euclideanClosedBall _ _ hv
    simpa only [PDE.euclideanClosedBall, PDE.euclideanSqDist, mem_ofPred_eq, sub_zero] using hclosed
  have hdiff := matrixContraction_sliceHessian_nonpos_of_localMax
    (hu.velocitySlice_contDiffAt (hQD hP)) hv hA
  rw [forwardKineticOperator_apply, kineticVelocityHessian_eq_sliceHessian]
  exact add_nonpos ht hdiff

/-- A positive maximum of a strict subsolution is on the exit boundary. -/
theorem comparison_inner_maximum_exclusion {d : ℕ}
    (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    {D : Set (KineticPoint d)} (hD : IsOpen D)
    (hQD : closure (forwardCylinder Z₀ R hR) ⊆ D)
    {u : KineticPoint d → ℝ} (hu : IsKineticC112On u D)
    (A : FullKineticCoefficient d)
    (hA : ∀ P ∈ D, (A P.time P.position P.velocity).PosSemidef)
    (hstrict : ∀ P ∈ D, 0 < u P → 0 < forwardKineticOperator A u P)
    {P : KineticPoint d} (hP : P ∈ closure (forwardCylinder Z₀ R hR))
    (hmax : IsMaxOn u (closure (forwardCylinder Z₀ R hR)) P) (hpos : 0 < u P) :
    P ∈ exitBoundary Z₀ R hR := by
  by_contra hnot
  exact (not_le.mpr (hstrict P (hQD hP) hpos))
    (comparison_operator_nonpos_at_max Z₀ R hR hD hQD hu A hP hnot hmax (hA P (hQD hP)))

end HypoellipticAleksandrov.KineticAleksandrov

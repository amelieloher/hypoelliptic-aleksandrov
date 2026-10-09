module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SmoothAutonomousP6Statement
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FullCoefficientAdapters
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Growth.MacroscopicPropagationPhysical
import HypoellipticAleksandrov.KineticAleksandrov.Holder.OscillationContractionGeometry
import Mathlib.Tactic

/-! # One radius doubling in the return-time propagation argument

The macroscopic propagation theorem supplies a uniform loss at each doubling.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic Set MeasureTheory Holder Holder.Growth

/-- The homogeneous solutions used for propagation live on the full positive-time slab. -/
def IsNonnegativeHomogeneousSolution {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (u : Point → ℝ) : Prop :=
  (∃ M : ℝ, ∀ p, 0 < p.time → |u p| ≤ M) ∧
    (∀ p, 0 < p.time → 0 ≤ u p) ∧
    IsKineticC112On u {p | 0 < p.time} ∧
    (∀ p, 0 < p.time → autonomousScalarOperator A.a u p = 0)

/-- The later cylinder follows the same transport centre and doubles the radius. -/
def returnDoubleCenter (z : Point) (ell : ℝ) : Point :=
  ⟨z.time + 8 * ell ^ 2, z.position + (8 * ell ^ 2) • z.velocity, z.velocity⟩

/-- Smooth autonomous scalar coefficients satisfy the full ellipticity predicate. -/
theorem autonomous_fullElliptic {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) :
    FullElliptic lam Lam (autonomousCoefficient A.a) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hc : Continuous (fullKineticCoefficientAt (autonomousCoefficient A.a)) := by
      apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      exact A.smooth.continuous.comp
        ((continuous_apply 0 |>.comp continuous_position).prodMk
          (continuous_apply 0 |>.comp continuous_velocity))
    exact hc.measurable
  · intro p
    exact autonomousCoefficient_symmetric A.a p.time p.position p.velocity
  · exact Filter.Eventually.of_forall fun p =>
      (autonomousCoefficient_bounds A p.time p.position p.velocity).1
  · exact Filter.Eventually.of_forall fun p =>
      (autonomousCoefficient_bounds A p.time p.position p.velocity).2

/-- The p-six hypothesis supplies admissibility on the positive-time slab. -/
theorem return_solution_admissible {lam Lam : ℝ}
    (hp6 : SmoothAutonomousP6Statement lam Lam) :
    ∃ C_A : ℝ, 0 < C_A ∧ ∀ (A : SmoothAutonomous lam Lam) (u : Point → ℝ),
      IsNonnegativeHomogeneousSolution A u →
      IsAdmissibleSolution (autonomousCoefficient A.a) {p | 0 < p.time} 6 C_A u := by
  obtain ⟨C_A, hC, h⟩ := hp6
  refine ⟨C_A, hC, ?_⟩
  intro A u hu
  exact h A _ (isOpen_lt continuous_const continuous_time) u hu.2.2.1
    (ae_restrict_of_forall_mem (measurableSet_lt measurable_const continuous_time.measurable)
      (fun p hp => hu.2.2.2 p hp))

/-- Each sufficiently small doubling loses the same factor, uniformly over its radius. -/
theorem return_patch_double (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hp6 : SmoothAutonomousP6Statement lam Lam) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (A : SmoothAutonomous lam Lam) (u : Point → ℝ),
      IsNonnegativeHomogeneousSolution A u → ∀ (z : Point) (ell k : ℝ),
      0 < ell → 12 * ell ^ 2 < z.time → 0 ≤ k →
      (∀ p ∈ backwardCylinder z ell, k ≤ u p) →
      ∀ p ∈ backwardCylinder (returnDoubleCenter z ell) (2 * ell), c * k ≤ u p := by
  obtain ⟨c, hc, hc1, hmacro⟩ := exists_physical_macroscopic_cap_constant
    1 (by omega) lam Lam hlam hLam 0 (1 / 4) (by norm_num) (by norm_num)
  obtain ⟨C_A, _hC, hadm⟩ := return_solution_admissible hp6
  refine ⟨c, hc, hc1, ?_⟩
  intro A u hu z ell k hell htime hk hpatch p hp
  let z' := returnDoubleCenter z ell
  have hscale : 0 < 2 * ell := by positivity
  have hcenter : kineticAffine z' (2 * ell) (samplingCenter 1 0) = z := by
    ext i <;> simp [z', returnDoubleCenter, kineticAffine, samplingCenter] <;> ring
  have hregion : closure (kineticAffine z' (2 * ell) ''
      referenceRegion 1 0 (referenceBound 0)) ⊆ {p | 0 < p.time} := by
    have hclosed : IsClosed {p : Point | z.time - 12 * ell ^ 2 ≤ p.time} :=
      isClosed_le continuous_const continuous_time
    have hsub : kineticAffine z' (2 * ell) '' referenceRegion 1 0 (referenceBound 0) ⊆
        {p : Point | z.time - 12 * ell ^ 2 ≤ p.time} := by
      rintro _ ⟨q, hq, rfl⟩
      have ht : -5 < q.time := by simpa only [Nat.cast_zero, zero_add] using hq.1
      change z.time - 12 * ell ^ 2 ≤ z.time + 8 * ell ^ 2 + (2 * ell) ^ 2 * q.time
      nlinarith [sq_nonneg ell]
    intro q hq
    have hq' := closure_minimal hsub hclosed hq
    change z.time - 12 * ell ^ 2 ≤ q.time at hq'
    change 0 < q.time
    linarith
  apply hmacro 6 C_A (by norm_num) _ (autonomous_fullElliptic A) z' (2 * ell) hscale
    _ (isOpen_lt continuous_const continuous_time) hregion u
    (fun q hq => hu.2.1 q hq) (hadm A u hu).1 z ell k hell (by linarith)
    (by rw [hcenter]; exact backwardCylinder_radius_mono z hell (by linarith)) hk
    (fun q hq => hpatch q ?_) p hp
  rcases hq with ⟨q, hq, rfl⟩
  exact (kineticAffine_mem_cylinder z q hell).mpr
    ((cap_subset_closedCap 1).trans (closedCap_subset_unitCylinder 1) hq)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

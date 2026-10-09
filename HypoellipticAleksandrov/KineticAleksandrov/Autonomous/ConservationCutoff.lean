module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FullSpaceIdentification
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.MarginalCutoffLimit
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierBound

/-! # Compact terminal cutoffs and the classical constant full-space solution -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

/-- A compact scalar cutoff in the diffused coordinate. -/
def conservationVelocityDatum (N : ℕ) : BoundedBorel (PDE.Vec 1) :=
  ⟨zCutoffN 1 N, (contDiff_zCutoffN 1 N).continuous.measurable,
    ⟨1, zero_le_one, fun v => by
      rw [abs_of_nonneg (zCutoffN_mem_Icc 1 N v).1]
      exact (zCutoffN_mem_Icc 1 N v).2⟩⟩

/-- Cut off both velocity and position for the constant terminal datum. -/
def conservationDatum (N : ℕ) : BoundedBorel (EvolutionAmbientState 1) :=
  cutoffDatum (conservationVelocityDatum N) N

/-- Conservation cutoffs take values in the unit interval. -/
theorem conservationDatum_bounds (N : ℕ) (x : EvolutionAmbientState 1) :
    0 ≤ conservationDatum N x ∧ conservationDatum N x ≤ 1 := by
  change 0 ≤ zCutoffN 1 N x.1 * zCutoffN 1 N x.2 ∧ _
  exact ⟨mul_nonneg (zCutoffN_mem_Icc 1 N x.1).1 (zCutoffN_mem_Icc 1 N x.2).1,
    (mul_le_mul (zCutoffN_mem_Icc 1 N x.1).2 (zCutoffN_mem_Icc 1 N x.2).2
      (zCutoffN_mem_Icc 1 N x.2).1 zero_le_one).trans (by norm_num)⟩

/-- The cutoffs are admitted compact terminal data on the full domain. -/
theorem conservationDatum_smoothCompact (N : ℕ) (τ : ℝ) :
    IsSmoothCompactTerminalDatum autonomousWholeDomain (fun _ => 0) τ
      (conservationDatum N) := by
  apply cutoffDatum_isSmoothCompact
  refine ⟨contDiff_zCutoffN 1 N, hasCompactSupport_zCutoffN 1 N, ?_⟩
  intro v _
  change v ∈ movingDomain (wholeSpace 1) (fun _ => 0) τ
  rw [movingDomain_wholeSpace]
  trivial

/-- The terminal deficit has a vanishing quadratic-tail bound. -/
theorem conservationDatum_deficit (N : ℕ) (x : EvolutionAmbientState 1) :
    1 - conservationDatum N x ≤ ((N : ℝ) + 1)⁻¹ ^ 2 *
      (1 + PDE.vecNormSq x.1 + PDE.vecNormSq x.2) := by
  have hR : 0 < (N : ℝ) + 1 := by positivity
  have hx1 := PDE.vecNormSq_nonneg x.1
  have hx2 := PDE.vecNormSq_nonneg x.2
  by_cases hy : ‖x.1‖ ≤ (N : ℝ) + 1
  · by_cases hz : ‖x.2‖ ≤ (N : ℝ) + 1
    · change 1 - zCutoffN 1 N x.1 * zCutoffN 1 N x.2 ≤ _
      rw [zCutoffN_eq_one hy, zCutoffN_eq_one hz]
      norm_num only [one_mul, sub_self]
      positivity
    · have hs := sq_lt_vecNormSq_of_lt_norm hR.le (lt_of_not_ge hz)
      apply (sub_le_self _ (conservationDatum_bounds N x).1).trans
      rw [inv_pow, ← div_eq_inv_mul, le_div_iff₀ (sq_pos_of_pos hR)]
      linarith
  · have hs := sq_lt_vecNormSq_of_lt_norm hR.le (lt_of_not_ge hy)
    apply (sub_le_self _ (conservationDatum_bounds N x).1).trans
    rw [inv_pow, ← div_eq_inv_mul, le_div_iff₀ (sq_pos_of_pos hR)]
    linarith

/-- A bounded constant datum is an actual classical solution on the full domain. -/
theorem fullspace_constant_solution (B : FullKineticCoefficient 1)
    (b : PDE.Vec 1 → PDE.Vec 1) (τ c : ℝ) :
    IsClassicalTerminalSolution autonomousWholeDomain (fun _ => 0) B b τ
      (BoundedBorel.const c) (fun _ => c) := by
  refine ⟨⟨|c|, abs_nonneg c, fun _ _ => le_rfl⟩, continuousOn_const,
    contDiffOn_const, ?_, fun _ _ => rfl, ?_⟩
  · intro p _
    rw [← viscousTransportedOperator_zero, viscousTransportedOperator_const]
  · intro p hp
    have h := hp.2
    change p.position ∈ frontier (movingDomain (wholeSpace 1) (fun _ => 0) p.time) at h
    rw [movingDomain_wholeSpace, frontier_univ] at h
    exact False.elim h

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

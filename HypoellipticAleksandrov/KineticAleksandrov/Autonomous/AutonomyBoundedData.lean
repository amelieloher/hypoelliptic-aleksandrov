module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.Autonomy
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ConservationBoundedLimit
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierBound

/-! # Classical full-space kernel representation for bounded smooth terminal data -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set MeasureTheory Filter
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped Topology

/-- Every bounded smooth datum has a classical solution represented by the supplied kernel. -/
theorem fullspace_bounded_smooth_solution
    (hH : HormanderHypoellipticityStatement) {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState 1))
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ∃ u : KineticPoint 1 → ℝ,
      IsClassicalTerminalSolution autonomousWholeDomain (fun _ => 0)
        (evolutionCoefficient A.a) (identityDrift 1) τ F u ∧
      ∀ q : EvolutionQuery autonomousWholeDomain (fun _ => 0), q.1.2.1 = τ →
        u ⟨q.1.1, q.1.2.2.1, q.1.2.2.2⟩ = ∫ x, F x ∂E.2.master q := by
  obtain ⟨C, hC0, hC⟩ := F.exists_bound
  choose v hv hvr _ using fun N =>
    hE.1 τ (boundedConservationDatum F N) (boundedConservationDatum_smoothCompact F hF N τ)
  have hb (N : ℕ) : ∀ p ∈
      evolutionPastClosedCylinder autonomousWholeDomain (fun _ => 0) τ, |v N p| ≤ C :=
    classical_abs_le_const
      (isOpen_of_isAdmissibleEvolutionDomain autonomousWholeDomain_admissible)
      continuous_const hlam (evolutionCoefficient_bounds A) (identityDrift_bounds 1).1
      le_rfl zero_le_one
      ((isClassicalViscousTerminalSolution_zero_iff _ _ _ _ _ _ _).2 (hv N))
      (boundedConservationDatum_bound F hC N)
  obtain ⟨u, hulim, hu⟩ := exists_bounded_fullspace_classical_limit hH hlam hLam A
    τ F C hC0 hC v hv hb
  refine ⟨u, hu, ?_⟩
  intro q hqτ
  let p : KineticPoint 1 := ⟨q.1.1, q.1.2.2.1, q.1.2.2.2⟩
  have hp : p ∈ evolutionPastClosedCylinder autonomousWholeDomain (fun _ => 0) τ :=
    ⟨hqτ ▸ q.2.1, subset_closure q.2.2.1⟩
  have heq (N : ℕ) : v N p = ∫ x, boundedConservationDatum F N x ∂E.2.master q := by
    let s : EvolutionState autonomousWholeDomain (fun _ => 0) q.1.1 :=
      ⟨q.1.2.2, q.2.2⟩
    have hr := hvr N q.1.1 (hqτ ▸ q.2.1) s
    have hi := hE.2.1 q.1.1 τ (hqτ ▸ q.2.1) s
      (terminalStateDatum (boundedConservationDatum F N))
    have hm := integral_master_eq_fiber E.2 autonomousWholeDomain_measurable
      q.1.1 τ (hqτ ▸ q.2.1) s (boundedConservationDatum F N)
      (boundedConservationDatum F N).measurable
    subst τ
    exact hr.trans (hi.trans hm.symm)
  have : IsFiniteMeasure (E.2.master q) :=
    ⟨(E.2.mass_le_one q).trans_lt ENNReal.one_lt_top⟩
  have ht : Tendsto (fun N => ∫ x, boundedConservationDatum F N x ∂E.2.master q)
      atTop (𝓝 (∫ x, F x ∂E.2.master q)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun N => (boundedConservationDatum F N).measurable.aestronglyMeasurable)
      (integrable_const C) (fun N => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_)
    · rw [Real.norm_eq_abs]
      exact boundedConservationDatum_bound F hC N x
    · obtain ⟨N₀, hN₀⟩ := exists_nat_ge (max ‖x.1‖ ‖x.2‖)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop N₀] with N hN
      have hn : (N₀ : ℝ) ≤ N := by exact_mod_cast hN
      change F x = F x * (zCutoffN 1 N x.1 * zCutoffN 1 N x.2)
      have hy : ‖x.1‖ ≤ (N : ℝ) + 1 := by
        have := le_max_left ‖x.1‖ ‖x.2‖; linarith
      have hz : ‖x.2‖ ≤ (N : ℝ) + 1 := by
        have := le_max_right ‖x.1‖ ‖x.2‖; linarith
      rw [zCutoffN_eq_one hy, zCutoffN_eq_one hz, mul_one, mul_one]
  exact tendsto_nhds_unique ((hulim p hp).congr heq) ht

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

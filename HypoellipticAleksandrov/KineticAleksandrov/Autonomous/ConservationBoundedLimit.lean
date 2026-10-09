module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ConservationBoundedCutoff
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ClassicalTerminalWeak
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExternalRegularity

/-! # Classical regularity of the bounded full-space cutoff limit -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Filter Set MeasureTheory Evolution
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped Topology MatrixOrder

/-- The cutoff limit for arbitrary bounded full-space terminal data is an actual classical
solution. Its compact approximating solutions are supplied by the realization. -/
theorem exists_bounded_fullspace_classical_limit
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam)
    (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState 1)) (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, |F x| ≤ C)
    (u : ℕ → KineticPoint 1 → ℝ)
    (hu : ∀ N, IsClassicalTerminalSolution autonomousWholeDomain (fun _ => 0)
      (evolutionCoefficient A.a) (identityDrift 1) τ (boundedConservationDatum F N) (u N))
    (hbd : ∀ N, ∀ p ∈ evolutionPastClosedCylinder autonomousWholeDomain (fun _ => 0) τ, |u N p| ≤
      C) :
    ∃ V : KineticPoint 1 → ℝ,
      (∀ p ∈ evolutionPastClosedCylinder autonomousWholeDomain (fun _ => 0) τ, Tendsto (fun N => u
        N p) atTop (𝓝 (V p))) ∧
      IsClassicalTerminalSolution autonomousWholeDomain (fun _ => 0) (evolutionCoefficient A.a)
        (identityDrift 1) τ F V := by
  let : SecondCountableTopology (KineticPoint 1) :=
    (KineticPoint.homeomorphProd 1).isEmbedding.secondCountableTopology
  have hΩo := isOpen_of_isAdmissibleEvolutionDomain autonomousWholeDomain_admissible
  let S := evolutionPastClosedCylinder autonomousWholeDomain (fun _ => 0) τ
  let U := evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) τ
  have hU : IsOpen U := isOpen_evolutionPastOpenCylinder hΩo continuous_const τ
  have hUS : U ⊆ S := fun p hp => ⟨hp.1.le, subset_closure hp.2⟩
  obtain ⟨Ct, _hCt0, hCt⟩ := classical_sub_le_growthBarrier hΩo continuous_const hlam
    (evolutionCoefficient_bounds A) (identityDrift_bounds 1).1
  -- tail bound
  have hTail : ∀ N M : ℕ, N ≤ M → ∀ p ∈ S,
      |u M p - u N p| ≤ (2 * C) / ((N : ℝ) + 1) ^ 2 * growthBarrier Ct τ p := by
    intro N M hNM p hp
    have hc : 0 ≤ (2 * C) / ((N : ℝ) + 1) ^ 2 := by positivity
    have h1 := hCt τ (boundedConservationDatum F M) (boundedConservationDatum F N) (u M) (u N) _
      hc (hu M) (hu N)
      (fun x _ => (le_abs_self _).trans (boundedConservationDatum_sub F hC0 hC hNM x)) p hp
    have h2 := hCt τ (boundedConservationDatum F N) (boundedConservationDatum F M) (u N) (u M) _
      hc (hu N) (hu M)
      (fun x _ => by
        exact (le_abs_self _).trans (by
          rw [abs_sub_comm]
          exact boundedConservationDatum_sub F hC0 hC hNM x)) p hp
    rw [abs_le]
    constructor <;> linarith
  have hlimex : ∀ p ∈ S, ∃ v, Tendsto (fun N => u N p) atTop (𝓝 v) := fun p hp =>
    cauchySeq_tendsto_of_complete (cauchySeq_of_quadratic_tail
      (K := (2 * C) * growthBarrier Ct τ p) (fun N M hNM => by
        have := hTail N M hNM p hp
        rwa [div_mul_eq_mul_div] at this))
  let V : KineticPoint 1 → ℝ := fun p => limUnder atTop (fun N => u N p)
  have hV : ∀ p ∈ S, Tendsto (fun N => u N p) atTop (𝓝 (V p)) := fun p hp =>
    tendsto_nhds_limUnder (hlimex p hp)
  -- the limit is bounded and satisfies the tail bound
  have hVbd : ∀ p ∈ S, |V p| ≤ C := fun p hp =>
    le_of_tendsto' ((hV p hp).abs) (fun N => hbd N p hp)
  have hVtail : ∀ N : ℕ, ∀ p ∈ S,
      |V p - u N p| ≤ (2 * C) / ((N : ℝ) + 1) ^ 2 * growthBarrier Ct τ p := by
    intro N p hp
    refine le_of_tendsto ((hV p hp).sub_const (u N p) |>.abs) ?_
    filter_upwards [eventually_ge_atTop N] with M hM
    exact hTail N M hM p hp
  -- continuity on the closed cylinder
  have hcont : ContinuousOn V S := by
    have hloc : TendstoLocallyUniformlyOn (fun N => u N) V atTop S := by
      rw [Metric.tendstoLocallyUniformlyOn_iff]
      intro ε hε x hx
      refine ⟨S ∩ {q | growthBarrier Ct τ q < growthBarrier Ct τ x + 1}, ?_, ?_⟩
      · exact inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds
          ((continuous_growthBarrier Ct τ).continuousAt.eventually_lt continuousAt_const
            (lt_add_one _) |>.mono fun q hq => hq))
      · have hlim := tendsto_quadratic_tail ((2 * C) * (growthBarrier Ct τ x + 1))
        filter_upwards [hlim.eventually (gt_mem_nhds hε)] with N hN y hy
        rw [Real.dist_eq]
        have h1 := hVtail N y hy.1
        have h2 : (2 * C) / ((N : ℝ) + 1) ^ 2 * growthBarrier Ct τ y ≤
            (2 * C) * (growthBarrier Ct τ x + 1) / ((N : ℝ) + 1) ^ 2 := by
          rw [div_mul_eq_mul_div]
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hy.2.le (by positivity : 0 ≤ 2 * C)
        linarith
    exact hloc.continuousOn (Eventually.of_forall fun N => (hu N).2.1).frequently
  -- terminal and lateral values
  have hterm : ∀ p ∈ evolutionTerminalClosure autonomousWholeDomain (fun _ => 0) τ,
      V p = F (p.position, p.velocity) := by
    intro p hp
    have hpS : p ∈ S := ⟨hp.1.le, hp.1 ▸ hp.2⟩
    refine tendsto_nhds_unique (hV p hpS) ?_
    refine tendsto_const_nhds.congr' ?_
    obtain ⟨N₀, hN₀⟩ := exists_nat_ge (max ‖p.position‖ ‖p.velocity‖)
    filter_upwards [eventually_ge_atTop N₀] with N hN
    have hn : (N₀ : ℝ) ≤ N := by exact_mod_cast hN
    have hy : ‖p.position‖ ≤ (N : ℝ) + 1 := by
      have := le_max_left ‖p.position‖ ‖p.velocity‖; linarith
    have hz : ‖p.velocity‖ ≤ (N : ℝ) + 1 := by
      have := le_max_right ‖p.position‖ ‖p.velocity‖; linarith
    rw [(hu N).2.2.2.2.1 p hp]
    change F (p.position, p.velocity) =
      F (p.position, p.velocity) *
        (zCutoffN 1 N p.position * zCutoffN 1 N p.velocity)
    rw [zCutoffN_eq_one hy, zCutoffN_eq_one hz, mul_one, mul_one]
  have hlat : ∀ p ∈ evolutionLateralFrontier autonomousWholeDomain (fun _ => 0) τ, V p = 0 := by
    intro p hp
    have hpS : p ∈ S := ⟨hp.1, frontier_subset_closure hp.2⟩
    refine tendsto_nhds_unique (hV p hpS) ?_
    refine tendsto_const_nhds.congr' (Eventually.of_forall fun N => ?_)
    exact ((hu N).2.2.2.2.2 p hp).symm
  -- weak equation, Hörmander, pointwise equation
  have hweak : IsKineticWeakTransportedSolution (evolutionCoefficient A.a) (identityDrift 1) U V
    (fun _ => 0) := by
    refine weak_transport_equation_of_vanishing_viscosity 1 (by omega) lam Lam 1 1 hlam hlamLam
      one_pos le_rfl
      autonomousWholeDomain (fun _ => 0) (evolutionCoefficient A.a) (identityDrift 1)
        autonomousWholeDomain_admissible (zeroCurve_piecewiseC1 1)
      (evolutionCoefficient_smooth A) (evolutionCoefficient_symmetric A.a)
      (evolutionCoefficient_bounds A) (identityDrift_smooth 1) (identityDrift_bounds 1).1
        (identityDrift_bounds 1).2 τ
      (fun _ => 0) (fun _ => le_rfl) tendsto_const_nhds u V C hC0 ?_ ?_ ?_ ?_ ?_
    · intro N
      exact classical_viscous_terminalSolution_isWeak hΩo continuous_const
        (evolutionCoefficient_smooth A) (evolutionCoefficient_symmetric A.a) (identityDrift_smooth
        1)
        ((isClassicalViscousTerminalSolution_zero_iff autonomousWholeDomain (fun _ => 0)
          (evolutionCoefficient A.a) (identityDrift 1) τ _ _).2 (hu N))
    · intro N
      filter_upwards [ae_restrict_mem hU.measurableSet] with p hp
      exact hbd N p (hUS hp)
    · exact (hcont.mono hUS).aestronglyMeasurable hU.measurableSet
    · filter_upwards [ae_restrict_mem hU.measurableSet] with p hp
      exact hVbd p (hUS hp)
    · intro ψ hψ
      refine tendsto_integral_of_dominated_convergence (fun p => C * |ψ p|) ?_ ?_ ?_ ?_
      · intro N
        exact (((hu N).2.1.mono hUS).aestronglyMeasurable hU.measurableSet).mul
          hψ.aestronglyMeasurable
      · exact hψ.norm.const_mul C
      · intro N
        filter_upwards [ae_restrict_mem hU.measurableSet] with p hp
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hbd N p (hUS hp)) (abs_nonneg _)
      · filter_upwards [ae_restrict_mem hU.measurableSet] with p hp
        exact (hV p (hUS hp)).mul_const _
  obtain ⟨V', hV', hrep⟩ := exists_smooth_kinetic_representative hH hlam
    (evolutionCoefficient_smooth A) (evolutionCoefficient_bounds A)
    (identityDrift_smooth 1) one_pos (identityDrift_bounds 1).2 U hU V hweak
  have hcontP : ContinuousOn (V ∘ evolutionHomeomorph 1) (evolutionHomeomorph 1 ⁻¹' U) :=
    (hcont.mono hUS).comp (evolutionHomeomorph 1).continuous.continuousOn (fun x hx => hx)
  have hEq : EqOn V V' U := eqOn_of_ae_eq_of_continuousOn_kinetic hU hcontP hV'.continuousOn hrep
  have hVsmooth : ContDiffOn ℝ (⊤ : ℕ∞) (V ∘ evolutionHomeomorph 1)
      (evolutionHomeomorph 1 ⁻¹' U) := hV'.congr fun x hx => hEq hx
  refine ⟨V, hV, ⟨C, hC0, fun p hp => hVbd p hp⟩, hcont, ?_, ?_, ?_, ?_⟩
  · rw [evolutionPastInteriorRaw_eq_image]
    exact contDiffOn_comp_evolutionHomeomorph_iff.mp hVsmooth
  · exact transportedForwardOperator_eq_zero_of_smooth_weak (evolutionCoefficient_smooth A)
      (evolutionCoefficient_symmetric A.a) (identityDrift_smooth 1) hU
      hweak hVsmooth (Filter.EventuallyEq.refl _ _)
  · exact hterm
  · exact hlat

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

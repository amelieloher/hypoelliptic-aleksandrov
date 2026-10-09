module

import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ClassicalTerminalLimit
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ClassicalTerminalWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.MarginalCutoffLimit
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ViscosityWeakLimit
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExternalRegularity

/-!
# The cutoff limit is a classical solution (Proposition 2.1)

Let `F` be a smooth compactly supported scalar datum and `u_N` classical terminal solutions for the
cutoff data `F_N(y, z) = F(y) χ((z)/(N+1))`.  By the growth tail comparison
(`classical_sub_le_growthBarrier`) the sequence `u_N(p)` is Cauchy at EVERY point of the past closed
cylinder, with `|V - u_N| ≤ ‖F‖ Φ_τ / (N + 1)²`; hence the limit `V` is a locally uniform limit of
functions continuous on the closed cylinder and is itself continuous there, including the terminal
and lateral faces (continuity BEFORE Hörmander).  The weak equation passes to the limit by bounded
convergence; the Hörmander input `hH` gives a smooth representative, which coincides with
the continuous `V` everywhere.  The limit is a classical terminal solution for the `z`-independent
datum `F(y)`; no covariance and no hypothesis on `B` beyond the standing ones are used.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Filter Set MeasureTheory Evolution
open scoped Topology MatrixOrder

theorem tendsto_quadratic_tail (K : ℝ) :
    Tendsto (fun N : ℕ => K / ((N : ℝ) + 1) ^ 2) atTop (𝓝 0) := by
  have h : Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).comp
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  exact tendsto_const_nhds.div_atTop h

/-- A sequence with the quadratic tail bound `|a M - a N| ≤ K / (N+1)²` (`M ≥ N`) is Cauchy. -/
theorem cauchySeq_of_quadratic_tail {a : ℕ → ℝ} {K : ℝ}
    (h : ∀ N M : ℕ, N ≤ M → |a M - a N| ≤ K / ((N : ℝ) + 1) ^ 2) : CauchySeq a := by
  refine cauchySeq_of_le_tendsto_0 (fun N => 2 * (K / ((N : ℝ) + 1) ^ 2)) ?_ ?_
  · intro n m N hn hm
    have h1 := h N n hn
    have h2 := h N m hm
    rw [Real.dist_eq]
    calc |a n - a m| ≤ |a n - a N| + |a N - a m| := abs_sub_le _ _ _
      _ = |a n - a N| + |a m - a N| := by rw [abs_sub_comm (a N) (a m)]
      _ ≤ 2 * (K / ((N : ℝ) + 1) ^ 2) := by linarith
  · simpa using (tendsto_quadratic_tail K).const_mul 2

/-- **Cutoff limit** (Proposition 2.1).  The pointwise limit of classical
solutions `u_N` of the cutoff data `F(y) χ_N(z)` exists on the past closed cylinder and is a
classical terminal solution for the `z`-independent datum `F(y)`. -/
theorem exists_cutoff_limit_classical
    (hH : HormanderHypoellipticityStatement)
    (n : ℕ) (hn : 1 ≤ n) (lam Lam m L_b : ℝ)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam) (hm : 0 < m) (hmLb : m ≤ L_b)
    (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n)
    (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n)
    (hΩ : IsAdmissibleEvolutionDomain Ω) (hγ : IsContinuousPiecewiseC1 γ)
    (hB_smooth : IsSmoothFullKineticCoefficient B)
    (hB_symm : IsSymmetricFullKineticCoefficient B)
    (hB_ell : HasEverywhereLoewnerBounds lam Lam B)
    (hb_smooth : IsSmoothDrift b) (hb_lipschitz : HasEuclideanLipschitzDrift L_b b)
    (hb_coercive : HasUnitDirectionDriftCoercivity m b)
    (τ : ℝ) (F : BoundedBorel (PDE.Vec n)) (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, |F x| ≤ C)
    (u : ℕ → KineticPoint n → ℝ)
    (hu : ∀ N, IsClassicalTerminalSolution Ω γ B b τ (cutoffDatum F N) (u N))
    (hbd : ∀ N, ∀ p ∈ evolutionPastClosedCylinder Ω γ τ, |u N p| ≤ C) :
    ∃ V : KineticPoint n → ℝ,
      (∀ p ∈ evolutionPastClosedCylinder Ω γ τ, Tendsto (fun N => u N p) atTop (𝓝 (V p))) ∧
      IsClassicalTerminalSolution Ω γ B b τ (lowerDatum F) V := by
  let : SecondCountableTopology (KineticPoint n) :=
    (KineticPoint.homeomorphProd n).isEmbedding.secondCountableTopology
  have hΩo := isOpen_of_isAdmissibleEvolutionDomain hΩ
  let S := evolutionPastClosedCylinder Ω γ τ
  let U := evolutionPastOpenCylinder Ω γ τ
  have hU : IsOpen U := isOpen_evolutionPastOpenCylinder hΩo hγ.1 τ
  have hUS : U ⊆ S := fun p hp => ⟨hp.1.le, subset_closure hp.2⟩
  obtain ⟨Ct, hCt0, hCt⟩ := classical_sub_le_growthBarrier hΩo hγ.1 hlam hB_ell hb_lipschitz
  -- tail bound
  have hTail : ∀ N M : ℕ, N ≤ M → ∀ p ∈ S,
      |u M p - u N p| ≤ C / ((N : ℝ) + 1) ^ 2 * growthBarrier Ct τ p := by
    intro N M hNM p hp
    have hc : 0 ≤ C / ((N : ℝ) + 1) ^ 2 := by positivity
    have h1 := hCt τ (cutoffDatum F M) (cutoffDatum F N) (u M) (u N) _ hc (hu M) (hu N)
      (fun x _ => (le_abs_self _).trans (abs_cutoffDatum_sub_le hC hC0 hNM x)) p hp
    have h2 := hCt τ (cutoffDatum F N) (cutoffDatum F M) (u N) (u M) _ hc (hu N) (hu M)
      (fun x _ => by
        exact (le_abs_self _).trans (by
          rw [abs_sub_comm]
          exact abs_cutoffDatum_sub_le hC hC0 hNM x)) p hp
    rw [abs_le]
    constructor <;> linarith
  have hlimex : ∀ p ∈ S, ∃ v, Tendsto (fun N => u N p) atTop (𝓝 v) := fun p hp =>
    cauchySeq_tendsto_of_complete (cauchySeq_of_quadratic_tail
      (K := C * growthBarrier Ct τ p) (fun N M hNM => by
        have := hTail N M hNM p hp
        rwa [div_mul_eq_mul_div] at this))
  let V : KineticPoint n → ℝ := fun p => limUnder atTop (fun N => u N p)
  have hV : ∀ p ∈ S, Tendsto (fun N => u N p) atTop (𝓝 (V p)) := fun p hp =>
    tendsto_nhds_limUnder (hlimex p hp)
  -- the limit is bounded and satisfies the tail bound
  have hVbd : ∀ p ∈ S, |V p| ≤ C := fun p hp =>
    le_of_tendsto' ((hV p hp).abs) (fun N => hbd N p hp)
  have hVtail : ∀ N : ℕ, ∀ p ∈ S,
      |V p - u N p| ≤ C / ((N : ℝ) + 1) ^ 2 * growthBarrier Ct τ p := by
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
      · have hlim := tendsto_quadratic_tail (C * (growthBarrier Ct τ x + 1))
        filter_upwards [hlim.eventually (gt_mem_nhds hε)] with N hN y hy
        rw [Real.dist_eq]
        have h1 := hVtail N y hy.1
        have h2 : C / ((N : ℝ) + 1) ^ 2 * growthBarrier Ct τ y ≤
            C * (growthBarrier Ct τ x + 1) / ((N : ℝ) + 1) ^ 2 := by
          rw [div_mul_eq_mul_div]
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hy.2.le hC0
        linarith
    exact hloc.continuousOn (Eventually.of_forall fun N => (hu N).2.1).frequently
  -- terminal and lateral values
  have hterm : ∀ p ∈ evolutionTerminalClosure Ω γ τ,
      V p = lowerDatum F (p.position, p.velocity) := by
    intro p hp
    have hpS : p ∈ S := ⟨hp.1.le, hp.1 ▸ hp.2⟩
    refine tendsto_nhds_unique (hV p hpS) ?_
    refine tendsto_const_nhds.congr' ?_
    obtain ⟨N₀, hN₀⟩ := exists_nat_ge ‖p.velocity‖
    filter_upwards [eventually_ge_atTop N₀] with N hN
    rw [(hu N).2.2.2.2.1 p hp, cutoffDatum_apply, lowerDatum_apply,
      zCutoffN_eq_one (by
        have : (N₀ : ℝ) ≤ N := by exact_mod_cast hN
        simp only
        linarith), mul_one]
  have hlat : ∀ p ∈ evolutionLateralFrontier Ω γ τ, V p = 0 := by
    intro p hp
    have hpS : p ∈ S := ⟨hp.1, frontier_subset_closure hp.2⟩
    refine tendsto_nhds_unique (hV p hpS) ?_
    refine tendsto_const_nhds.congr' (Eventually.of_forall fun N => ?_)
    exact ((hu N).2.2.2.2.2 p hp).symm
  -- weak equation, Hörmander, pointwise equation
  have hweak : IsKineticWeakTransportedSolution B b U V (fun _ => 0) := by
    refine weak_transport_equation_of_vanishing_viscosity n hn lam Lam m L_b hlam hlamLam hm hmLb
      Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive τ
      (fun _ => 0) (fun _ => le_rfl) tendsto_const_nhds u V C hC0 ?_ ?_ ?_ ?_ ?_
    · intro N
      exact classical_viscous_terminalSolution_isWeak hΩo hγ.1 hB_smooth hB_symm hb_smooth
        ((isClassicalViscousTerminalSolution_zero_iff Ω γ B b τ _ _).2 (hu N))
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
  obtain ⟨V', hV', hrep⟩ := exists_smooth_kinetic_representative hH hlam hB_smooth hB_ell
    hb_smooth hm hb_coercive U hU V hweak
  have hcontP : ContinuousOn (V ∘ evolutionHomeomorph n) (evolutionHomeomorph n ⁻¹' U) :=
    (hcont.mono hUS).comp (evolutionHomeomorph n).continuous.continuousOn (fun x hx => hx)
  have hEq : EqOn V V' U := eqOn_of_ae_eq_of_continuousOn_kinetic hU hcontP hV'.continuousOn hrep
  have hVsmooth : ContDiffOn ℝ (⊤ : ℕ∞) (V ∘ evolutionHomeomorph n)
      (evolutionHomeomorph n ⁻¹' U) := hV'.congr fun x hx => hEq hx
  refine ⟨V, hV, ⟨C, hC0, fun p hp => hVbd p hp⟩, hcont, ?_, ?_, ?_, ?_⟩
  · rw [evolutionPastInteriorRaw_eq_image]
    exact contDiffOn_comp_evolutionHomeomorph_iff.mp hVsmooth
  · exact transportedForwardOperator_eq_zero_of_smooth_weak hB_smooth hB_symm hb_smooth hU
      hweak hVsmooth (Filter.EventuallyEq.refl _ _)
  · exact hterm
  · exact hlat

end HypoellipticAleksandrov.KineticAleksandrov

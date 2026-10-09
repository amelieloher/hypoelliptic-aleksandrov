module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.PhaseCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.PhaseInfinity
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.Order.Compact
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Uniqueness
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonEvolution
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Cutoffs of the strictly forbidden phase

A compactly supported terminal test has a positive phase margin. A smooth
increasing cutoff of the phase then dominates the test and vanishes at phase zero.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open Set Filter MeasureTheory
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped Topology

/-- A compact test supported in a positive phase region has a uniform positive margin. -/
theorem exists_positive_phase_margin {E : Type*} [TopologicalSpace E]
    {φ q : E → ℝ} (hφ : HasCompactSupport φ) (hq : Continuous q)
    (hs : tsupport φ ⊆ {x | 0 < q x}) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ tsupport φ, δ ≤ q x := by
  by_cases he : (tsupport φ).Nonempty
  · obtain ⟨x, hx, hmin⟩ := hφ.exists_isMinOn he hq.continuousOn
    exact ⟨q x, hs hx, fun y hy => hmin hy⟩
  · exact ⟨1, zero_lt_one, fun x hx => False.elim (he ⟨x, hx⟩)⟩

/-- A smooth monotone phase cutoff dominates every `[0,1]` test in the forbidden set. -/
theorem exists_phase_cutoff {E : Type*} [TopologicalSpace E]
    {φ q : E → ℝ} (hφ : HasCompactSupport φ) (hq : Continuous q)
    (hs : tsupport φ ⊆ {x | 0 < q x}) (hbound : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ Monotone χ ∧
      χ 0 = 0 ∧ (∀ r, 0 ≤ χ r ∧ χ r ≤ 1) ∧ (∀ x, φ x ≤ χ (q x)) := by
  obtain ⟨δ, hδ, hm⟩ := exists_positive_phase_margin hφ hq hs
  refine ⟨fun r => Real.smoothTransition (r / δ), ?_, ?_, ?_, ?_, ?_⟩
  · exact Real.smoothTransition.contDiff.comp (contDiff_id.div_const δ)
  · intro r s hrs
    exact Real.smoothTransition.monotone (div_le_div_of_nonneg_right hrs hδ.le)
  · simp only [zero_div, Real.smoothTransition.zero]
  · intro r
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  · intro x
    change φ x ≤ Real.smoothTransition (q x / δ)
    by_cases hx : x ∈ tsupport φ
    · rw [Real.smoothTransition.one_of_one_le ((one_le_div hδ).mpr (hm x hx))]
      exact (hbound x).2
    · rw [image_eq_zero_of_notMem_tsupport hx]
      exact Real.smoothTransition.nonneg _

/-- Composing a signed phase with a smooth scalar cutoff preserves slice regularity. -/
theorem phaseCutoff_isSliceRegularAt {d : ℕ} (sgn : ℝ) (ξ z0 : PDE.Vec d)
    {b : PDE.Vec d → PDE.Vec d} {Lb : ℝ} (hb : HasEuclideanLipschitzDrift Lb b)
    {γ : ℝ → PDE.Vec d} {σ τ ρ : ℝ} (hγ : ContinuousOn γ (Icc σ τ))
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ 2 χ) (p : KineticPoint d) (ht : p.time ∈ Ioo σ τ) :
    IsSliceRegularAt (fun q => χ (phaseBarrier sgn ξ z0 b γ σ Lb ρ q)) p := by
  have hr := phaseBarrier_isSliceRegularAt sgn ξ z0 hb (ρ := ρ) hγ p ht
  exact ⟨(hχ.differentiable (by norm_num)).differentiableAt.comp p.time hr.time,
    hχ.contDiffAt.comp p.position hr.position, hχ.contDiffAt.comp p.velocity hr.velocity⟩

/-- The transported operator obeys the scalar chain rule on an affine phase barrier. -/
theorem lop_phaseCutoff {d : ℕ} (B : CoefficientField d) (sgn : ℝ) (ξ z0 : PDE.Vec d)
    {b : PDE.Vec d → PDE.Vec d} {Lb : ℝ} (hb : HasEuclideanLipschitzDrift Lb b)
    {γ : ℝ → PDE.Vec d} {σ τ ρ : ℝ} (hγ : ContinuousOn γ (Icc σ τ))
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ 2 χ) (p : KineticPoint d) (ht : p.time ∈ Ioo σ τ) :
    lop B b (fun q => χ (phaseBarrier sgn ξ z0 b γ σ Lb ρ q)) p =
      deriv χ (phaseBarrier sgn ξ z0 b γ σ Lb ρ p) *
        lop B b (phaseBarrier sgn ξ z0 b γ σ Lb ρ) p := by
  let κ := phaseBarrier sgn ξ z0 b γ σ Lb ρ
  have hr := phaseBarrier_isSliceRegularAt sgn ξ z0 hb (ρ := ρ) hγ p ht
  have hd := (hχ.differentiable (by norm_num)).differentiableAt.hasDerivAt
    (x := κ p)
  have htime : kineticTimeDerivative (fun q => χ (κ q)) p =
      deriv χ (κ p) * kineticTimeDerivative κ p := by
    exact (hd.comp p.time hr.time.hasDerivAt).deriv
  have hgrad : kineticVelocityGradient (fun q => χ (κ q)) p =
      deriv χ (κ p) • kineticVelocityGradient κ p := by
    have hv := hd.comp_hasFDerivAt p.velocity
      (hr.velocity.differentiableAt (by norm_num)).hasFDerivAt
    ext i
    change fderiv ℝ (χ ∘ fun z : PDE.Vec d =>
      phaseBarrier sgn ξ z0 b γ σ Lb ρ ⟨p.time, p.position, z⟩)
        p.velocity (PDE.basisVec i) = _
    rw [hv.fderiv]
    rfl
  have hh : diffusedHessian (fun q => χ (κ q)) p = 0 := by
    have hz : (fun y : PDE.Vec d => kineticPositionGradient
        (fun q => χ (κ q)) ⟨p.time, y, p.velocity⟩) = fun _ => 0 := by
      funext y i
      change fderiv ℝ (fun _ : PDE.Vec d => χ (κ p)) y (PDE.basisVec i) = 0
      rw [fderiv_const_apply]
      rfl
    ext i j
    simp only [diffusedHessian]
    rw [hz, fderiv_const_apply]
    rfl
  unfold lop transportedForwardOperatorOfTimeDiffusedCoefficient transportedForwardOperator
  rw [htime, hgrad, hh, phase_diffused_hessian]
  simp only [matrixContraction, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  simp only [PDE.vecDot, Pi.smul_apply, smul_eq_mul]
  have hs : (∑ i, b p.position i * (deriv χ (κ p) * kineticVelocityGradient κ p i)) =
      ∑ i, deriv χ (κ p) * (b p.position i * kineticVelocityGradient κ p i) := by
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hs, ← Finset.mul_sum]
  dsimp only [κ]
  ring

/-- A classical terminal solution with a forbidden-phase test is nonpositive initially. -/
theorem classical_phase_test_nonpos {d : ℕ} (B : CoefficientField d)
    (b : PDE.Vec d → PDE.Vec d) (γ : ℝ → PDE.Vec d)
    (σ τ Lb ρ : ℝ) (hστ : σ < τ) (hρ : 0 < ρ)
    (ξ z0 : PDE.Vec d) (hξ : PDE.vecNormSq ξ = 1)
    (hb : HasEuclideanLipschitzDrift Lb b) (hγ : Continuous γ)
    (hB : ∀ t v, (B t v).PosSemidef)
    (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1)
    (φ : BoundedBorel (EvolutionAmbientState d))
    (hφ : IsSmoothCompactTerminalDatum (PDE.euclideanBall 0 ρ) γ τ φ)
    (hbound : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hs : tsupport (φ : EvolutionAmbientState d → ℝ) ⊆
      {x | 0 < sgn * (phaseCoordinate ξ z0 x - phaseCenter ξ b γ σ τ) -
        Lb * ρ * (τ - σ)})
    (u : KineticPoint d → ℝ)
    (hu : IsClassicalTerminalSolution (PDE.euclideanBall 0 ρ) γ
      (zIndependentCoefficient B) b τ φ u)
    (v : PDE.Vec d) (hv : v ∈ movingDomain (PDE.euclideanBall 0 ρ) γ σ) :
    u ⟨σ, v, z0⟩ ≤ 0 := by
  let Ω := PDE.euclideanBall (0 : PDE.Vec d) ρ
  let κ := phaseBarrier sgn ξ z0 b γ σ Lb ρ
  let q : EvolutionAmbientState d → ℝ := fun x =>
    sgn * (phaseCoordinate ξ z0 x - phaseCenter ξ b γ σ τ) - Lb * ρ * (τ - σ)
  have hq : Continuous q := by
    dsimp only [q, phaseCoordinate]
    unfold PDE.vecDot
    simp only [Pi.sub_apply]
    fun_prop
  obtain ⟨χ, hχ, hmχ, hχ0, hχbounds, hdom⟩ := exists_phase_cutoff hφ.2.1 hq hs hbound
  have hχ2 : ContDiff ℝ 2 χ := hχ.of_le
    (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
  let F : KineticPoint d → ℝ := fun p => χ (κ p)
  have hFnonneg : ∀ p, 0 ≤ F p := fun p => (hχbounds (κ p)).1
  have hFc : ContinuousOn F (maximumClosedTube Ω γ σ τ) :=
    hχ.continuous.comp_continuousOn
      ((phaseBarrier_continuousOn sgn ξ z0 hb (ρ := ρ) hστ.le hγ.continuousOn).mono
        (fun p hp => hp.1))
  have hFr : ∀ p ∈ maximumOpenTube Ω γ σ τ, IsSliceRegularAt F p :=
    fun p hp => phaseCutoff_isSliceRegularAt sgn ξ z0 hb hγ.continuousOn hχ2 p hp.1
  have hFlop : ∀ p ∈ maximumOpenTube Ω γ σ τ, lop B b F p ≤ 0 := by
    intro p hp
    rw [lop_phaseCutoff B sgn ξ z0 hb hγ.continuousOn hχ2 p hp.1]
    apply mul_nonpos_of_nonneg_of_nonpos hmχ.deriv_nonneg
    apply (phase_barrier_drift B b γ σ τ Lb ρ hρ ξ z0 hξ hb hγ.continuousOn
      sgn hsgn p hp.1 ?_).2
    have hv' := mem_movingDomain_iff.mp hp.2
    simpa only [Ω, PDE.euclideanBall, PDE.euclideanSqDist, Set.mem_ofPred_eq, sub_zero] using hv'
  obtain ⟨M, hM, hbM, -⟩ :=
    phase_infinity_barrier B b σ τ ρ hρ γ hγ.continuousOn
      (continuous_of_euclidean_lipschitz hb) z0
  obtain ⟨C, -, hC⟩ := hu.1
  have hclosed : maximumClosedTube Ω γ σ τ ⊆ evolutionPastClosedCylinder Ω γ τ :=
    fun p hp => ⟨hp.1.2, hp.2⟩
  have hopen : maximumOpenTube Ω γ σ τ ⊆ evolutionPastOpenCylinder Ω γ τ :=
    fun p hp => ⟨hp.1.2, hp.2⟩
  have huv := (isClassicalViscousTerminalSolution_zero_iff Ω γ
    (zIndependentCoefficient B) b τ φ u).mpr hu
  have hur : ∀ p ∈ maximumOpenTube Ω γ σ τ, IsSliceRegularAt u p :=
    fun p hp => huv.isSliceRegularAt (PDE.isOpen_euclideanBall 0 ρ) hγ (hopen hp)
  have huinitial : ∀ η : ℝ, 0 < η →
      u ⟨σ, v, z0⟩ ≤ η * Real.exp ((M + 1) * (τ - σ)) := by
    intro η hη
    let H := infinityBarrier η M τ z0
    let w : KineticPoint d → ℝ := fun p => u p - F p - H p
    have hHr : ∀ p, IsSliceRegularAt H p := infinityBarrier_isSliceRegularAt η M τ z0
    have hwcontrol : IsUniformlyNegAtInfinityOn w (maximumClosedTube Ω γ σ τ) := by
      intro A
      obtain ⟨R, hR, hh⟩ := infinityBarrier_uniform_growth hη hM z0 (C - A)
      refine ⟨R, hR, ?_⟩
      intro p hp hz
      have huC := (le_abs_self (u p)).trans (hC p (hclosed hp))
      have hH := hh p hp.1.2 hz
      have hF := hFnonneg p
      dsimp [w, H]
      linarith
    have hwr : ∀ p ∈ maximumOpenTube Ω γ σ τ, IsSliceRegularAt w p :=
      fun p hp => ((hur p hp).sub (hFr p hp)).sub (hHr p)
    have hwsub : ∀ p ∈ maximumOpenTube Ω γ σ τ,
        0 ≤ transportedForwardOperator (zIndependentCoefficient B) b w p := by
      intro p hp
      have hr := hur p hp
      have hfr := hFr p hp
      have hhr := hHr p
      have heq := hu.2.2.2.1 p (hopen hp)
      have hf := hFlop p hp
      have hh := lop_infinityBarrier_le B b (τ := τ) hη.le hM z0 p
        (hbM p ⟨⟨hp.1.1.le, hp.1.2.le⟩, subset_closure hp.2⟩)
      have hHpos : 0 ≤ H p := by
        have hn := PDE.vecNormSq_nonneg (p.velocity - z0)
        dsimp [H, infinityBarrier]
        positivity
      have he : transportedForwardOperator (zIndependentCoefficient B) b w p =
          transportedForwardOperator (zIndependentCoefficient B) b u p -
            lop B b F p - lop B b H p := by
        have h1 := viscousTransportedOperator_sub (B := zIndependentCoefficient B)
          (b := b) (ε := 0) (hr.sub hfr) hhr
        have h2 := viscousTransportedOperator_sub (B := zIndependentCoefficient B)
          (b := b) (ε := 0) hr hfr
        simpa only [viscousTransportedOperator_zero, h2, w, lop,
          transportedForwardOperatorOfTimeDiffusedCoefficient] using h1
      rw [he, heq]
      linarith
    have hterminal : ∀ p ∈ maximumClosedTube Ω γ σ τ, p.time = τ → w p ≤ 0 := by
      intro p hp ht
      have hut := hu.2.2.2.2.1 p ⟨ht, ht ▸ hp.2⟩
      have hdom' := hdom (p.position, p.velocity)
      have hF : F p = χ (q (p.position, p.velocity)) := by
        dsimp [F, κ, q, phaseBarrier, phaseCoordinate]
        rw [ht]
      have hH : 0 ≤ H p := by
        have hn := PDE.vecNormSq_nonneg (p.velocity - z0)
        dsimp [H, infinityBarrier]
        positivity
      dsimp [w]
      rw [hut, hF]
      linarith
    have hlateral : ∀ p ∈ maximumClosedTube Ω γ σ τ,
        p.position ∈ frontier (movingDomain Ω γ p.time) → w p ≤ 0 := by
      intro p hp hf
      have hul := hu.2.2.2.2.2 p ⟨hp.1.2, hf⟩
      have hF := hFnonneg p
      have hH : 0 ≤ H p := by
        have hn := PDE.vecNormSq_nonneg (p.velocity - z0)
        dsimp [H, infinityBarrier]
        positivity
      dsimp [w]
      rw [hul]
      linarith
    have hw := nonpos_on_maximumClosedTube hστ (PDE.isOpen_euclideanBall 0 ρ)
      (isCompact_closure_of_maximumPrinciple_domain (Or.inl ⟨0, ρ, hρ, rfl⟩))
      hγ.continuousOn
      (((hu.2.1.mono hclosed).sub hFc).sub (infinityBarrier_continuous η M τ z0).continuousOn)
      (Or.inr hwcontrol)
      (fun p hp => ⟨(hwr p hp).time, (hwr p hp).position,
        (hwr p hp).velocity.differentiableAt (by norm_num)⟩)
      (fun p _ => hB p.time p.position) hwsub hterminal hlateral
      ⟨σ, v, z0⟩ ⟨⟨le_rfl, hστ.le⟩, subset_closure hv⟩
    have hstart : F ⟨σ, v, z0⟩ = 0 := by
      dsimp [F, κ, phaseBarrier, phaseCenter]
      simpa only [sub_self, PDE.vecDot, Pi.zero_apply, mul_zero,
        Finset.sum_const_zero, intervalIntegral.integral_same, sub_zero] using hχ0
    dsimp [w, H] at hw
    rw [hstart] at hw
    simpa only [infinityBarrier, sub_self, PDE.vecNormSq, PDE.vecDot, Pi.zero_apply,
      mul_zero, Finset.sum_const_zero, add_zero, mul_one, sub_zero, sub_nonpos] using hw
  by_contra hn
  have hpos : 0 < u ⟨σ, v, z0⟩ := lt_of_not_ge hn
  let E := Real.exp ((M + 1) * (τ - σ))
  have he : 0 < E := Real.exp_pos _
  have hh := huinitial (u ⟨σ, v, z0⟩ / (2 * E)) (div_pos hpos (by positivity))
  have hcancel : u ⟨σ, v, z0⟩ / (2 * E) * E = u ⟨σ, v, z0⟩ / 2 := by
    field_simp
  rw [hcancel] at hh
  linarith

/-- Constant extension of a continuous curve on a nonempty interval is continuous. -/
theorem continuous_clippedCurve {d : ℕ} {γ : ℝ → PDE.Vec d} {σ τ : ℝ}
    (hστ : σ ≤ τ) (hγ : ContinuousOn γ (Icc σ τ)) :
    Continuous (clippedCurve γ σ τ) := by
  apply hγ.comp_continuous
    (continuous_const.max (continuous_const.min continuous_id))
  intro t
  exact ⟨le_max_left _ _, max_le hστ (min_le_left _ _)⟩

/-- Clipping does not change the source phase center over its defining interval. -/
theorem phaseCenter_clippedCurve {d : ℕ} (ξ : PDE.Vec d)
    (b : PDE.Vec d → PDE.Vec d) (γ : ℝ → PDE.Vec d) {σ τ : ℝ} (hστ : σ ≤ τ) :
    phaseCenter ξ b (clippedCurve γ σ τ) σ τ = phaseCenter ξ b γ σ τ := by
  unfold phaseCenter
  apply intervalIntegral.integral_congr
  intro t ht
  change PDE.vecDot ξ (b (clippedCurve γ σ τ t)) = PDE.vecDot ξ (b (γ t))
  rw [clippedCurve_eq_of_mem γ (by simpa only [uIcc_of_le hστ] using ht)]

/-- Smooth forbidden-phase tests have zero integral against the supplied moving kernel. -/
theorem phase_forbidden_test_integral_eq_zero (d : ℕ) (_hd : 1 ≤ d)
    (lam Lam : ℝ) (_hlam : 0 < lam) (_hlamLam : lam ≤ Lam)
    (m Lb : ℝ) (D : Set (PDE.Vec d)) (B : CoefficientField d)
    (b : PDE.Vec d → PDE.Vec d) (hsetting : SourceSetting lam Lam m Lb D B b)
    (σ τ H ρ : ℝ) (γ : ℝ → PDE.Vec d) (hστ0 : σ ≤ τ) (hρ : 0 < ρ)
    (hγ : PiecewiseC1On γ σ τ) (_hspeed : HasCurveSpeedOn H γ σ τ)
    (_hfit : ∀ r ∈ Icc σ τ, PDE.euclideanBall (γ r) ρ ⊆ D)
    (S : TerminalOperatorFamily (PDE.euclideanBall 0 ρ) (clippedCurve γ σ τ))
    (K : MovingFiberKernel (PDE.euclideanBall 0 ρ) (clippedCurve γ σ τ))
    (hreal : RealizesTerminalEvolution (PDE.euclideanBall 0 ρ) (clippedCurve γ σ τ)
      (PDE.isOpen_euclideanBall 0 ρ).measurableSet (zIndependentCoefficient B) b S K)
    (_hpar : HasParabolicMarginalBundle (PDE.euclideanBall 0 ρ) (clippedCurve γ σ τ)
      (PDE.isOpen_euclideanBall 0 ρ).measurableSet (zIndependentCoefficient B) K)
    (ξ z0 v : PDE.Vec d) (hξ : PDE.vecNormSq ξ = 1)
    (hστ : σ ≤ τ)
    (hv : v ∈ movingDomain (PDE.euclideanBall 0 ρ) (clippedCurve γ σ τ) σ)
    (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1)
    (φ : BoundedBorel (EvolutionAmbientState d))
    (hφ : IsSmoothCompactTerminalDatum (PDE.euclideanBall 0 ρ)
      (clippedCurve γ σ τ) τ φ)
    (hbound : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hs : tsupport (φ : EvolutionAmbientState d → ℝ) ⊆
      {x | 0 < sgn * (phaseCoordinate ξ z0 x - phaseCenter ξ b γ σ τ) -
        Lb * ρ * (τ - σ)}) :
    ∫ x, φ x ∂K.master (movingQuery σ τ hστ v z0 hv) = 0 := by
  let Ω := PDE.euclideanBall (0 : PDE.Vec d) ρ
  let γc := clippedCurve γ σ τ
  let p : EvolutionState Ω γc σ := ⟨(v, z0), hv, mem_univ _⟩
  have hi : ∫ x, φ x ∂K.master (movingQuery σ τ hστ v z0 hv) =
      ∫ x, φ x.1 ∂K.fiberKernel (PDE.isOpen_euclideanBall 0 ρ).measurableSet σ τ hστ p :=
    integral_master_eq_fiber K (PDE.isOpen_euclideanBall 0 ρ).measurableSet
      σ τ hστ p φ φ.measurable
  by_cases ht : σ = τ
  · subst τ
    rw [hi, hreal.2.2.1 σ]
    simp only [ProbabilityTheory.Kernel.id_apply, integral_dirac]
    change φ (v, z0) = 0
    by_contra hn
    have hs' := hs (subset_tsupport (φ : EvolutionAmbientState d → ℝ)
      (show (v, z0) ∈ Function.support (φ : EvolutionAmbientState d → ℝ) from hn))
    simp only [Set.mem_ofPred_eq, phaseCoordinate, phaseCenter, sub_self,
      PDE.vecDot, Pi.zero_apply,
      mul_zero, Finset.sum_const_zero, intervalIntegral.integral_same, sub_zero, lt_self_iff_false]
      at hs'
  · have ht' : σ < τ := lt_of_le_of_ne hστ ht
    obtain ⟨u, hu, hup, -⟩ := hreal.1 τ φ hφ
    have hB : ∀ t v, (B t v).PosSemidef := by
      intro t v
      have hbounds := (sectionTwoCoefficient_fullBounds lam Lam B hsetting.1).2.2
      exact posSemidef_of_hasEverywhereLoewnerBounds hsetting.1.1.le hbounds t v 0
    have hs' : tsupport (φ : EvolutionAmbientState d → ℝ) ⊆
        {x | 0 < sgn * (phaseCoordinate ξ z0 x - phaseCenter ξ b γc σ τ) -
          Lb * ρ * (τ - σ)} := by
      simpa only [γc, phaseCenter_clippedCurve ξ b γ hστ] using hs
    have hnonpos := classical_phase_test_nonpos B b γc σ τ Lb ρ ht' hρ ξ z0 hξ
      hsetting.2.2.2.2.1.1 (continuous_clippedCurve hστ0 hγ.1) hB sgn hsgn
      φ hφ hbound hs' u hu v hv
    have huintegral : ∫ x, φ x ∂K.master (movingQuery σ τ hστ v z0 hv) =
        u ⟨σ, v, z0⟩ := by
      rw [hi]
      exact (hreal.2.1 σ τ hστ p (terminalStateDatum φ)).symm.trans (hup σ hστ p).symm
    apply le_antisymm
    · exact huintegral.trans_le hnonpos
    · exact integral_nonneg (fun x => (hbound x).1)

end HypoellipticAleksandrov.KineticAleksandrov.Decay

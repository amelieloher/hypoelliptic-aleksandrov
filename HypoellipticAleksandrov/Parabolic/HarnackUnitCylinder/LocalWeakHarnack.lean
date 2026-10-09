module

public import HypoellipticAleksandrov.Parabolic.SourceLocalHarnackScaling
public import HypoellipticAleksandrov.Parabolic.HarnackStability
public import HypoellipticAleksandrov.Parabolic.HarnackUnitCylinder.CoefficientExtension

/-! # Local weak Harnack inequalities on closed link boxes -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped ENNReal Topology Matrix.Norms.Elementwise

/-- Smooth coefficients and values have a continuous parabolic residual. -/
theorem continuous_parabolicOperator_of_smooth_for_unitCylinder
    {d : ℕ} {B : CoefficientField d} {q : TimeVelocity d → ℝ}
    (hB : IsSmoothCoefficient B)
    (hq : ContDiff ℝ (↑(⊤ : ℕ∞)) q) :
    Continuous (fun z => parabolicOperator B q z) := by
  change Continuous (fun x =>
    timeDerivative q x - matrixContraction (coefficientAt B x) (velocityHessian q x))
  apply Continuous.sub
  · unfold timeDerivative
    exact ((hq.contDiff_fderiv_apply (m := 0) (by norm_num)).comp
      (contDiff_id.prodMk contDiff_const)).continuous
  · unfold matrixContraction
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    apply Continuous.mul
    · exact hB.continuous.matrix_elem i j
    · unfold velocityHessian
      have hfirst : ContDiff ℝ 1 (fderiv ℝ q) :=
        hq.fderiv_right (m := 1) (by exact WithTop.coe_le_coe.mpr le_top)
      simpa using (hfirst.continuous_fderiv (by norm_num)).clm_apply
        continuous_const |>.clm_apply continuous_const

/-- The local source estimate passes through aligned nonnegative mollifications. -/
theorem exists_local_parabolic_harnack_weak_continuous
    (d : ℕ) (hd : 1 ≤ d) (lam : ℝ) (hlam : 0 < lam)
    (Lam : ℝ) (hlamLam : lam ≤ Lam) :
    ∃ hBox : ℝ, 0 < hBox ∧ hBox ≤ 1 ∧
      ∀ (U : Set (TimeVelocity d)) (B : CoefficientField d)
        (u : TimeVelocity d → ℝ) (t0 : ℝ) (v0 : PDE.Vec d) (r : ℝ),
        IsOpen U → 0 < r →
        parabolicClosedBox 2 r (t0 - r ^ 2) v0 ⊆ U →
        IsContinuousCoefficientOn B U →
        (∀ z ∈ U, (coefficientAt B z).IsSymm) →
        HasLowerEllipticityOn lam B U → HasUpperEllipticityOn Lam B U →
        IsWeakParabolicEquationLoc B U (parabolicExponent d) u →
        ContinuousOn u U → IsNonnegativeOn u U →
        ∀ v ∈ velocityCube v0 (r / 2),
          hBox * u (t0, v0) ≤ u (t0 + r ^ 2, v) := by
  obtain ⟨hBox, C, hh0, hh1, _hC, hsource⟩ :=
    exists_source_local_parabolic_harnack d hd lam hlam Lam hlamLam
  refine ⟨hBox, hh0, hh1, ?_⟩
  intro U B u t0 v0 r hU hr hKU hB hSymm hLower hUpper hWeak hu huNonneg v hv
  let K := parabolicClosedBox 2 r (t0 - r ^ 2) v0
  have hK : IsCompact K := isCompact_parabolicClosedBox _ _ _ _
  let Aext := extendCoefficientByMidpoint B U (ellipticityMidpoint d lam Lam)
  have hExtAE : coefficientAt Aext =ᵐ[timeVelocityVolumeOn U] coefficientAt B :=
    ae_restrict_of_forall_mem hU.measurableSet (fun z hz => by
      simp only [Aext, coefficientAt_extendCoefficientByMidpoint, ite_eq_left hz])
  obtain ⟨_, hExtLower, hExtUpper⟩ :=
    extendCoefficientByMidpoint_global_ellipticity d lam Lam B U
      hSymm hLower hUpper hlamLam
  obtain ⟨J, hUniform, hResidual, hTail⟩ :=
    exists_localizedJet_eventually_nonnegative_residual_mollifications_tendsto d hd lam Lam
      B Aext U K u u hU hK hKU hExtAE
      (isBorel_midpointExtension_of_continuousOn hU hB lam Lam) hExtLower hExtUpper
      hWeak (ae_restrict_of_forall_mem hU.measurableSet huNonneg) hu EventuallyEq.rfl
  let F : ℕ → TimeVelocity d → ℝ := fun n z =>
    parabolicOperator (parabolicMollifyCoefficient Aext n) (parabolicMollifiedValue J.g n) z
  have hFnorm : Tendsto (fun n => parabolicELpNormOn d (F n) K) atTop (nhds 0) := by
    apply Tendsto.congr' ?_ hResidual
    filter_upwards [hTail] with n hn
    have hAE : F n =ᵐ[volume.restrict K]
        weakEquationMollificationResidual Aext J.g n :=
      ae_restrict_of_forall_mem hK.measurableSet hn.2.2.2.2.2.2
    exact (eLpNorm_congr_ae hAE).symm
  have hFreal := tendsto_parabolicLpNormOn_of_tendsto_parabolicELpNormOn_zero hFnorm
  let ε : ℕ → ℝ := fun n =>
    C * r ^ ((d : ℝ) / ((d : ℝ) + 1)) * parabolicLpNormOn d (F n) K
  have hε : Tendsto ε atTop (nhds 0) := by
    simpa only [ε, mul_zero] using tendsto_const_nhds.mul hFreal
  have hsourceMem : (t0, v0) ∈ K := by
    rw [mem_parabolicClosedBox_iff]
    refine ⟨by nlinarith [sq_nonneg r], by nlinarith [sq_nonneg r], ?_⟩
    intro i
    simpa using hr.le
  have htargetMem : (t0 + r ^ 2, v) ∈ K := by
    rw [mem_parabolicClosedBox_iff]
    refine ⟨by nlinarith [sq_nonneg r], by nlinarith, ?_⟩
    intro i
    exact (hv i).le.trans (by linarith)
  have hEventually : ∀ᶠ n in atTop,
      hBox * parabolicMollifiedValue J.g n (t0, v0) ≤
        parabolicMollifiedValue J.g n (t0 + r ^ 2, v) + ε n := by
    filter_upwards [hTail] with n hn
    have hBcontinuous : IsContinuousCoefficient (parabolicMollifyCoefficient Aext n) := by
      change Continuous (fun x i j => coefficientAt (parabolicMollifyCoefficient Aext n) x i j)
      rw [continuous_pi_iff]
      intro i
      rw [continuous_pi_iff]
      intro j
      exact hn.1.continuous.matrix_elem i j
    exact hsource K U (parabolicMollifyCoefficient Aext n) (parabolicMollifiedValue J.g n)
      (F n) t0 v0 r hr hK hKU hU (Subset.refl _)
      (IsContinuousCoefficientOn.of_global hBcontinuous U)
      (contDiffOn_of_global (hn.2.2.2.2.1.of_le
        (by exact WithTop.coe_le_coe.mpr le_top)) U)
      (continuous_parabolicOperator_of_smooth_for_unitCylinder hn.1
        hn.2.2.2.2.1).continuousOn hn.2.2.2.2.2.1
      (HasLowerEllipticityOn.of_global hn.2.2.1 K)
      (HasUpperEllipticityOn.of_global hn.2.2.2.1 K) (fun _ _ => rfl) v hv
  have hleft : Tendsto (fun n => hBox * parabolicMollifiedValue J.g n (t0, v0))
      atTop (nhds (hBox * u (t0, v0))) :=
    tendsto_const_nhds.mul (hUniform.tendsto_at hsourceMem)
  have hright := (hUniform.tendsto_at htargetMem).add hε
  exact le_of_tendsto_of_tendsto hleft (by simpa only [add_zero] using hright) hEventually

end HypoellipticAleksandrov.Parabolic

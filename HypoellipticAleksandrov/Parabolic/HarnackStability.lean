module

public import HypoellipticAleksandrov.Parabolic.HarnackPerturbation
public import HypoellipticAleksandrov.Parabolic.HarnackStabilityLimit
public import HypoellipticAleksandrov.Parabolic.WeakSolutionMollifierResidualConvergence

/-!
# Aligned approximation stability for parabolic Harnack

This module passes the finite source-bearing Harnack chain estimate through a
common compact-uniform smooth approximation and then applies it to the aligned
mollifications of a nonnegative local weak solution.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open scoped Matrix.Norms.Elementwise

open Filter MeasureTheory Set
open scoped ENNReal Topology

private theorem continuous_parabolicOperator_of_smooth
    {d : Nat} {B : CoefficientField d} {w : TimeVelocity d -> Real}
    (hB : IsSmoothCoefficient B)
    (hw : ContDiff Real (↑(⊤ : ℕ∞)) w) :
    Continuous (fun x => parabolicOperator B w x) := by
  change Continuous (fun x =>
    timeDerivative w x - matrixContraction (coefficientAt B x) (velocityHessian w x))
  apply Continuous.sub
  · unfold timeDerivative
    exact ((hw.contDiff_fderiv_apply (m := 0) (by norm_num)).comp
      (contDiff_id.prodMk contDiff_const)).continuous
  · unfold matrixContraction
    apply continuous_finset_sum
    intro i _
    apply continuous_finset_sum
    intro j _
    apply Continuous.mul
    · exact hB.continuous.matrix_elem i j
    · unfold velocityHessian
      have hfirst : ContDiff Real 1 (fderiv Real w) :=
        hw.fderiv_right (m := 1) (by exact WithTop.coe_le_coe.mpr le_top)
      simpa using (hfirst.continuous_fderiv (by norm_num)).clm_apply continuous_const |>.clm_apply
        continuous_const

/-- Extended restricted parabolic norm convergence to zero gives convergence of the
corresponding real restricted norm. -/
theorem tendsto_parabolicLpNormOn_of_tendsto_parabolicELpNormOn_zero
    {d : Nat} {K : Set (TimeVelocity d)}
    {R : Nat -> TimeVelocity d -> Real}
    (hR : Tendsto (fun n => parabolicELpNormOn d (R n) K)
      atTop (nhds 0)) :
    Tendsto (fun n => parabolicLpNormOn d (R n) K)
      atTop (nhds 0) := by
  simpa only [parabolicLpNormOn, Function.comp_def, ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hR

/-- A common smooth source-bearing approximation on one chain carrier passes the
finite inhomogeneous Harnack inequality to its uniform limit. -/
theorem exists_parabolic_harnack_limit_of_aligned_source_approximations
    (d : Nat) (hd : 1 <= d) (lam : Real) (hlam : 0 < lam)
    (Lam : Real) (hlamLam : lam <= Lam) :
    ∃ h C : Real, 0 < h ∧ h <= 1 ∧ 0 < C ∧
      ∀ (K U : Set (TimeVelocity d))
        (B : Nat -> CoefficientField d)
        (v R : Nat -> TimeVelocity d -> Real)
        (q : TimeVelocity d -> Real),
        IsCompact K -> K ⊆ U -> IsOpen U ->
        (∀ z ∈ PDE.euclideanBall (0 : PDE.Vec d) 1,
          ∀ k ≤ harnackChainLength d,
            harnackChainClosedLinkBox z k ⊆ K) ->
        TendstoUniformlyOn v q atTop K ->
        Tendsto (fun n => parabolicELpNormOn d (R n) K)
          atTop (nhds 0) ->
        (∀ᶠ n in atTop,
          IsSmoothCoefficient (B n) ∧
          ContDiff Real (↑(⊤ : ℕ∞)) (v n) ∧
          IsNonnegativeOn (v n) K ∧
          HasLowerEllipticityOn lam (B n) K ∧
          HasUpperEllipticityOn Lam (B n) K ∧
          (∀ x ∈ K, parabolicOperator (B n) (v n) x = R n x)) ->
        ∀ z ∈ PDE.euclideanBall (0 : PDE.Vec d) 1,
          h * q harnackSource <= q (4, z) := by
  obtain ⟨h, C, hh0, hh1, hC, hchain⟩ :=
    exists_parabolic_harnack_fixed_chain_of_source d hd lam hlam Lam hlamLam
  refine ⟨h, C, hh0, hh1, hC, ?_⟩
  intro K U B v R q hK hKU hU hlinks hUniform hR hraw z hz
  let F : Nat -> TimeVelocity d -> Real := fun n x => parabolicOperator (B n) (v n) x
  have hFnorm : Tendsto (fun n => parabolicELpNormOn d (F n) K) atTop (nhds 0) := by
    apply Tendsto.congr' ?_ hR
    filter_upwards [hraw] with n hn
    have hcarrierAE : F n =ᵐ[volume.restrict K] R n := by
      filter_upwards [ae_restrict_mem hK.measurableSet] with x hxK
      exact hn.2.2.2.2.2 x hxK
    have hnorm : parabolicELpNormOn d (F n) K = parabolicELpNormOn d (R n) K := by
      simpa only [parabolicELpNormOn] using eLpNorm_congr_ae hcarrierAE
    exact hnorm.symm
  have hFreal : Tendsto (fun n => parabolicLpNormOn d (F n) K) atTop (nhds 0) :=
    tendsto_parabolicLpNormOn_of_tendsto_parabolicELpNormOn_zero hFnorm
  let ε : Nat -> Real := fun n => C * parabolicLpNormOn d (F n) K
  have hε : Tendsto ε atTop (nhds 0) := by
    simpa only [ε, mul_zero] using tendsto_const_nhds.mul hFreal
  have hsourceMem : harnackSource ∈ K := by
    have hzero : (0 : PDE.Vec d) ∈ PDE.euclideanBall (0 : PDE.Vec d) 1 := by
      change PDE.euclideanSqDist (0 : PDE.Vec d) 0 < 1 ^ 2
      rw [PDE.euclideanSqDist_self]
      norm_num
    apply hlinks 0 hzero 0 (Nat.zero_le _)
    change (1, (0 : PDE.Vec d)) ∈ harnackChainClosedLinkBox 0 0
    rw [harnackChainClosedLinkBox, mem_parabolicClosedBox_iff,
      harnackChainTime_zero, harnackChainVelocity_zero]
    refine ⟨by nlinarith [sq_nonneg (harnackChainRadius d)],
      by nlinarith [sq_nonneg (harnackChainRadius d)], ?_⟩
    intro i
    simpa using (harnackChainRadius_pos hd).le
  have htargetSubset : harnackTargetSlice ⊆ K := by
    intro x hx
    rcases x with ⟨t, z'⟩
    rcases (mem_harnackTargetSlice_iff.mp hx) with ⟨ht, hz'⟩
    subst t
    apply hlinks z' hz' (harnackChainLength d) le_rfl
    rw [harnackChainClosedLinkBox, mem_parabolicClosedBox_iff,
      harnackChainTime_terminal hd, harnackChainVelocity_terminal hd z']
    refine ⟨by nlinarith [sq_nonneg (harnackChainRadius d)],
      by nlinarith [sq_nonneg (harnackChainRadius d)], ?_⟩
    intro i
    simpa using (harnackChainRadius_pos hd).le
  have hEventually : ∀ᶠ n in atTop, ∀ x ∈ harnackTargetSlice,
      h * v n harnackSource <= v n x + ε n := by
    filter_upwards [hraw] with n hn
    have hcont : ContinuousOn (F n) U :=
      (continuous_parabolicOperator_of_smooth hn.1 hn.2.1).continuousOn
    have hvalue : ContDiffOn Real 2 (v n) U := by
      apply contDiffOn_of_global
      exact hn.2.1.of_le (by exact WithTop.coe_le_coe.mpr le_top)
    have hBcontinuous : IsContinuousCoefficient (B n) := by
      change Continuous (fun x i j => coefficientAt (B n) x i j)
      rw [continuous_pi_iff]
      intro i
      rw [continuous_pi_iff]
      intro j
      exact hn.1.continuous.matrix_elem i j
    have hineq := hchain K U (B n) (v n) (F n) hK hKU hU hlinks
      (IsContinuousCoefficientOn.of_global hBcontinuous U) hvalue hcont hn.2.2.1
      hn.2.2.2.1 hn.2.2.2.2.1 (fun x hx => rfl)
    intro x hx
    rcases x with ⟨t, z'⟩
    rcases (mem_harnackTargetSlice_iff.mp hx) with ⟨ht, hz'⟩
    subst t
    simpa only [ε] using hineq z' hz'
  have hlimit := harnack_limit_of_tendstoUniformlyOn_of_eventually_le_add
    hsourceMem htargetSubset hUniform hε hEventually
  exact hlimit (4, z) (mem_harnackTargetSlice_iff.mpr ⟨rfl, hz⟩)

/-- The continuous representative of a nonnegative local weak solution obeys the
normalized finite-chain Harnack inequality through the aligned mollifier route. -/
theorem exists_parabolic_harnack_of_nonnegative_weak_solution
    (d : Nat) (hd : 1 <= d) (lam : Real) (hlam : 0 < lam)
    (Lam : Real) (hlamLam : lam <= Lam) :
    ∃ h : Real, 0 < h ∧ h <= 1 ∧
      ∀ (A Aext : CoefficientField d)
        (U K : Set (TimeVelocity d))
        (u q : TimeVelocity d -> Real),
        IsOpen U -> IsCompact K -> K ⊆ U ->
        (∀ z ∈ PDE.euclideanBall (0 : PDE.Vec d) 1,
          ∀ k ≤ harnackChainLength d,
            harnackChainClosedLinkBox z k ⊆ K) ->
        coefficientAt Aext =ᵐ[timeVelocityVolumeOn U] coefficientAt A ->
        IsBorelCoefficient Aext ->
        HasLowerEllipticity lam Aext ->
        HasUpperEllipticity Lam Aext ->
        IsWeakParabolicEquationLoc A U (parabolicExponent d) u ->
        (∀ᵐ z ∂timeVelocityVolumeOn U, 0 <= u z) ->
        ContinuousOn q U -> q =ᵐ[timeVelocityVolumeOn U] u ->
        ∀ z ∈ PDE.euclideanBall (0 : PDE.Vec d) 1,
          h * q harnackSource <= q (4, z) := by
  obtain ⟨h, C, hh0, hh1, _hC, hGeneric⟩ :=
    exists_parabolic_harnack_limit_of_aligned_source_approximations d hd lam hlam Lam hlamLam
  refine ⟨h, hh0, hh1, ?_⟩
  intro A Aext U K u q hU hK hKU hlinks hExtAE hExtBorel hExtLower hExtUpper hWeak
    huNonneg hq hqu
  obtain ⟨J, hUniform, hResidual, hTail⟩ :=
    exists_localizedJet_eventually_nonnegative_residual_mollifications_tendsto d hd lam Lam
      A Aext U K u q hU hK hKU hExtAE hExtBorel hExtLower hExtUpper hWeak huNonneg hq hqu
  exact hGeneric K U
    (fun n => parabolicMollifyCoefficient Aext n)
    (fun n => parabolicMollifiedValue J.g n)
    (fun n => weakEquationMollificationResidual Aext J.g n)
    q hK hKU hU hlinks hUniform (by simpa only [parabolicELpNormOn] using hResidual) (by
      filter_upwards [hTail] with n hn
      exact ⟨hn.1, hn.2.2.2.2.1, hn.2.2.2.2.2.1,
        HasLowerEllipticityOn.of_global hn.2.2.1 K,
        HasUpperEllipticityOn.of_global hn.2.2.2.1 K, hn.2.2.2.2.2.2⟩)

end HypoellipticAleksandrov.Parabolic

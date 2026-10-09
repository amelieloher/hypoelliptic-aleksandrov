module

public import HypoellipticAleksandrov.Parabolic.MovingDomainMaximum
public import HypoellipticAleksandrov.Parabolic.MovingLensSign
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Small-seed moving-lens comparison

This module proves the principal-part classical comparison core in the
small-seed branch of Krylov--Safonov Lemma 1.3.  The compact causal minimum
principle is applied to the difference between a supplied supersolution and
the strictly signed moving-lens barrier.  The initial and lateral boundary
calculations are performed here; neither is an extra hypothesis.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter Set
open scoped MatrixOrder Topology

private theorem parabolicOperator_const_smul
    {d : ℕ} (A : CoefficientField d) (c : ℝ)
    (u : TimeVelocity d → ℝ) (z : TimeVelocity d) :
    parabolicOperator A (c • u) z = c * parabolicOperator A u z := by
  have hfirst : fderiv ℝ (c • u) = c • fderiv ℝ u :=
    fderiv_const_smul_field c
  have htime : timeDerivative (c • u) z = c * timeDerivative u z := by
    unfold timeDerivative
    rw [fderiv_const_smul_field]
    rfl
  have hhessian : velocityHessian (c • u) z = c • velocityHessian u z := by
    have hsecond : fderiv ℝ (fderiv ℝ (c • u)) z =
        c • fderiv ℝ (fderiv ℝ u) z := by
      rw [hfirst]
      exact congrFun (fderiv_const_smul_field (f := fderiv ℝ u) c) z
    ext i j
    unfold velocityHessian
    rw [hsecond]
    rfl
  rw [parabolicOperator_apply, parabolicOperator_apply, htime, hhessian,
    HypoellipticAleksandrov.matrixContraction_smul_right]
  ring

private theorem parabolicOperator_sub_of_contDiffAt
    {d : ℕ} (A : CoefficientField d) (u v : TimeVelocity d → ℝ)
    (z : TimeVelocity d) (hu : ContDiffAt ℝ 2 u z)
    (hv : ContDiffAt ℝ 2 v z) :
    parabolicOperator A (fun q => u q - v q) z =
      parabolicOperator A u z - parabolicOperator A v z := by
  have huDiff : DifferentiableAt ℝ u z := hu.differentiableAt (by norm_num)
  have hvDiff : DifferentiableAt ℝ v z := hv.differentiableAt (by norm_num)
  have hfirst : fderiv ℝ (fun q => u q - v q) =ᶠ[𝓝 z]
      fun q => fderiv ℝ u q - fderiv ℝ v q := by
    filter_upwards [hu.eventually (by norm_num), hv.eventually (by norm_num)]
      with q huq hvq
    exact fderiv_fun_sub (huq.differentiableAt (by norm_num))
      (hvq.differentiableAt (by norm_num))
  have huFirstDiff : DifferentiableAt ℝ (fderiv ℝ u) z :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hvFirstDiff : DifferentiableAt ℝ (fderiv ℝ v) z :=
    (hv.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsecond : fderiv ℝ (fderiv ℝ (fun q => u q - v q)) z =
      fderiv ℝ (fderiv ℝ u) z - fderiv ℝ (fderiv ℝ v) z := by
    calc
      fderiv ℝ (fderiv ℝ (fun q => u q - v q)) z =
          fderiv ℝ (fun q => fderiv ℝ u q - fderiv ℝ v q) z :=
        hfirst.fderiv_eq
      _ = fderiv ℝ (fderiv ℝ u) z - fderiv ℝ (fderiv ℝ v) z :=
        fderiv_fun_sub huFirstDiff hvFirstDiff
  have htime : timeDerivative (fun q => u q - v q) z =
      timeDerivative u z - timeDerivative v z := by
    unfold timeDerivative
    rw [fderiv_fun_sub huDiff hvDiff]
    rfl
  have hhessian : velocityHessian (fun q => u q - v q) z =
      velocityHessian u z - velocityHessian v z := by
    ext i j
    unfold velocityHessian
    rw [hsecond]
    rfl
  rw [parabolicOperator_apply, parabolicOperator_apply, parabolicOperator_apply,
    htime, hhessian]
  simp only [sub_eq_add_neg, HypoellipticAleksandrov.matrixContraction_add_right,
    HypoellipticAleksandrov.matrixContraction_neg_right]
  ring

private theorem movingLensSignXi_nonneg {kappa : ℝ} (hkappa : 0 < kappa) :
    0 ≤ movingLensSignXi kappa := by
  unfold movingLensSignXi
  positivity

private theorem movingLensSignExponent_pos (d : ℕ) (lam Lam kappa : ℝ) :
    0 < movingLensSignExponent d lam Lam kappa := by
  unfold movingLensSignExponent
  omega

/-- The small-seed moving-lens comparison at its terminal centre. -/
theorem movingLens_terminal_lower_bound
    (d : ℕ) (lam Lam kappa : ℝ)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hkappa : 0 < kappa) (hkappa_one : kappa ≤ 1)
    (A : CoefficientField d) (u : TimeVelocity d → ℝ)
    (tau eps ell : ℝ) (y : PDE.Vec d)
    (htau : 0 < tau) (htau_upper : tau ≤ kappa⁻¹)
    (heps : 0 < eps) (hsmall : 2 * eps ^ 2 < kappa ^ 2)
    (hell : 0 < ell)
    (hy : PDE.vecNormSq y ≤ (d : ℝ) * kappa ^ (-4 : ℤ))
    (hucont : ContinuousOn u
      (movingLensClosed (movingLensSignXi kappa) eps tau y))
    (hudiff : ∀ z ∈ movingLensActive
      (movingLensSignXi kappa) eps tau y, ContDiffAt ℝ 2 u z)
    (hunonneg : IsNonnegativeOn u
      (movingLensClosed (movingLensSignXi kappa) eps tau y))
    (hlower : HasLowerEllipticityOn lam A
      (movingLensActive (movingLensSignXi kappa) eps tau y))
    (hupper : HasUpperEllipticityOn Lam A
      (movingLensActive (movingLensSignXi kappa) eps tau y))
    (hsuper : IsParabolicSupersolutionOn A (fun _ ↦ 0) u
      (movingLensActive (movingLensSignXi kappa) eps tau y))
    (hseed : ∀ v : PDE.Vec d,
      PDE.vecNormSq v < eps ^ 2 → ell ≤ u (0, v)) :
    ell * eps ^ (2 * movingLensSignExponent d lam Lam kappa) /
        kappa ^ (2 * movingLensSignExponent d lam Lam kappa) <
      u (tau, tau • y) := by
  let xi := movingLensSignXi kappa
  let n := movingLensSignExponent d lam Lam kappa
  let psi : TimeVelocity d → ℝ := movingLensBarrier xi eps n y
  let c : ℝ := ell * eps ^ (2 * n)
  let w : TimeVelocity d → ℝ := fun z => u z - c * psi z
  have hxi : 0 ≤ xi := by
    dsimp only [xi]
    exact movingLensSignXi_nonneg hkappa
  have hn : 0 < n := by
    dsimp only [n]
    exact movingLensSignExponent_pos d lam Lam kappa
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  have hDK : movingLensActive xi eps tau y ⊆ movingLensClosed xi eps tau y :=
    movingLensActive_subset_movingLensClosed xi eps tau y
  have hKcompact : IsCompact (movingLensClosed xi eps tau y) :=
    isCompact_movingLensClosed hxi heps htau.le
  have hpsiCont : ContinuousOn psi (movingLensClosed xi eps tau y) := by
    intro z hz
    have hden : 0 < movingLensDenominator xi eps z.1 :=
      movingLensDenominator_pos hxi heps hz.1
    exact (contDiffAt_movingLensBarrier hden.ne').continuousAt.continuousWithinAt
  have hwcont : ContinuousOn w (movingLensClosed xi eps tau y) := by
    exact hucont.sub (continuousOn_const.mul hpsiCont)
  have hDpast : ∀ z ∈ movingLensActive xi eps tau y,
      movingLensActive xi eps tau y ∈ 𝓝[Iic z.1 ×ˢ Set.univ] z := by
    intro z hz
    exact movingLensActive_mem_nhdsWithin_past hz
  have hwDiff : ∀ z ∈ movingLensActive xi eps tau y, ContDiffAt ℝ 2 w z := by
    intro z hz
    have hden : 0 < movingLensDenominator xi eps z.1 :=
      movingLensDenominator_pos hxi heps hz.1.le
    have hpsi : ContDiffAt ℝ 2 psi z := by
      exact contDiffAt_movingLensBarrier hden.ne'
    exact (hudiff z hz).sub (ContDiffAt.const_smul c hpsi)
  have hApsd : ∀ z ∈ movingLensActive xi eps tau y,
      (coefficientAt A z).PosSemidef := by
    intro z hz
    exact (posDef_of_loewner_lower hlam (hlower z hz)).posSemidef
  have hPpos : ∀ z ∈ movingLensActive xi eps tau y,
      0 < parabolicOperator A w z := by
    intro z hz
    have hden : 0 < movingLensDenominator xi eps z.1 :=
      movingLensDenominator_pos hxi heps hz.1.le
    have hden_lt : movingLensDenominator xi eps z.1 < kappa ^ 2 := by
      dsimp only [xi]
      unfold movingLensDenominator movingLensSignXi
      have hslope : kappa ^ 3 / 2 * z.1 ≤ kappa ^ 2 / 2 := by
        have hleft : kappa ^ 3 / 2 * z.1 ≤ kappa ^ 3 / 2 * kappa⁻¹ :=
          mul_le_mul_of_nonneg_left (hz.2.1.trans htau_upper) (by positivity)
        calc
          kappa ^ 3 / 2 * z.1 ≤ kappa ^ 3 / 2 * kappa⁻¹ := hleft
          _ = kappa ^ 2 / 2 := by
            field_simp [hkappa.ne']
      nlinarith
    have hr : movingLensRadiusSq xi eps y z < 1 :=
      (movingLensRadiusSq_lt_one_iff hden).2 hz.2.2
    have hpsiNeg : parabolicOperator A psi z < 0 := by
      dsimp only [psi, xi, n]
      exact parabolicOperator_movingLensBarrier_lt_zero_of_pointwise_loewner
        d lam Lam kappa hlam hlamLam hkappa hkappa_one A y z eps
        (by simpa only [xi] using hden) (by simpa only [xi] using hden_lt)
        hy (by simpa only [xi] using hr) (hlower z hz) (hupper z hz)
    have hoperator : parabolicOperator A w z =
        parabolicOperator A u z - c * parabolicOperator A psi z := by
      dsimp only [w]
      calc
        parabolicOperator A (fun q => u q - c * psi q) z =
            parabolicOperator A u z - parabolicOperator A (c • psi) z := by
          simpa only [Pi.smul_apply, smul_eq_mul] using
            parabolicOperator_sub_of_contDiffAt A u (c • psi) z (hudiff z hz)
              ((contDiffAt_movingLensBarrier hden.ne').const_smul c)
        _ = parabolicOperator A u z - c * parabolicOperator A psi z := by
          rw [parabolicOperator_const_smul]
    rw [hoperator]
    have hu : 0 ≤ parabolicOperator A u z := by
      simpa only using hsuper z hz
    nlinarith [mul_pos hc (neg_pos.mpr hpsiNeg)]
  have hboundary : ∀ z ∈ movingLensClosed xi eps tau y \
      movingLensActive xi eps tau y, 0 ≤ w z := by
    intro z hz
    rw [mem_movingLensClosed_diff_active_iff] at hz
    rcases hz with hinitial | hlateral
    · rcases hinitial with ⟨hzTime, hzTau, hzSpatial⟩
      have hden : 0 < movingLensDenominator xi eps z.1 :=
        movingLensDenominator_pos hxi heps hzTime.ge
      have hdispInitial : movingLensDisplacement y z = z.2 := by
        unfold movingLensDisplacement
        rw [hzTime, zero_smul, sub_zero]
      have hdenInitial : movingLensDenominator xi eps z.1 = eps ^ 2 := by
        unfold movingLensDenominator
        rw [hzTime, mul_zero, zero_add]
      by_cases hstrict : PDE.vecNormSq (movingLensDisplacement y z) <
          movingLensDenominator xi eps z.1
      · have hseedPoint : ell ≤ u z := by
          have hball : PDE.vecNormSq z.2 < eps ^ 2 := by
            simpa only [hdispInitial, hdenInitial] using hstrict
          have hzEq : z = (0, z.2) := by
            apply Prod.ext
            · exact hzTime
            · rfl
          rw [hzEq]
          exact hseed z.2 hball
        have hrnonneg : 0 ≤ movingLensRadiusSq xi eps y z := by
          unfold movingLensRadiusSq
          exact div_nonneg (PDE.vecNormSq_nonneg _) hden.le
        have hrle : movingLensRadiusSq xi eps y z ≤ 1 :=
          (movingLensRadiusSq_le_one_iff hden).2 hzSpatial
        have hrproduct : 0 ≤ movingLensRadiusSq xi eps y z *
            (2 - movingLensRadiusSq xi eps y z) :=
          mul_nonneg hrnonneg (by linarith)
        have hfactor : (1 - movingLensRadiusSq xi eps y z) ^ 2 ≤ 1 := by
          nlinarith [hrproduct]
        have hpow : 0 < (eps ^ 2) ^ n :=
          pow_pos (sq_pos_of_pos heps) _
        have hbarrier : c * psi z ≤ ell := by
          calc
            c * psi z = ell * (1 - movingLensRadiusSq xi eps y z) ^ 2 := by
              dsimp only [c, psi, movingLensBarrier]
              rw [hdenInitial]
              rw [show eps ^ (2 * n) = (eps ^ 2) ^ n by ring]
              field_simp [hpow.ne']
            _ ≤ ell * 1 := mul_le_mul_of_nonneg_left hfactor hell.le
            _ = ell := mul_one ell
        dsimp only [w]
        linarith
      · have hspatialEq : PDE.vecNormSq (movingLensDisplacement y z) =
          movingLensDenominator xi eps z.1 :=
          le_antisymm hzSpatial (le_of_not_gt hstrict)
        have hbarrierZero : psi z = 0 := by
          dsimp only [psi, movingLensBarrier, movingLensRadiusSq]
          rw [hspatialEq]
          field_simp [hden.ne']
          ring
        dsimp only [w]
        rw [hbarrierZero, mul_zero, sub_zero]
        exact hunonneg z ⟨hzTime.ge, hzTau, hzSpatial⟩
    · rcases hlateral with ⟨hzTime, hzTau, hspatialEq⟩
      have hden : 0 < movingLensDenominator xi eps z.1 :=
        movingLensDenominator_pos hxi heps hzTime
      have hbarrierZero : psi z = 0 := by
        dsimp only [psi, movingLensBarrier, movingLensRadiusSq]
        rw [hspatialEq]
        field_simp [hden.ne']
        ring
      dsimp only [w]
      rw [hbarrierZero, mul_zero, sub_zero]
      exact hunonneg z ⟨hzTime, hzTau, hspatialEq.le⟩
  have hwNonneg : IsNonnegativeOn w (movingLensClosed xi eps tau y) :=
    isNonnegativeOn_of_strict_parabolicOperator_of_compact hDK hKcompact hwcont
      hDpast hwDiff hApsd hPpos hboundary
  have hterminal : (tau, tau • y) ∈ movingLensActive xi eps tau y := by
    have hcenter : tau⁻¹ • (tau • y) = y := by
      rw [smul_smul, inv_mul_cancel₀ htau.ne', one_smul]
    simpa only [hcenter] using
      terminalCenter_mem_movingLensActive hxi heps htau (tau • y)
  have hterminalNonneg := hwNonneg (tau, tau • y)
    (movingLensActive_subset_movingLensClosed xi eps tau y hterminal)
  have hdenTerminal : movingLensDenominator xi eps tau < kappa ^ 2 := by
    dsimp only [xi]
    unfold movingLensDenominator movingLensSignXi
    have hslope : kappa ^ 3 / 2 * tau ≤ kappa ^ 2 / 2 := by
      calc
        kappa ^ 3 / 2 * tau ≤ kappa ^ 3 / 2 * kappa⁻¹ :=
          mul_le_mul_of_nonneg_left htau_upper (by positivity)
        _ = kappa ^ 2 / 2 := by
          field_simp [hkappa.ne']
    nlinarith
  have hdenTerminalPos : 0 < movingLensDenominator xi eps tau :=
    movingLensDenominator_pos hxi heps htau.le
  have hpsiTerminal : psi (tau, tau • y) =
      1 / (movingLensDenominator xi eps tau) ^ n := by
    dsimp only [psi, movingLensBarrier]
    have hdisp : movingLensDisplacement y (tau, tau • y) = 0 := by
      unfold movingLensDisplacement
      rw [sub_self]
    have hradius : movingLensRadiusSq xi eps y (tau, tau • y) = 0 := by
      unfold movingLensRadiusSq
      rw [hdisp]
      simp only [PDE.vecNormSq, PDE.vecDot, Pi.zero_apply, mul_zero,
        Finset.sum_const_zero, zero_div]
    rw [hradius]
    simp only [sub_zero, one_pow]
  have hcomparison : c / (movingLensDenominator xi eps tau) ^ n ≤
      u (tau, tau • y) := by
    dsimp only [w] at hterminalNonneg
    rw [hpsiTerminal] at hterminalNonneg
    have : c * (1 / (movingLensDenominator xi eps tau) ^ n) =
        c / (movingLensDenominator xi eps tau) ^ n := by ring
    rw [this] at hterminalNonneg
    linarith
  have hdenPow : (movingLensDenominator xi eps tau) ^ n < (kappa ^ 2) ^ n :=
    pow_lt_pow_left₀ (by simpa only [xi] using hdenTerminal)
      hdenTerminalPos.le hn.ne'
  have hstrict : ell * eps ^ (2 * n) / kappa ^ (2 * n) <
      c / (movingLensDenominator xi eps tau) ^ n := by
    have hrightPos : 0 < (movingLensDenominator xi eps tau) ^ n :=
      pow_pos hdenTerminalPos _
    calc
      ell * eps ^ (2 * n) / kappa ^ (2 * n) = c / (kappa ^ 2) ^ n := by
        dsimp only [c]
        rw [show kappa ^ (2 * n) = (kappa ^ 2) ^ n by ring]
      _ < c / (movingLensDenominator xi eps tau) ^ n :=
        div_lt_div_of_pos_left hc hrightPos hdenPow
  exact hstrict.trans_le (by simpa only [c, n] using hcomparison)

end HypoellipticAleksandrov.Parabolic

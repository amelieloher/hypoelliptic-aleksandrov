module

public import HypoellipticAleksandrov.Parabolic.ForwardPropagationGeometry
public import HypoellipticAleksandrov.Parabolic.MovingLensComparison
public import HypoellipticAleksandrov.Parabolic.Scaling
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Normalized forward propagation

This module proves the normalized classical forward-propagation estimate from
the moving-lens comparison.  The equation and ellipticity data are used only
in the open physical rectangle.  The closed-time conclusion is recovered at
the top face by a genuine interior-time limit and consequently uses the
strictly smaller advertised constant.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter Set
open scoped MatrixOrder Topology

/-- The power of the initial relative radius in forward propagation. -/
def forwardPropagationExponent (d : ℕ) (lam Lam kappa : ℝ) : ℕ :=
  2 * movingLensSignExponent d lam Lam kappa

/-- The strict closed-corridor forward-propagation constant. -/
def forwardPropagationDelta (d : ℕ) (lam Lam kappa : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (1 / 4 : ℝ) ^ movingLensSignExponent d lam Lam kappa

/-- The forward-propagation radius exponent is positive. -/
theorem forwardPropagationExponent_pos
    (d : ℕ) (lam Lam kappa : ℝ) :
    0 < forwardPropagationExponent d lam Lam kappa := by
  unfold forwardPropagationExponent
  have hn : 0 < movingLensSignExponent d lam Lam kappa := by
    unfold movingLensSignExponent
    omega
  omega

/-- The strict closed-corridor forward-propagation constant is positive. -/
theorem forwardPropagationDelta_pos
    (d : ℕ) (lam Lam kappa : ℝ) :
    0 < forwardPropagationDelta d lam Lam kappa := by
  unfold forwardPropagationDelta
  exact mul_pos (by norm_num) (pow_pos (by norm_num) _)

/-- Interior times tending increasingly to the physical top face. -/
private def forwardPropagationInteriorTime (kappa tau : ℝ) (j : ℕ) : ℝ :=
  tau - (tau - kappa) / (j + 1 : ℝ)

private theorem kappa_lt_forwardPropagationInteriorTime
    {kappa tau : ℝ} (htau : kappa < tau) {j : ℕ} (hj : 0 < j) :
    kappa < forwardPropagationInteriorTime kappa tau j := by
  unfold forwardPropagationInteriorTime
  have hjone : 1 < (j + 1 : ℝ) := by
    exact_mod_cast Nat.succ_lt_succ hj
  have hden : 0 < (j + 1 : ℝ) := by positivity
  have hdiv : (tau - kappa) / (j + 1 : ℝ) < tau - kappa :=
    (div_lt_iff₀ hden).2 (by nlinarith [sub_pos.mpr htau])
  nlinarith

private theorem forwardPropagationInteriorTime_lt_tau
    {kappa tau : ℝ} (htau : kappa < tau) (j : ℕ) :
    forwardPropagationInteriorTime kappa tau j < tau := by
  unfold forwardPropagationInteriorTime
  rw [sub_lt_iff_lt_add]
  exact lt_add_of_pos_right _ (div_pos (sub_pos.mpr htau) (by positivity))

private theorem tendsto_forwardPropagationInteriorTime
    (kappa tau : ℝ) :
    Tendsto (forwardPropagationInteriorTime kappa tau) atTop (𝓝 tau) := by
  unfold forwardPropagationInteriorTime
  have hdiv : Tendsto (fun j : ℕ => (tau - kappa) / (j + 1 : ℝ)) atTop
      (𝓝 0) := by
    simpa only [div_eq_mul_inv, one_mul, mul_zero] using
      (Tendsto.const_mul (tau - kappa)
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun j : ℕ => 1 / (j + 1 : ℝ)) atTop (𝓝 0)))
  simpa using tendsto_const_nhds.sub hdiv

private theorem small_seed_radius_lt_kappa {rho kappa : ℝ}
    (hrho : 0 < rho) (hkappa : 0 < kappa)
    (hsmall : 2 * rho ^ 2 < kappa ^ 2) :
    rho < kappa := by
  nlinarith [sq_nonneg (rho + kappa)]

private theorem large_seed_radius_le {eps kappa : ℝ}
    (heps : 0 < eps) (hkappa : 0 < kappa)
    (hlarge : ¬ 2 * eps ^ 2 < kappa ^ 2) :
    kappa / 2 ≤ eps := by
  have hsq : kappa ^ 2 ≤ 2 * eps ^ 2 := le_of_not_gt hlarge
  have hhalfSq : (kappa / 2) ^ 2 ≤ eps ^ 2 := by nlinarith
  exact (sq_le_sq₀ (by positivity) heps.le).1 hhalfSq

private theorem half_kappa_small {kappa : ℝ} (hkappa : 0 < kappa) :
    2 * (kappa / 2) ^ 2 < kappa ^ 2 := by
  nlinarith [sq_pos_of_pos hkappa]

private theorem seed_lower_bound_on_ball
    {d : ℕ} {lower upper : PDE.Vec d} {kappa rho eps ell : ℝ}
    {u : TimeVelocity d → ℝ}
    (hrho : 0 < rho) (hrhoEps : rho ≤ eps) (hrhoKappa : rho < kappa)
    (hbase : ∀ i, lower i + kappa ≤ 0 ∧ 0 < upper i - kappa)
    (hseed : ∀ v ∈ velocityClosedRectangle lower upper,
      v ∈ velocityCube (0 : PDE.Vec d) eps → ell ≤ u (0, v)) :
    ∀ v : PDE.Vec d, PDE.vecNormSq v < rho ^ 2 → ell ≤ u (0, v) := by
  intro v hv
  have hvBall : v ∈ PDE.euclideanBall (0 : PDE.Vec d) rho := by
    simpa only [PDE.euclideanBall, PDE.euclideanSqDist, Set.mem_setOf_eq, sub_zero] using hv
  have hcontain := euclideanBall_subset_velocityCube_inter_velocityRectangle
    hrho hrhoEps hrhoKappa (fun i => ⟨(hbase i).1, (hbase i).2.le⟩) hvBall
  apply hseed v
  · intro i
    exact ⟨(hcontain.2 i).1.le, (hcontain.2 i).2.le⟩
  · exact hcontain.1

/-- Sharp normalized interior forward propagation.

The coefficient bounds and supersolution inequality are used only on the open
physical rectangle. -/
theorem forward_propagation_normalized_interior
    (d : ℕ) (lam Lam kappa : ℝ)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hkappa : 0 < kappa) (hkappa_one : kappa ≤ 1)
    (A : CoefficientField d) (lower upper : PDE.Vec d) (tau : ℝ)
    (U : Set (TimeVelocity d)) (u : TimeVelocity d → ℝ)
    (eps ell tStar : ℝ) (vStar : PDE.Vec d)
    (htauLower : kappa < tau) (htauUpper : tau ≤ kappa⁻¹)
    (hwidth : ∀ i, 2 * kappa < upper i - lower i ∧
      upper i - lower i ≤ kappa⁻¹)
    (hbase : ∀ i, lower i + kappa ≤ 0 ∧ 0 < upper i - kappa)
    (hU : IsOpen U)
    (hclosedU : parabolicClosedRectangle tau lower upper ⊆ U)
    (hu : ContDiffOn ℝ 2 u U)
    (hnonneg : IsNonnegativeOn u (parabolicRectangle tau lower upper))
    (hlower : HasLowerEllipticityOn lam A
      (parabolicRectangle tau lower upper))
    (hupper : HasUpperEllipticityOn Lam A
      (parabolicRectangle tau lower upper))
    (hsuper : IsParabolicSupersolutionOn A (fun _ ↦ 0) u
      (parabolicRectangle tau lower upper))
    (heps : 0 < eps) (hepsOne : eps ≤ 1) (hell : 0 < ell)
    (hseed : ∀ v ∈ velocityClosedRectangle lower upper,
      v ∈ velocityCube (0 : PDE.Vec d) eps → ell ≤ u (0, v))
    (htStarLower : kappa < tStar) (htStarUpper : tStar < tau)
    (htarget : ∀ i, lower i + kappa < vStar i ∧
      vStar i < upper i - kappa) :
    (1 / 4 : ℝ) ^ movingLensSignExponent d lam Lam kappa *
        eps ^ forwardPropagationExponent d lam Lam kappa * ell <
      u (tStar, vStar) := by
  let n := movingLensSignExponent d lam Lam kappa
  have hn : 0 < n := by
    dsimp only [n]
    unfold movingLensSignExponent
    omega
  have htStarPos : 0 < tStar := hkappa.trans htStarLower
  have htauPos : 0 < tau := hkappa.trans htauLower
  have hfaces : ∀ i, lower i < upper i := by
    intro i
    nlinarith [(hwidth i).1]
  have hzero : (0 : PDE.Vec d) ∈ velocityClosedRectangle lower upper := by
    intro i
    simpa only [Pi.zero_apply] using
      ⟨by nlinarith [(hbase i).1], by nlinarith [(hbase i).2]⟩
  have hvStar : vStar ∈ velocityClosedRectangle lower upper := by
    intro i
    exact ⟨by nlinarith [(htarget i).1], by nlinarith [(htarget i).2]⟩
  have hy : PDE.vecNormSq (tStar⁻¹ • vStar) ≤
      (d : ℝ) * kappa ^ (-4 : ℤ) :=
    vecNormSq_inv_smul_le_of_mem_rectangle hkappa htStarLower.le
      (fun i => (hwidth i).2) hzero hvStar
  have hrectNonneg : IsNonnegativeOn u
      (parabolicClosedRectangle tau lower upper) := by
    apply IsNonnegativeOn.parabolicClosedRectangle htauPos hfaces
      (hu.continuousOn.mono hclosedU) hnonneg
  have hpowFour : (1 / 4 : ℝ) ^ n < 1 := by
    apply pow_lt_one₀ (by norm_num) (by norm_num)
    omega
  have hbasePow : 0 < eps ^ (2 * n) * ell := by positivity
  by_cases hsmall : 2 * eps ^ 2 < kappa ^ 2
  · have hepsKappa : eps < kappa :=
      small_seed_radius_lt_kappa heps hkappa hsmall
    have hclosedLens : movingLensClosed (movingLensSignXi kappa) eps tStar
        (tStar⁻¹ • vStar) ⊆ parabolicClosedRectangle tau lower upper :=
      movingLensClosed_subset_parabolicClosedRectangle hkappa heps hsmall
        htStarPos htStarUpper.le htauUpper
        (fun i => ⟨(hbase i).1, (hbase i).2.le⟩)
        (fun i => ⟨(htarget i).1.le, (htarget i).2.le⟩)
    have hactiveLens : movingLensActive (movingLensSignXi kappa) eps tStar
        (tStar⁻¹ • vStar) ⊆ parabolicRectangle tau lower upper :=
      movingLensActive_subset_parabolicRectangle hkappa heps hsmall
        htStarPos htStarUpper htauUpper
        (fun i => ⟨(hbase i).1, (hbase i).2.le⟩)
        (fun i => ⟨(htarget i).1.le, (htarget i).2.le⟩)
    have hcomparison := movingLens_terminal_lower_bound d lam Lam kappa
      hlam hlamLam hkappa hkappa_one A u tStar eps ell (tStar⁻¹ • vStar)
      htStarPos (htStarUpper.le.trans htauUpper) heps hsmall hell hy
      (hu.continuousOn.mono (hclosedLens.trans hclosedU))
      (fun z hz => contDiffAt_of_contDiffOn_of_isOpen hU hu
        (hclosedU (hclosedLens
          (movingLensActive_subset_movingLensClosed _ _ _ _ hz))))
      (hrectNonneg.mono hclosedLens)
      (hlower.mono hactiveLens) (hupper.mono hactiveLens)
      (hsuper.mono hactiveLens)
      (seed_lower_bound_on_ball heps le_rfl hepsKappa hbase hseed)
    have hkappaPow : kappa ^ (2 * n) ≤ 1 :=
      pow_le_one₀ hkappa.le hkappa_one
    have hmain : (1 / 4 : ℝ) ^ n * (eps ^ (2 * n) * ell) <
        ell * eps ^ (2 * n) / kappa ^ (2 * n) := by
      have hleft : (1 / 4 : ℝ) ^ n * (eps ^ (2 * n) * ell) <
          eps ^ (2 * n) * ell :=
        by
          calc
            (1 / 4 : ℝ) ^ n * (eps ^ (2 * n) * ell) <
                1 * (eps ^ (2 * n) * ell) :=
              mul_lt_mul_of_pos_right hpowFour hbasePow
            _ = eps ^ (2 * n) * ell := one_mul _
      have hright : eps ^ (2 * n) * ell ≤
          ell * eps ^ (2 * n) / kappa ^ (2 * n) := by
        rw [mul_comm ell]
        exact (le_div_iff₀ (pow_pos hkappa _)).2
          (by simpa only [mul_assoc, mul_one] using
            mul_le_mul_of_nonneg_left hkappaPow hbasePow.le)
      exact hleft.trans_le hright
    rw [forwardPropagationExponent]
    simpa only [n, smul_smul, mul_inv_cancel₀ htStarPos.ne', one_smul,
      mul_assoc, mul_left_comm, mul_comm] using hmain.trans hcomparison
  · let rho : ℝ := kappa / 2
    have hrho : 0 < rho := by dsimp only [rho]; positivity
    have hrhoEps : rho ≤ eps := by
      dsimp only [rho]
      exact large_seed_radius_le heps hkappa hsmall
    have hrhoSmall : 2 * rho ^ 2 < kappa ^ 2 := by
      dsimp only [rho]
      exact half_kappa_small hkappa
    have hrhoKappa : rho < kappa := by
      dsimp only [rho]
      linarith
    have hclosedLens : movingLensClosed (movingLensSignXi kappa) rho tStar
        (tStar⁻¹ • vStar) ⊆ parabolicClosedRectangle tau lower upper :=
      movingLensClosed_subset_parabolicClosedRectangle hkappa hrho hrhoSmall
        htStarPos htStarUpper.le htauUpper
        (fun i => ⟨(hbase i).1, (hbase i).2.le⟩)
        (fun i => ⟨(htarget i).1.le, (htarget i).2.le⟩)
    have hactiveLens : movingLensActive (movingLensSignXi kappa) rho tStar
        (tStar⁻¹ • vStar) ⊆ parabolicRectangle tau lower upper :=
      movingLensActive_subset_parabolicRectangle hkappa hrho hrhoSmall
        htStarPos htStarUpper htauUpper
        (fun i => ⟨(hbase i).1, (hbase i).2.le⟩)
        (fun i => ⟨(htarget i).1.le, (htarget i).2.le⟩)
    have hcomparison := movingLens_terminal_lower_bound d lam Lam kappa
      hlam hlamLam hkappa hkappa_one A u tStar rho ell (tStar⁻¹ • vStar)
      htStarPos (htStarUpper.le.trans htauUpper) hrho hrhoSmall hell hy
      (hu.continuousOn.mono (hclosedLens.trans hclosedU))
      (fun z hz => contDiffAt_of_contDiffOn_of_isOpen hU hu
        (hclosedU (hclosedLens
          (movingLensActive_subset_movingLensClosed _ _ _ _ hz))))
      (hrectNonneg.mono hclosedLens)
      (hlower.mono hactiveLens) (hupper.mono hactiveLens)
      (hsuper.mono hactiveLens)
      (seed_lower_bound_on_ball hrho hrhoEps hrhoKappa hbase hseed)
    have hhalfPow : (1 / 4 : ℝ) ^ n = (1 / 2 : ℝ) ^ (2 * n) := by
      calc
        (1 / 4 : ℝ) ^ n = ((1 / 2 : ℝ) ^ 2) ^ n := by norm_num
        _ = (1 / 2 : ℝ) ^ (2 * n) := by rw [pow_mul]
    have hepsPow : eps ^ (2 * n) ≤ 1 :=
      pow_le_one₀ heps.le hepsOne
    have hlargeBound : (1 / 4 : ℝ) ^ n * eps ^ (2 * n) * ell ≤
        ell * rho ^ (2 * n) / kappa ^ (2 * n) := by
      calc
        (1 / 4 : ℝ) ^ n * eps ^ (2 * n) * ell ≤
            (1 / 4 : ℝ) ^ n * 1 * ell := by
          gcongr
        _ = ell * rho ^ (2 * n) / kappa ^ (2 * n) := by
          dsimp only [rho]
          rw [hhalfPow]
          field_simp [pow_ne_zero _ hkappa.ne']
          ring
    rw [forwardPropagationExponent]
    simpa only [n, smul_smul, mul_inv_cancel₀ htStarPos.ne', one_smul,
      mul_assoc, mul_left_comm, mul_comm] using hlargeBound.trans_lt hcomparison

/-- Normalized source-facing forward propagation on the closed time corridor.

Only continuity of `u` at the top is used when `tStar = tau`; no coefficient
or PDE datum is requested there. -/
theorem forward_propagation_normalized
    (d : ℕ) (lam Lam kappa : ℝ)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hkappa : 0 < kappa) (hkappa_one : kappa ≤ 1)
    (A : CoefficientField d) (lower upper : PDE.Vec d) (tau : ℝ)
    (U : Set (TimeVelocity d)) (u : TimeVelocity d → ℝ)
    (eps ell tStar : ℝ) (vStar : PDE.Vec d)
    (htauLower : kappa < tau) (htauUpper : tau ≤ kappa⁻¹)
    (hwidth : ∀ i, 2 * kappa < upper i - lower i ∧
      upper i - lower i ≤ kappa⁻¹)
    (hbase : ∀ i, lower i + kappa ≤ 0 ∧ 0 < upper i - kappa)
    (hU : IsOpen U)
    (hclosedU : parabolicClosedRectangle tau lower upper ⊆ U)
    (hu : ContDiffOn ℝ 2 u U)
    (hnonneg : IsNonnegativeOn u (parabolicRectangle tau lower upper))
    (hlower : HasLowerEllipticityOn lam A
      (parabolicRectangle tau lower upper))
    (hupper : HasUpperEllipticityOn Lam A
      (parabolicRectangle tau lower upper))
    (hsuper : IsParabolicSupersolutionOn A (fun _ ↦ 0) u
      (parabolicRectangle tau lower upper))
    (heps : 0 < eps) (hepsOne : eps ≤ 1) (hell : 0 < ell)
    (hseed : ∀ v ∈ velocityClosedRectangle lower upper,
      v ∈ velocityCube (0 : PDE.Vec d) eps → ell ≤ u (0, v))
    (htStarLower : kappa < tStar) (htStarUpper : tStar ≤ tau)
    (htarget : ∀ i, lower i + kappa < vStar i ∧
      vStar i < upper i - kappa) :
    forwardPropagationDelta d lam Lam kappa *
        eps ^ forwardPropagationExponent d lam Lam kappa * ell <
      u (tStar, vStar) := by
  rcases htStarUpper.lt_or_eq with hinterior | rfl
  · have hsharp := forward_propagation_normalized_interior d lam Lam kappa
      hlam hlamLam hkappa hkappa_one A lower upper tau U u eps ell tStar vStar
      htauLower htauUpper hwidth hbase hU hclosedU hu hnonneg hlower hupper
      hsuper heps hepsOne hell hseed htStarLower hinterior htarget
    unfold forwardPropagationDelta forwardPropagationExponent
    have hhalf : (1 / 2 : ℝ) * ((1 / 4 : ℝ) ^
        movingLensSignExponent d lam Lam kappa * eps ^
          (2 * movingLensSignExponent d lam Lam kappa) * ell) <
        (1 / 4 : ℝ) ^ movingLensSignExponent d lam Lam kappa * eps ^
          (2 * movingLensSignExponent d lam Lam kappa) * ell := by
      have hq : 0 < (1 / 4 : ℝ) ^ movingLensSignExponent d lam Lam kappa *
          eps ^ (2 * movingLensSignExponent d lam Lam kappa) * ell := by positivity
      nlinarith
    simpa only [mul_assoc] using hhalf.trans hsharp
  ·
    let q : ℝ := (1 / 4 : ℝ) ^ movingLensSignExponent d lam Lam kappa *
      eps ^ forwardPropagationExponent d lam Lam kappa * ell
    have hq : 0 < q := by
      dsimp only [q]
      positivity
    have htopClosed : (tStar, vStar) ∈
        parabolicClosedRectangle tStar lower upper := by
      rw [mem_parabolicClosedRectangle_iff]
      exact ⟨(hkappa.trans htauLower).le, le_rfl,
        fun i => ⟨by nlinarith [(htarget i).1],
          by nlinarith [(htarget i).2]⟩⟩
    have htopMem : (tStar, vStar) ∈ U := hclosedU htopClosed
    have htopDiff : ContDiffAt ℝ 2 u (tStar, vStar) :=
      contDiffAt_of_contDiffOn_of_isOpen hU hu htopMem
    have hzu : Tendsto (fun j : ℕ =>
        u (forwardPropagationInteriorTime kappa tStar j, vStar)) atTop
        (𝓝 (u (tStar, vStar))) :=
      htopDiff.continuousAt.tendsto.comp
        ((tendsto_forwardPropagationInteriorTime kappa tStar).prodMk_nhds
          tendsto_const_nhds)
    have hinterior : ∀ j : ℕ, 0 < j → q <
        u (forwardPropagationInteriorTime kappa tStar j, vStar) := by
      intro j hj
      exact forward_propagation_normalized_interior d lam Lam kappa
        hlam hlamLam hkappa hkappa_one A lower upper tStar U u eps ell
        (forwardPropagationInteriorTime kappa tStar j) vStar
        htauLower htauUpper hwidth hbase hU hclosedU hu hnonneg hlower hupper
        hsuper heps hepsOne hell hseed
        (kappa_lt_forwardPropagationInteriorTime htauLower hj)
        (forwardPropagationInteriorTime_lt_tau htauLower j) htarget
    have hsharpTop : q ≤ u (tStar, vStar) :=
      le_of_tendsto_of_tendsto tendsto_const_nhds hzu (by
        filter_upwards [eventually_gt_atTop (0 : ℕ)] with j hj
        exact (hinterior j hj).le)
    unfold forwardPropagationDelta
    have hhalf : (1 / 2 : ℝ) * q < q := by nlinarith
    simpa only [q, mul_assoc] using hhalf.trans_le hsharpTop

/-- Uniform normalized forward-propagation constants. -/
theorem exists_forward_propagation_constants_normalized
    (d : ℕ) (lam Lam kappa : ℝ)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hkappa : 0 < kappa) (hkappa_one : kappa ≤ 1) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ m : ℕ, 0 < m ∧
      ∀ (A : CoefficientField d) (lower upper : PDE.Vec d) (tau : ℝ)
        (U : Set (TimeVelocity d)) (u : TimeVelocity d → ℝ)
        (eps ell tStar : ℝ) (vStar : PDE.Vec d),
        kappa < tau → tau ≤ kappa⁻¹ →
        (∀ i, 2 * kappa < upper i - lower i ∧
          upper i - lower i ≤ kappa⁻¹) →
        (∀ i, lower i + kappa ≤ 0 ∧ 0 < upper i - kappa) →
        IsOpen U → parabolicClosedRectangle tau lower upper ⊆ U →
        ContDiffOn ℝ 2 u U →
        IsNonnegativeOn u (parabolicRectangle tau lower upper) →
        HasLowerEllipticityOn lam A (parabolicRectangle tau lower upper) →
        HasUpperEllipticityOn Lam A (parabolicRectangle tau lower upper) →
        IsParabolicSupersolutionOn A (fun _ ↦ 0) u
          (parabolicRectangle tau lower upper) →
        0 < eps → eps ≤ 1 → 0 < ell →
        (∀ v ∈ velocityClosedRectangle lower upper,
          v ∈ velocityCube (0 : PDE.Vec d) eps → ell ≤ u (0, v)) →
        kappa < tStar → tStar ≤ tau →
        (∀ i, lower i + kappa < vStar i ∧
          vStar i < upper i - kappa) →
        delta * eps ^ m * ell < u (tStar, vStar) := by
  refine ⟨forwardPropagationDelta d lam Lam kappa,
    forwardPropagationDelta_pos d lam Lam kappa,
    forwardPropagationExponent d lam Lam kappa,
    forwardPropagationExponent_pos d lam Lam kappa, ?_⟩
  intro A lower upper tau U u eps ell tStar vStar
    htauLower htauUpper hwidth hbase hU hclosedU hu hnonneg hlower hupper
    hsuper heps hepsOne hell hseed htStarLower htStarUpper htarget
  exact forward_propagation_normalized d lam Lam kappa hlam hlamLam hkappa
    hkappa_one A lower upper tau U u eps ell tStar vStar htauLower htauUpper
    hwidth hbase hU hclosedU hu hnonneg hlower hupper hsuper heps hepsOne hell
    hseed htStarLower htStarUpper htarget

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

open Set

/-- Scaled principal-part classical forward propagation, source-facing form. -/
theorem exists_forward_propagation_constants
    (d : ℕ) (lam Lam kappa : ℝ)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hkappa : 0 < kappa) (hkappa_one : kappa ≤ 1) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ m : ℕ, 0 < m ∧
      ∀ (R : ℝ) (A : CoefficientField d)
        (v0 lower upper : PDE.Vec d) (tau : ℝ)
        (U : Set (TimeVelocity d)) (u : TimeVelocity d → ℝ)
        (eps ell tStar : ℝ) (vStar : PDE.Vec d),
        0 < R → R ≤ 2 →
        kappa * R ^ 2 < tau → tau ≤ kappa⁻¹ * R ^ 2 →
        (∀ i, 2 * kappa * R < upper i - lower i ∧
          upper i - lower i ≤ kappa⁻¹ * R) →
        (∀ i, lower i + kappa * R ≤ v0 i ∧
          v0 i < upper i - kappa * R) →
        IsOpen U → parabolicClosedRectangle tau lower upper ⊆ U →
        ContDiffOn ℝ 2 u U →
        IsNonnegativeOn u (parabolicRectangle tau lower upper) →
        HasLowerEllipticityOn lam A (parabolicRectangle tau lower upper) →
        HasUpperEllipticityOn Lam A (parabolicRectangle tau lower upper) →
        IsParabolicSupersolutionOn A (fun _ ↦ 0) u
          (parabolicRectangle tau lower upper) →
        0 < eps → eps ≤ 1 → 0 < ell →
        (∀ v ∈ velocityClosedRectangle lower upper,
          v ∈ velocityCube v0 (eps * R) → ell ≤ u (0, v)) →
        kappa * R ^ 2 < tStar → tStar ≤ tau →
        (∀ i, lower i + kappa * R < vStar i ∧
          vStar i < upper i - kappa * R) →
        delta * eps ^ m * ell < u (tStar, vStar) := by
  refine ⟨forwardPropagationDelta d lam Lam kappa,
    forwardPropagationDelta_pos d lam Lam kappa,
    forwardPropagationExponent d lam Lam kappa,
    forwardPropagationExponent_pos d lam Lam kappa, ?_⟩
  intro R A v0 lower upper tau U u eps ell tStar vStar
    hR _hRtwo htauLower htauUpper hwidth hbase hU hclosedU hu hnonneg
    hlower hupper hsuper heps hepsOne hell hseed htStarLower htStarUpper
    htarget
  let tauHat : ℝ := tau / R ^ 2
  let tStarHat : ℝ := tStar / R ^ 2
  let lowerHat : PDE.Vec d := pullbackRectangleLower v0 lower R
  let upperHat : PDE.Vec d := pullbackRectangleUpper v0 upper R
  let vStarHat : PDE.Vec d := R⁻¹ • (vStar - v0)
  let UHat : Set (TimeVelocity d) := parabolicAffine 0 v0 R ⁻¹' U
  let AHat : CoefficientField d := pullbackCoefficient A 0 v0 R
  let uHat : TimeVelocity d → ℝ := pullbackScalar u 0 v0 R
  have hRsq : 0 < R ^ 2 := sq_pos_of_pos hR
  have htauLowerHat : kappa < tauHat := by
    dsimp only [tauHat]
    exact (lt_div_iff₀ hRsq).2 htauLower
  have htauUpperHat : tauHat ≤ kappa⁻¹ := by
    dsimp only [tauHat]
    exact (div_le_iff₀ hRsq).2 htauUpper
  have htStarLowerHat : kappa < tStarHat := by
    dsimp only [tStarHat]
    exact (lt_div_iff₀ hRsq).2 htStarLower
  have htStarUpperHat : tStarHat ≤ tauHat := by
    dsimp only [tStarHat, tauHat]
    exact (div_le_div_iff₀ hRsq hRsq).2
      (mul_le_mul_of_nonneg_right htStarUpper hRsq.le)
  have hwidthScale (i : Fin d) :
      upperHat i - lowerHat i = R⁻¹ * (upper i - lower i) := by
    dsimp only [upperHat, lowerHat, pullbackRectangleUpper,
      pullbackRectangleLower]
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hwidthHat : ∀ i, 2 * kappa < upperHat i - lowerHat i ∧
      upperHat i - lowerHat i ≤ kappa⁻¹ := by
    intro i
    rw [hwidthScale i]
    constructor
    · exact (lt_inv_mul_iff₀ hR).2 (by
        simpa only [mul_assoc, mul_comm, mul_left_comm] using (hwidth i).1)
    · exact (inv_mul_le_iff₀ hR).2 (by
        simpa only [mul_assoc, mul_comm, mul_left_comm] using (hwidth i).2)
  have hbaseHat : ∀ i, lowerHat i + kappa ≤ 0 ∧
      0 < upperHat i - kappa := by
    intro i
    constructor
    · dsimp only [lowerHat, pullbackRectangleLower]
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      apply le_of_mul_le_mul_left ?_ hR
      calc
        R * (R⁻¹ * (lower i - v0 i) + kappa) =
            lower i - v0 i + kappa * R := by
          field_simp [hR.ne']
        _ ≤ 0 := by nlinarith [(hbase i).1]
        _ = R * 0 := by ring
    · dsimp only [upperHat, pullbackRectangleUpper]
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      apply lt_of_mul_lt_mul_left ?_ hR.le
      calc
        R * 0 = 0 := by ring
        _ < upper i - v0 i - kappa * R := by nlinarith [(hbase i).2]
        _ = R * (R⁻¹ * (upper i - v0 i) - kappa) := by
          field_simp [hR.ne']
  have htargetHat : ∀ i, lowerHat i + kappa < vStarHat i ∧
      vStarHat i < upperHat i - kappa := by
    intro i
    constructor
    · dsimp only [lowerHat, vStarHat, pullbackRectangleLower]
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      apply lt_of_mul_lt_mul_left ?_ hR.le
      calc
        R * (R⁻¹ * (lower i - v0 i) + kappa) =
            lower i - v0 i + kappa * R := by
          field_simp [hR.ne']
        _ < vStar i - v0 i := by nlinarith [(htarget i).1]
        _ = R * (R⁻¹ * (vStar i - v0 i)) := by
          field_simp [hR.ne']
    · dsimp only [upperHat, vStarHat, pullbackRectangleUpper]
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      apply lt_of_mul_lt_mul_left ?_ hR.le
      calc
        R * (R⁻¹ * (vStar i - v0 i)) = vStar i - v0 i := by
          field_simp [hR.ne']
        _ < upper i - v0 i - kappa * R := by nlinarith [(htarget i).2]
        _ = R * (R⁻¹ * (upper i - v0 i) - kappa) := by
          field_simp [hR.ne']
  have hmapU : MapsTo (parabolicAffine 0 v0 R) UHat U := by
    intro z hz
    exact hz
  have hUHat : IsOpen UHat := by
    dsimp only [UHat]
    exact hU.preimage (contDiff_parabolicAffine 0 v0 R).continuous
  have hclosedUHat :
      parabolicClosedRectangle tauHat lowerHat upperHat ⊆ UHat := by
    intro z hz
    exact hclosedU (mapsTo_parabolicAffine_parabolicClosedRectangle hR
      (by simpa only [tauHat, lowerHat, upperHat] using hz))
  have huHat : ContDiffOn ℝ 2 uHat UHat := by
    dsimp only [uHat]
    exact ContDiffOn.pullbackScalar hu hmapU
  have hmapQ : MapsTo (parabolicAffine 0 v0 R)
      (parabolicRectangle tauHat lowerHat upperHat)
      (parabolicRectangle tau lower upper) := by
    intro z hz
    exact mapsTo_parabolicAffine_parabolicRectangle hR
      (by simpa only [tauHat, lowerHat, upperHat] using hz)
  have hnonnegHat : IsNonnegativeOn uHat
      (parabolicRectangle tauHat lowerHat upperHat) := by
    dsimp only [uHat]
    exact hnonneg.pullbackScalar hmapQ
  have hlowerHat : HasLowerEllipticityOn lam AHat
      (parabolicRectangle tauHat lowerHat upperHat) := by
    dsimp only [AHat]
    exact hlower.pullback hmapQ
  have hupperHat : HasUpperEllipticityOn Lam AHat
      (parabolicRectangle tauHat lowerHat upperHat) := by
    dsimp only [AHat]
    exact hupper.pullback hmapQ
  have hQsubU : parabolicRectangle tau lower upper ⊆ U := by
    intro z hz
    apply hclosedU
    rw [mem_parabolicRectangle_iff] at hz
    rw [mem_parabolicClosedRectangle_iff]
    exact ⟨hz.1.le, hz.2.1.le,
      fun i => ⟨(hz.2.2 i).1.le, (hz.2.2 i).2.le⟩⟩
  have hsuperHat : IsParabolicSupersolutionOn AHat (fun _ ↦ 0) uHat
      (parabolicRectangle tauHat lowerHat upperHat) := by
    dsimp only [AHat, uHat]
    simpa only [mul_zero] using
      IsParabolicSupersolutionOn.pullback
        (U := parabolicRectangle tau lower upper)
        (V := parabolicRectangle tauHat lowerHat upperHat)
        (isOpen_parabolicRectangle tau lower upper) (hu.mono hQsubU)
        hsuper hmapQ
  have hseedHat : ∀ v ∈ velocityClosedRectangle lowerHat upperHat,
      v ∈ velocityCube (0 : PDE.Vec d) eps → ell ≤ uHat (0, v) := by
    intro v hvRect hvCube
    have hvPhysicalRect :
        v0 + R • v ∈ velocityClosedRectangle lower upper :=
      (mem_affineVelocity_velocityClosedRectangle_iff hR).2
        (by simpa only [lowerHat, upperHat] using hvRect)
    have hvPhysicalCube : v0 + R • v ∈ velocityCube v0 (eps * R) :=
      (mem_affineVelocity_velocityCube_iff hR).2 hvCube
    simpa only [uHat, pullbackScalar_apply, parabolicAffine, mul_zero,
      zero_add] using
      hseed (v0 + R • v) hvPhysicalRect hvPhysicalCube
  have hHat := forward_propagation_normalized d lam Lam kappa
    hlam hlamLam hkappa hkappa_one AHat lowerHat upperHat tauHat UHat uHat
    eps ell tStarHat vStarHat htauLowerHat htauUpperHat hwidthHat hbaseHat
    hUHat hclosedUHat huHat hnonnegHat hlowerHat hupperHat hsuperHat heps
    hepsOne hell hseedHat htStarLowerHat htStarUpperHat htargetHat
  have heval : parabolicAffine 0 v0 R (tStarHat, vStarHat) =
      (tStar, vStar) := by
    dsimp only [parabolicAffine, tStarHat, vStarHat]
    ext
    · field_simp [hR.ne']
      ring
    · simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul]
      ring
  simpa only [uHat, pullbackScalar_apply, heval] using hHat

end HypoellipticAleksandrov.Parabolic

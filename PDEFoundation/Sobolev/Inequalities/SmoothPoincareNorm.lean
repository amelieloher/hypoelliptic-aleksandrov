module

public import PDEFoundation.Measure.LpPower
public import PDEFoundation.Sobolev.Inequalities.SmoothPoincare
public import PDEFoundation.Sobolev.W1p.EuclideanGradient
public import PDEFoundation.Sobolev.W1p.Smooth

/-!
# Smooth convex-domain Poincaré estimates in `L^p` norm form

This file converts the integral-power estimate for globally smooth functions
into the extended-real norm used by the public Sobolev theorem. The displayed
constant is `2 ^ d`, uniformly for every real exponent `p ≥ 1`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory

private theorem rpow_inv_le_const_mul_of_le_const_mul_rpow
    {A B C D p : ℝ} (hp : 1 ≤ p)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 1 ≤ C) (hD : 0 ≤ D)
    (h : A ≤ C * D ^ p * B) :
    A ^ (1 / p : ℝ) ≤ C * D * B ^ (1 / p : ℝ) := by
  have hpPos : 0 < p :=
    zero_lt_one.trans_le hp
  have hinvNonneg : 0 ≤ (1 / p : ℝ) := by
    positivity
  have hinvLeOne : (1 / p : ℝ) ≤ 1 :=
    (div_le_one hpPos).2 hp
  have hCNonneg : 0 ≤ C :=
    zero_le_one.trans hC
  have hDPowNonneg : 0 ≤ D ^ p :=
    Real.rpow_nonneg hD p
  calc
    A ^ (1 / p : ℝ) ≤
        (C * D ^ p * B) ^ (1 / p : ℝ) :=
      Real.rpow_le_rpow hA h hinvNonneg
    _ = C ^ (1 / p : ℝ) *
        (D ^ p) ^ (1 / p : ℝ) *
          B ^ (1 / p : ℝ) := by
      rw [Real.mul_rpow (mul_nonneg hCNonneg hDPowNonneg) hB,
        Real.mul_rpow hCNonneg hDPowNonneg]
    _ = C ^ (1 / p : ℝ) * D *
        B ^ (1 / p : ℝ) := by
      rw [one_div, Real.rpow_rpow_inv hD hpPos.ne']
    _ ≤ C * D * B ^ (1 / p : ℝ) := by
      refine mul_le_mul_of_nonneg_right ?_
        (Real.rpow_nonneg hB _)
      exact
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_self_of_one_le hC hinvLeOne) hD

/-- Smooth diameter-only Poincaré inequality in the unnormalized extended
`L^p` norm. The constant `2 ^ d` is independent of `p`. -/
theorem eLpNormOn_sub_integralAverage_le_two_pow_mul_of_contDiff
    {d : ℕ} {U : Set (Vec d)} {D p : ℝ}
    (hU : IsOpenBoundedConvexDomain U)
    (hUDiameter : HasEuclideanDiameterLE U D)
    (hD : 0 ≤ D)
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hp : 1 ≤ p)
    (hUPos : 0 < volume U) (hUTop : volume U < ∞) :
    eLpNormOn U (ENNReal.ofReal p)
        (fun x => u x - integralAverage U u) ≤
      ENNReal.ofReal ((2 : ℝ) ^ d * D) *
        euclideanFieldELpNormOn U (ENNReal.ofReal p)
          (classicalGradient u) := by
  let : IsFiniteMeasure (volumeOn U) :=
    hU.isSobolevRegularDomain.isFiniteMeasure_volumeOn
  have hpPos : 0 < p :=
    zero_lt_one.trans_le hp
  let us :
      W1pFunction U (ENNReal.ofReal p) :=
    W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain
      hU (hu.of_le (by norm_num))
  have hsubMem :
      MemLp (fun x => u x - integralAverage U u)
        (ENNReal.ofReal p) (volumeOn U) := by
    have hconst :
        MemLp (fun _ : Vec d => integralAverage U u)
          (ENNReal.ofReal p) (volumeOn U) :=
      memLp_const _
    simpa only [us,
      W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain_toFun]
      using! us.memLp.sub hconst
  have hgradHilbert :
      MemLp (toHilbertVecField (classicalGradient u))
        (ENNReal.ofReal p) (volumeOn U) := by
    apply gradMemLpOn_iff_memLp_toHilbertVecField.mp
    simpa only [us,
      W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain_grad]
      using us.gradMemLp
  have hgradMem :
      MemLp
        (fun x => vecEuclideanNorm (classicalGradient u x))
        (ENNReal.ofReal p) (volumeOn U) := by
    exact
      MemLp.ae_eq
        (Filter.Eventually.of_forall fun x =>
          norm_toHilbertVecField_apply
            (classicalGradient u) x)
        hgradHilbert.norm
  let A : ℝ :=
    ∫ x in U, |u x - integralAverage U u| ^ p ∂volume
  let B : ℝ :=
    ∫ x in U,
      vecEuclideanNorm (classicalGradient u x) ^ p ∂volume
  let C : ℝ :=
    (2 : ℝ) ^ d
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact integral_nonneg_of_ae <|
      Filter.Eventually.of_forall fun x =>
        Real.rpow_nonneg (abs_nonneg _) _
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact integral_nonneg_of_ae <|
      Filter.Eventually.of_forall fun x =>
        Real.rpow_nonneg (vecEuclideanNorm_nonneg _) _
  have hC : 1 ≤ C := by
    dsimp only [C]
    exact one_le_pow₀ (by norm_num)
  have hIntegral : A ≤ C * D ^ p * B := by
    simpa only [A, B, C] using
      setIntegral_abs_sub_integralAverage_rpow_le_two_pow_mul
        hU hUDiameter hD hu hp hUPos hUTop
  have hRoot :
      A ^ (1 / p : ℝ) ≤
        C * D * B ^ (1 / p : ℝ) :=
    rpow_inv_le_const_mul_of_le_const_mul_rpow
      hp hA hB hC hD hIntegral
  have hLeftReal :
      (eLpNormOn U (ENNReal.ofReal p)
        (fun x => u x - integralAverage U u)).toReal =
          A ^ (1 / p : ℝ) := by
    simpa only [eLpNormOn, volumeOn, A, Real.norm_eq_abs] using
      toReal_eLpNorm_ofReal_eq_integral_rpow_norm_rpow_inv
        hpPos hsubMem
  have hGradReal :
      (euclideanFieldELpNormOn U (ENNReal.ofReal p)
        (classicalGradient u)).toReal =
          B ^ (1 / p : ℝ) := by
    simpa only [euclideanFieldELpNormOn, eLpNormOn, volumeOn,
      B, Real.norm_eq_abs,
      abs_of_nonneg (vecEuclideanNorm_nonneg _)] using
      toReal_eLpNorm_ofReal_eq_integral_rpow_norm_rpow_inv
        hpPos hgradMem
  have hLeftTop :
      eLpNormOn U (ENNReal.ofReal p)
        (fun x => u x - integralAverage U u) ≠ ∞ :=
    hsubMem.eLpNorm_ne_top
  have hGradTop :
      euclideanFieldELpNormOn U (ENNReal.ofReal p)
        (classicalGradient u) ≠ ∞ :=
    hgradMem.eLpNorm_ne_top
  have hRightTop :
      ENNReal.ofReal (C * D) *
        euclideanFieldELpNormOn U (ENNReal.ofReal p)
          (classicalGradient u) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hGradTop
  have hCDNonneg : 0 ≤ C * D :=
    mul_nonneg (zero_le_one.trans hC) hD
  refine
    (ENNReal.toReal_le_toReal hLeftTop hRightTop).mp ?_
  rw [hLeftReal, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hCDNonneg, hGradReal]
  simpa only [C] using hRoot

/-- Smooth diameter-only Poincaré inequality in the normalized extended
`L^p` norm. The constant `2 ^ d` is independent of `p`. -/
theorem eLpMeanNormOn_sub_integralAverage_le_two_pow_mul_of_contDiff
    {d : ℕ} {U : Set (Vec d)} {D p : ℝ}
    (hU : IsOpenBoundedConvexDomain U)
    (hUDiameter : HasEuclideanDiameterLE U D)
    (hD : 0 ≤ D)
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hp : 1 ≤ p)
    (hUPos : 0 < volume U) (hUTop : volume U < ∞) :
    eLpMeanNormOn U (ENNReal.ofReal p)
        (fun x => u x - integralAverage U u) ≤
      ENNReal.ofReal ((2 : ℝ) ^ d * D) *
        euclideanFieldELpMeanNormOn U (ENNReal.ofReal p)
          (classicalGradient u) := by
  rw [eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn
      hUTop,
    euclideanFieldELpMeanNormOn_eq_volume_inv_rpow_mul
      hUTop]
  calc
    (volume U)⁻¹ ^ (1 / ENNReal.ofReal p).toReal *
          eLpNormOn U (ENNReal.ofReal p)
            (fun x => u x - integralAverage U u) ≤
        (volume U)⁻¹ ^ (1 / ENNReal.ofReal p).toReal *
          (ENNReal.ofReal ((2 : ℝ) ^ d * D) *
            euclideanFieldELpNormOn U (ENNReal.ofReal p)
              (classicalGradient u)) :=
      mul_le_mul_right
        (eLpNormOn_sub_integralAverage_le_two_pow_mul_of_contDiff
          hU hUDiameter hD hu hp hUPos hUTop) _
    _ = ENNReal.ofReal ((2 : ℝ) ^ d * D) *
        ((volume U)⁻¹ ^ (1 / ENNReal.ofReal p).toReal *
          euclideanFieldELpNormOn U (ENNReal.ofReal p)
            (classicalGradient u)) := by
      ac_rfl

end PDE

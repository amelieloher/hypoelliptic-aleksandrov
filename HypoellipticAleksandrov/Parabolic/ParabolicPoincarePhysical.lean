module

public import HypoellipticAleksandrov.Parabolic.ParabolicPoincare
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyScaling
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyProjection

/-!
# Physical parabolic Morrey Poincare estimate

This module transports the unit forward-box Poincare inequality to
positive-radius physical forward boxes by parabolic affine scaling.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set
open scoped BigOperators ENNReal

private theorem continuous_timeDerivative_physical
    {d : Nat} {u : TimeVelocity d -> Real} (hu : ContDiff Real 2 u) :
    Continuous (timeDerivative u) := by
  change Continuous (fun z : TimeVelocity d => fderiv Real u z (1, 0))
  exact ((hu.contDiff_fderiv_apply (m := 0) (by norm_num)).comp
    (contDiff_id.prodMk contDiff_const)).continuous

private theorem continuous_velocityHessian_physical
    {d : Nat} {u : TimeVelocity d -> Real} (hu : ContDiff Real 2 u) :
    Continuous (velocityHessian u) := by
  apply continuous_matrix
  intro i j
  change Continuous (fun z : TimeVelocity d =>
    fderiv Real (fderiv Real u) z (0, Pi.single i 1) (0, Pi.single j 1))
  have hdu : ContDiff Real 1 (fderiv Real u) :=
    hu.fderiv_right (m := 1) (by norm_num)
  exact (((hdu.contDiff_fderiv_apply (m := 0) (by norm_num)).comp
    (contDiff_id.prodMk contDiff_const)).clm_apply contDiff_const).continuous

private theorem continuous_parabolicMorreyUnitAffineProjection_physical
    {d : Nat} (u : TimeVelocity d -> Real) :
    Continuous (parabolicMorreyUnitAffineProjection u) := by
  unfold parabolicMorreyUnitAffineProjection
  apply Continuous.add continuous_const
  apply continuous_finset_sum
  intro i _
  exact continuous_const.mul (continuous_apply i |>.comp continuous_snd)

private theorem parabolicELpNormPullbackMeasureFactor_pos
    (d : Nat) {r : Real} (hr : 0 < r) :
    0 < parabolicELpNormPullbackMeasureFactor d r := by
  unfold parabolicELpNormPullbackMeasureFactor
  apply ENNReal.rpow_pos
  · exact ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos hr _))
  · exact ENNReal.ofReal_ne_top

private theorem ne_top_of_eq_mul
    {a b c : ENNReal} (ha : a ≠ 0) (hscale : b = a * c) (hb : b ≠ ⊤) :
    c ≠ ⊤ := by
  intro hc
  apply hb
  rw [hscale, hc, ENNReal.mul_top ha]

/-- Scale-normalized smooth parabolic Poincare inequality on every positive-radius
forward physical box, modulo the transported velocity-affine moment projection. -/
theorem exists_parabolicMorreyBoxAffinePoincareConst (d : Nat)
    (hd : 1 <= d) :
    ∃ C : Real, 0 < C ∧
      ∀ (t₀ : Real) (v₀ : PDE.Vec d) (r : Real), 0 < r ->
      ∀ u : TimeVelocity d -> Real, ContDiff Real 2 u ->
        (r ^ 2)⁻¹ *
          parabolicLpNormOn d
            (fun z => u z -
              parabolicMorreyBoxAffineProjection t₀ v₀ r u z)
            (parabolicBox 1 r t₀ v₀) <=
          C *
            (parabolicLpNormOn d (timeDerivative u)
                (parabolicBox 1 r t₀ v₀) +
              ∑ i : Fin d, ∑ j : Fin d,
                parabolicLpNormOn d
                  (fun z => velocityHessian u z i j)
                  (parabolicBox 1 r t₀ v₀)) := by
  obtain ⟨C, hCpos, hC⟩ := exists_parabolicMorreyUnitAffinePoincareConst d hd
  refine ⟨C, hCpos, ?_⟩
  intro t₀ v₀ r hr u hu
  let uhat : TimeVelocity d -> Real := pullbackScalar u t₀ v₀ r
  let w : TimeVelocity d -> Real := fun z =>
    u z - parabolicMorreyBoxAffineProjection t₀ v₀ r u z
  let what : TimeVelocity d -> Real := fun z =>
    uhat z - parabolicMorreyUnitAffineProjection uhat z
  let factor : ENNReal := parabolicELpNormPullbackMeasureFactor d r
  let F : Real := factor.toReal
  let box : Set (TimeVelocity d) := parabolicBox 1 r t₀ v₀
  have huHat : ContDiff Real 2 uhat := by
    exact hu.comp (contDiff_parabolicAffine t₀ v₀ r)
  have hpullResidual : pullbackScalar w t₀ v₀ r = what := by
    funext z
    simp only [w, what, uhat, pullbackScalar_apply]
    rw [parabolicMorreyBoxAffineProjection_parabolicAffine t₀ v₀ hr]
  have hboxImage : parabolicAffine t₀ v₀ r '' parabolicMorreyUnitBox d = box := by
    exact parabolicAffine_image_parabolicMorreyUnitBox t₀ v₀ hr
  have hfactorPos : 0 < factor := by
    dsimp only [factor]
    exact parabolicELpNormPullbackMeasureFactor_pos d hr
  have hfactorNeZero : factor ≠ 0 := ne_of_gt hfactorPos
  have hFpos : 0 < F := by
    dsimp only [F]
    exact ENNReal.toReal_pos hfactorNeZero
      (ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top)
  have hwhatContinuous : Continuous what := by
    dsimp only [what]
    exact huHat.continuous.sub
      (continuous_parabolicMorreyUnitAffineProjection_physical uhat)
  have hwhatUnitFin :
      parabolicELpNormOn d what (parabolicMorreyUnitBox d) ≠ ⊤ := by
    exact (Continuous.memLp_parabolicMorreyUnitBox hwhatContinuous).eLpNorm_ne_top
  have htimeUnitFin :
      parabolicELpNormOn d (timeDerivative uhat) (parabolicMorreyUnitBox d) ≠ ⊤ := by
    exact (Continuous.memLp_parabolicMorreyUnitBox
      (continuous_timeDerivative_physical huHat)).eLpNorm_ne_top
  have hhessianUnitFin (i j : Fin d) :
      parabolicELpNormOn d (fun z => velocityHessian uhat z i j)
          (parabolicMorreyUnitBox d) ≠ ⊤ := by
    exact (Continuous.memLp_parabolicMorreyUnitBox
      ((continuous_pi_iff.mp (continuous_pi_iff.mp
        (continuous_velocityHessian_physical huHat) i)) j)).eLpNorm_ne_top
  have hresidualScale :
      parabolicELpNormOn d what (parabolicMorreyUnitBox d) =
        factor * parabolicELpNormOn d w box := by
    calc
      parabolicELpNormOn d what (parabolicMorreyUnitBox d) =
          parabolicELpNormOn d (pullbackScalar w t₀ v₀ r)
            (parabolicMorreyUnitBox d) := by rw [hpullResidual]
      _ = factor * parabolicELpNormOn d w
          (parabolicAffine t₀ v₀ r '' parabolicMorreyUnitBox d) := by
        exact parabolicELpNormOn_pullbackScalar t₀ v₀ hr w _
      _ = factor * parabolicELpNormOn d w box := by rw [hboxImage]
  have hresidualPhysicalFin : parabolicELpNormOn d w box ≠ ⊤ :=
    ne_top_of_eq_mul hfactorNeZero hresidualScale hwhatUnitFin
  have hrSqNeZero : r ^ 2 ≠ 0 := pow_ne_zero 2 hr.ne'
  have htimeFactorNeZero : ‖r ^ 2‖ₑ * factor ≠ 0 := by
    exact mul_ne_zero (enorm_ne_zero.mpr hrSqNeZero) hfactorNeZero
  have htimeScale :
      parabolicELpNormOn d (timeDerivative uhat) (parabolicMorreyUnitBox d) =
        (‖r ^ 2‖ₑ * factor) * parabolicELpNormOn d (timeDerivative u) box := by
    calc
      parabolicELpNormOn d (timeDerivative uhat) (parabolicMorreyUnitBox d) =
          (‖r ^ 2‖ₑ * factor) * parabolicELpNormOn d (timeDerivative u)
            (parabolicAffine t₀ v₀ r '' parabolicMorreyUnitBox d) := by
        exact parabolicELpNormOn_timeDerivative_pullbackScalar t₀ v₀ hr u hu _
      _ = (‖r ^ 2‖ₑ * factor) * parabolicELpNormOn d (timeDerivative u) box := by
        rw [hboxImage]
  have htimePhysicalFin : parabolicELpNormOn d (timeDerivative u) box ≠ ⊤ :=
    ne_top_of_eq_mul htimeFactorNeZero htimeScale htimeUnitFin
  have hhessianScale (i j : Fin d) :
      parabolicELpNormOn d (fun z => velocityHessian uhat z i j)
          (parabolicMorreyUnitBox d) =
        (‖r ^ 2‖ₑ * factor) *
          parabolicELpNormOn d (fun z => velocityHessian u z i j) box := by
    calc
      parabolicELpNormOn d (fun z => velocityHessian uhat z i j)
          (parabolicMorreyUnitBox d) =
        (‖r ^ 2‖ₑ * factor) *
          parabolicELpNormOn d (fun z => velocityHessian u z i j)
            (parabolicAffine t₀ v₀ r '' parabolicMorreyUnitBox d) := by
        exact parabolicELpNormOn_velocityHessian_pullbackScalar t₀ v₀ hr u hu _ i j
      _ = (‖r ^ 2‖ₑ * factor) *
          parabolicELpNormOn d (fun z => velocityHessian u z i j) box := by
        rw [hboxImage]
  have hhessianPhysicalFin (i j : Fin d) :
      parabolicELpNormOn d (fun z => velocityHessian u z i j) box ≠ ⊤ :=
    ne_top_of_eq_mul htimeFactorNeZero (hhessianScale i j) (hhessianUnitFin i j)
  obtain ⟨_, hresidualReal⟩ :=
    parabolicLpNormOn_pullbackScalar_finite t₀ v₀ hr w (parabolicMorreyUnitBox d) (by
      simpa only [hboxImage] using hresidualPhysicalFin
    )
  have hresidualReal' : parabolicLpNormOn d what (parabolicMorreyUnitBox d) =
      F * parabolicLpNormOn d w box := by
    rw [← hpullResidual]
    simpa only [factor, F, hboxImage] using hresidualReal
  obtain ⟨_, htimeReal⟩ :=
    parabolicLpNormOn_timeDerivative_pullbackScalar_finite t₀ v₀ hr u hu
      (parabolicMorreyUnitBox d) (by simpa only [hboxImage] using htimePhysicalFin)
  have htimeCoefficient : (‖r ^ 2‖ₑ * factor).toReal = r ^ 2 * F := by
    rw [ENNReal.toReal_mul, Real.enorm_of_nonneg (sq_nonneg r),
      ENNReal.toReal_ofReal (sq_nonneg r)]
  have htimeReal' : parabolicLpNormOn d (timeDerivative uhat)
      (parabolicMorreyUnitBox d) = r ^ 2 * F *
        parabolicLpNormOn d (timeDerivative u) box := by
    rw [htimeReal, htimeCoefficient, hboxImage]
  have hhessianReal' (i j : Fin d) :
      parabolicLpNormOn d (fun z => velocityHessian uhat z i j)
          (parabolicMorreyUnitBox d) = r ^ 2 * F *
            parabolicLpNormOn d (fun z => velocityHessian u z i j) box := by
    obtain ⟨_, hreal⟩ :=
      parabolicLpNormOn_velocityHessian_pullbackScalar_finite t₀ v₀ hr u hu
        (parabolicMorreyUnitBox d) i j (by
          simpa only [hboxImage] using hhessianPhysicalFin i j)
    rw [hreal, htimeCoefficient, hboxImage]
  have hunit := hC uhat huHat
  rw [hresidualReal', htimeReal'] at hunit
  simp_rw [hhessianReal'] at hunit
  have hscalePos : 0 < r ^ 2 * F := mul_pos (sq_pos_of_pos hr) hFpos
  apply le_of_mul_le_mul_left (a := r ^ 2 * F) ?_ hscalePos
  calc
    (r ^ 2 * F) * ((r ^ 2)⁻¹ * parabolicLpNormOn d w box) =
        F * parabolicLpNormOn d w box := by
      field_simp
    _ <= C * (r ^ 2 * F * parabolicLpNormOn d (timeDerivative u) box +
        ∑ i : Fin d, ∑ j : Fin d, r ^ 2 * F *
          parabolicLpNormOn d (fun z => velocityHessian u z i j) box) := hunit
    _ = (r ^ 2 * F) * (C * (parabolicLpNormOn d (timeDerivative u) box +
        ∑ i : Fin d, ∑ j : Fin d,
          parabolicLpNormOn d (fun z => velocityHessian u z i j) box)) := by
      calc
        C * (r ^ 2 * F * parabolicLpNormOn d (timeDerivative u) box +
            ∑ i : Fin d, ∑ j : Fin d, r ^ 2 * F *
              parabolicLpNormOn d (fun z => velocityHessian u z i j) box) =
            C * (r ^ 2 * F * parabolicLpNormOn d (timeDerivative u) box) +
              ∑ i : Fin d, ∑ j : Fin d, C * (r ^ 2 * F *
                parabolicLpNormOn d (fun z => velocityHessian u z i j) box) := by
          rw [mul_add, Finset.mul_sum]
          simp_rw [Finset.mul_sum]
        _ = (r ^ 2 * F) * (C * (parabolicLpNormOn d (timeDerivative u) box +
            ∑ i : Fin d, ∑ j : Fin d,
              parabolicLpNormOn d (fun z => velocityHessian u z i j) box)) := by
          rw [mul_add, Finset.mul_sum]
          simp_rw [Finset.mul_sum]
          rw [mul_add]
          simp_rw [Finset.mul_sum]
          ring_nf

end HypoellipticAleksandrov.Parabolic

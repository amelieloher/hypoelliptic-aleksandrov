module

public import HypoellipticAleksandrov.Parabolic.ParabolicPoincareSpatial
public import HypoellipticAleksandrov.Parabolic.ParabolicPoincareTime

/-!
# Smooth normalized parabolic Poincare estimate

This module assembles the spatial and temporal unit-box estimates into the
second-order parabolic Poincare inequality modulo the canonical affine moment
projection.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped BigOperators ENNReal

private theorem continuous_timeDerivative_local
    {d : Nat} {u : TimeVelocity d -> Real} (hu : ContDiff Real 2 u) :
    Continuous (timeDerivative u) := by
  change Continuous (fun z : TimeVelocity d => fderiv Real u z (1, 0))
  exact ((hu.contDiff_fderiv_apply (m := 0) (by norm_num)).comp
    (contDiff_id.prodMk contDiff_const)).continuous

private theorem continuous_velocityHessian_local
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

private theorem stronglyMeasurable_parabolicMorreyUnitSpatialAffineProjection
    {d : Nat} {u : TimeVelocity d -> Real} (hu : Continuous u) :
    StronglyMeasurable (parabolicMorreyUnitSpatialAffineProjection u) := by
  let V : Set (PDE.Vec d) := velocityCube (0 : PDE.Vec d) 1
  let ν : Measure (PDE.Vec d) := volume.restrict V
  have huStrong : StronglyMeasurable
      (Function.uncurry fun t : Real => fun v : PDE.Vec d => u (t, v)) := by
    change StronglyMeasurable u
    exact hu.stronglyMeasurable
  have hAverage : StronglyMeasurable (parabolicMorreyUnitVelocityAverage u) := by
    unfold parabolicMorreyUnitVelocityAverage
    apply stronglyMeasurable_const.mul
    simpa only [ν, V] using (huStrong.integral_prod_right (ν := ν))
  have hCoeff : ∀ i : Fin d,
      StronglyMeasurable (fun t => parabolicMorreyUnitVelocityCoeffAt u t i) := by
    intro i
    have huCoordinate : StronglyMeasurable
        (Function.uncurry fun t : Real => fun v : PDE.Vec d => u (t, v) * v i) := by
      change StronglyMeasurable (fun z : TimeVelocity d => u z * z.2 i)
      exact (hu.mul ((continuous_apply i).comp continuous_snd)).stronglyMeasurable
    unfold parabolicMorreyUnitVelocityCoeffAt
    apply stronglyMeasurable_const.mul
    simpa only [ν, V] using (huCoordinate.integral_prod_right (ν := ν))
  unfold parabolicMorreyUnitSpatialAffineProjection
  apply (hAverage.comp_measurable measurable_fst).add
  rw [← Finset.sum_fn]
  refine Finset.stronglyMeasurable_sum Finset.univ fun i _ => ?_
  exact ((hCoeff i).comp_measurable measurable_fst).mul
    (((continuous_apply i).comp continuous_snd).stronglyMeasurable)

private theorem continuous_parabolicMorreyUnitAffineProjection_local
    {d : Nat} (u : TimeVelocity d -> Real) :
    Continuous (parabolicMorreyUnitAffineProjection u) := by
  unfold parabolicMorreyUnitAffineProjection
  apply Continuous.add continuous_const
  apply continuous_finset_sum
  intro i _
  exact continuous_const.mul (continuous_apply i |>.comp continuous_snd)

/-- Smooth normalized second-order parabolic Poincare inequality modulo the
canonical time-independent velocity-affine moment projection. -/
theorem exists_parabolicMorreyUnitAffinePoincareConst (d : Nat)
    (hd : 1 <= d) :
    ∃ C : Real, 0 < C ∧
      ∀ u : TimeVelocity d -> Real,
        ContDiff Real 2 u ->
        parabolicLpNormOn d
            (fun z => u z - parabolicMorreyUnitAffineProjection u z)
            (parabolicMorreyUnitBox d) <=
          C *
            (parabolicLpNormOn d (timeDerivative u)
                (parabolicMorreyUnitBox d) +
              ∑ i : Fin d, ∑ j : Fin d,
                parabolicLpNormOn d
                  (fun z => velocityHessian u z i j)
                  (parabolicMorreyUnitBox d)) := by
  obtain ⟨Cs, hCsPos, hCs⟩ :=
    exists_parabolicMorreyUnitSpatialAffinePoincareConst d hd
  obtain ⟨CsENN, _hCsENNPos, hCsENN⟩ :=
    exists_parabolicMorreyUnitSpatialAffinePoincareELpConst d hd
  let Ct : Real := 1 + 3 * (d : Real)
  refine ⟨Cs + Ct, ?_, ?_⟩
  · have hCtPos : 0 < Ct := by
      dsimp only [Ct]
      have hdnonneg : 0 <= (d : Real) := Nat.cast_nonneg d
      linarith
    linarith
  · intro u hu
    let S : TimeVelocity d -> Real := fun z =>
      u z - parabolicMorreyUnitSpatialAffineProjection u z
    let D : TimeVelocity d -> Real := fun z =>
      parabolicMorreyUnitSpatialAffineProjection u z -
        parabolicMorreyUnitAffineProjection u z
    let T : ENNReal :=
      parabolicELpNormOn d (timeDerivative u) (parabolicMorreyUnitBox d)
    let H : ENNReal := ∑ i : Fin d, ∑ j : Fin d,
      parabolicELpNormOn d (fun z => velocityHessian u z i j)
        (parabolicMorreyUnitBox d)
    have hTfin : T ≠ ⊤ := by
      dsimp only [T]
      exact (Continuous.memLp_parabolicMorreyUnitBox
        (continuous_timeDerivative_local hu)).eLpNorm_ne_top
    have hHijfin (i : Fin d) (j : Fin d) :
        parabolicELpNormOn d (fun z => velocityHessian u z i j)
          (parabolicMorreyUnitBox d) ≠ ⊤ := by
      exact (Continuous.memLp_parabolicMorreyUnitBox
        ((continuous_pi_iff.mp (continuous_pi_iff.mp
          (continuous_velocityHessian_local hu) i)) j)).eLpNorm_ne_top
    have hHfin : H ≠ ⊤ := by
      dsimp only [H]
      refine ENNReal.sum_ne_top.mpr fun i _ => ?_
      exact ENNReal.sum_ne_top.mpr fun j _ => hHijfin i j
    have hSENN : parabolicELpNormOn d S (parabolicMorreyUnitBox d) <=
        ENNReal.ofReal CsENN * H := by
      simpa only [S, H] using hCsENN u hu
    have hSfin : parabolicELpNormOn d S (parabolicMorreyUnitBox d) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hHfin) hSENN
    have hDENN : parabolicELpNormOn d D (parabolicMorreyUnitBox d) <=
        ENNReal.ofReal Ct * T := by
      simpa only [D, T, Ct] using
        parabolicMorreyUnitTemporalAffinePoincareELpNorm_le d u hu
    have hDfin : parabolicELpNormOn d D (parabolicMorreyUnitBox d) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hTfin) hDENN
    have hSpatialStrong : StronglyMeasurable
        (parabolicMorreyUnitSpatialAffineProjection u) :=
      stronglyMeasurable_parabolicMorreyUnitSpatialAffineProjection hu.continuous
    have hSmeas : AEStronglyMeasurable S (volume.restrict (parabolicMorreyUnitBox d)) := by
      exact (hu.continuous.stronglyMeasurable.sub hSpatialStrong).aestronglyMeasurable
    have hDmeas : AEStronglyMeasurable D (volume.restrict (parabolicMorreyUnitBox d)) := by
      exact StronglyMeasurable.aestronglyMeasurable
        (hSpatialStrong.sub
          (continuous_parabolicMorreyUnitAffineProjection_local u).stronglyMeasurable)
    have hp : (1 : ENNReal) <= parabolicExponent d := by
      simpa only [parabolicExponent] using
        (le_add_of_nonneg_left (show (0 : ENNReal) <= d from bot_le))
    have hdecomp :
        (fun z => u z - parabolicMorreyUnitAffineProjection u z) = S + D := by
      funext z
      dsimp only [S, D, Pi.add_apply]
      ring
    have htriangle : parabolicELpNormOn d (S + D) (parabolicMorreyUnitBox d) <=
        parabolicELpNormOn d S (parabolicMorreyUnitBox d) +
          parabolicELpNormOn d D (parabolicMorreyUnitBox d) := by
      exact MeasureTheory.eLpNorm_add_le hp
    have hSDfin : parabolicELpNormOn d S (parabolicMorreyUnitBox d) +
        parabolicELpNormOn d D (parabolicMorreyUnitBox d) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨hSfin, hDfin⟩
    have hRealTriangle :
        (parabolicELpNormOn d
          (fun z => u z - parabolicMorreyUnitAffineProjection u z)
          (parabolicMorreyUnitBox d)).toReal <=
          (parabolicELpNormOn d S (parabolicMorreyUnitBox d)).toReal +
            (parabolicELpNormOn d D (parabolicMorreyUnitBox d)).toReal := by
      rw [hdecomp]
      have h := ENNReal.toReal_mono hSDfin htriangle
      rw [ENNReal.toReal_add hSfin hDfin] at h
      exact h
    have hSReal : (parabolicELpNormOn d S (parabolicMorreyUnitBox d)).toReal <=
        Cs * ∑ i : Fin d, ∑ j : Fin d,
          (parabolicELpNormOn d (fun z => velocityHessian u z i j)
            (parabolicMorreyUnitBox d)).toReal := by
      simpa only [S, parabolicLpNormOn] using hCs u hu
    have hDReal : (parabolicELpNormOn d D (parabolicMorreyUnitBox d)).toReal <=
        Ct * (parabolicELpNormOn d (timeDerivative u)
          (parabolicMorreyUnitBox d)).toReal := by
      simpa only [D, Ct, parabolicLpNormOn] using
        parabolicMorreyUnitTemporalAffinePoincareLpNorm_le d u hu
    have hTnonneg : 0 <= (parabolicELpNormOn d (timeDerivative u)
        (parabolicMorreyUnitBox d)).toReal := ENNReal.toReal_nonneg
    have hHnonneg : 0 <= H.toReal := ENNReal.toReal_nonneg
    have hCtNonneg : 0 <= Ct := by
      dsimp only [Ct]
      positivity
    unfold parabolicLpNormOn
    have hHtoReal : H.toReal = ∑ i : Fin d, ∑ j : Fin d,
        (parabolicELpNormOn d (fun z => velocityHessian u z i j)
          (parabolicMorreyUnitBox d)).toReal := by
      dsimp only [H]
      rw [ENNReal.toReal_sum fun i _ =>
        ENNReal.sum_ne_top.mpr fun j _ => hHijfin i j]
      apply Finset.sum_congr rfl
      intro i _
      exact ENNReal.toReal_sum fun j _ => hHijfin i j
    rw [← hHtoReal] at hSReal
    rw [← hHtoReal]
    calc
      (parabolicELpNormOn d
        (fun z => u z - parabolicMorreyUnitAffineProjection u z)
        (parabolicMorreyUnitBox d)).toReal <=
          (parabolicELpNormOn d S (parabolicMorreyUnitBox d)).toReal +
            (parabolicELpNormOn d D (parabolicMorreyUnitBox d)).toReal := hRealTriangle
      _ <= Cs * H.toReal + Ct * T.toReal := by
        change _ <= Cs * H.toReal + Ct *
          (parabolicELpNormOn d (timeDerivative u) (parabolicMorreyUnitBox d)).toReal
        exact add_le_add hSReal hDReal
      _ <= (Cs + Ct) * (T.toReal + H.toReal) := by
        change Cs * H.toReal + Ct *
          (parabolicELpNormOn d (timeDerivative u) (parabolicMorreyUnitBox d)).toReal <=
            (Cs + Ct) *
              ((parabolicELpNormOn d (timeDerivative u)
                (parabolicMorreyUnitBox d)).toReal + H.toReal)
        nlinarith [hCsPos.le]

end HypoellipticAleksandrov.Parabolic

module

public import HypoellipticAleksandrov.Parabolic.MovingLensSourceABP
public import HypoellipticAleksandrov.Parabolic.LocalClassical
public import HypoellipticAleksandrov.Measure.TimeVelocity
public import PDEFoundation.Measure.LpPower
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Supplied-source lower bound on a physical moving lens

This module closes the physical-coordinate contact/area argument with the
finite restricted parabolic norm of the supplied source.  It uses no
transformed operator or measure surface.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped ENNReal MatrixOrder

private def movingLensSourceConstant (d : Nat) (lam kappa : Real) : Real :=
  (4 / ((d : Real) + 1)) *
    ((movingLensVelocityFootprint d kappa ^ d) /
      ((volume (PDE.euclideanBall (0 : PDE.Vec d) 1)).toReal * lam ^ d)) ^
        (1 / ((d : Real) + 1) : Real)

private theorem parabolicExponent_eq_ofReal (d : Nat) :
    parabolicExponent d = ENNReal.ofReal ((d : Real) + 1) := by
  rw [show ((d : Real) + 1) = ((d + 1 : Nat) : Real) by norm_num]
  simpa only [parabolicExponent, Nat.cast_add, Nat.cast_one] using
    (ENNReal.ofReal_natCast (d + 1)).symm

private theorem source_memLp_movingLensClosed
    {d : Nat} {kappa eps tau : Real} {y : PDE.Vec d}
    (hkappa : 0 < kappa) (heps : 0 < eps) (htau : 0 < tau)
    (F : TimeVelocity d -> Real)
    (hF : ContinuousOn F
      (movingLensClosed (movingLensSignXi kappa) eps tau y)) :
    MemLp F (parabolicExponent d)
      (volume.restrict (movingLensClosed (movingLensSignXi kappa) eps tau y)) := by
  let L := movingLensClosed (movingLensSignXi kappa) eps tau y
  have hxi : 0 <= movingLensSignXi kappa := by
    unfold movingLensSignXi
    positivity
  have hLcompact : IsCompact L :=
    isCompact_movingLensClosed hxi heps htau.le
  have hLmeas : MeasurableSet L := hLcompact.measurableSet
  letI : IsFiniteMeasure (volume.restrict L) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hLcompact.measure_lt_top⟩
  obtain ⟨C, hC⟩ := hLcompact.exists_bound_of_continuousOn hF
  refine MemLp.of_bound (hF.aestronglyMeasurable hLmeas) C ?_
  filter_upwards [ae_restrict_mem hLmeas] with z hz
  exact hC z hz

private theorem parabolicLpNormOn_movingLensClosed_eq_integral_abs_pow
    {d : Nat} {kappa eps tau : Real} {y : PDE.Vec d}
    {F : TimeVelocity d -> Real}
    (hFmem : MemLp F (parabolicExponent d)
      (volume.restrict (movingLensClosed (movingLensSignXi kappa) eps tau y))) :
    parabolicLpNormOn d F
      (movingLensClosed (movingLensSignXi kappa) eps tau y) =
      (∫ z in movingLensClosed (movingLensSignXi kappa) eps tau y,
        |F z| ^ (d + 1) ∂volume) ^ (1 / ((d : Real) + 1) : Real) := by
  have hp : 0 < (d : Real) + 1 := by positivity
  have hFmem' : MemLp F (ENNReal.ofReal ((d : Real) + 1))
      (volume.restrict (movingLensClosed (movingLensSignXi kappa) eps tau y)) := by
    rw [<- parabolicExponent_eq_ofReal]
    exact hFmem
  rw [parabolicLpNormOn, parabolicELpNormOn, parabolicExponent_eq_ofReal]
  calc
    (eLpNorm F (ENNReal.ofReal ((d : Real) + 1))
        (volume.restrict (movingLensClosed (movingLensSignXi kappa) eps tau y))).toReal =
      (∫ z in movingLensClosed (movingLensSignXi kappa) eps tau y,
        ‖F z‖ ^ ((d : Real) + 1) ∂volume) ^ (1 / ((d : Real) + 1) : Real) :=
      PDE.toReal_eLpNorm_ofReal_eq_integral_rpow_norm_rpow_inv hp hFmem'
    _ = (∫ z in movingLensClosed (movingLensSignXi kappa) eps tau y,
        |F z| ^ (d + 1) ∂volume) ^ (1 / ((d : Real) + 1) : Real) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with z
      rw [Real.norm_eq_abs,
        show ((d : Real) + 1) = ((d + 1 : Nat) : Real) by norm_num,
        Real.rpow_natCast]

private theorem movingLensSourceConstant_pos
    (d : Nat) {lam kappa : Real} (hlam : 0 < lam) (hkappa : 0 < kappa) :
    0 < movingLensSourceConstant d lam kappa := by
  have hp : 0 < (d : Real) + 1 := by positivity
  have homega : 0 < (volume (PDE.euclideanBall (0 : PDE.Vec d) 1)).toReal :=
    PDE.volume_euclideanBall_toReal_pos (0 : PDE.Vec d) (by norm_num)
  have hlamPow : 0 < lam ^ d := pow_pos hlam d
  have hR : 0 < movingLensVelocityFootprint d kappa := by
    unfold movingLensVelocityFootprint
    exact add_pos_of_pos_of_nonneg hkappa
      (mul_nonneg (Real.sqrt_nonneg _) (zpow_nonneg (le_of_lt hkappa) _))
  unfold movingLensSourceConstant
  exact mul_pos (div_pos (by norm_num) hp)
    (Real.rpow_pos_of_pos (div_pos (pow_pos hR d) (mul_pos homega hlamPow)) _)

private theorem measurable_movingLensSourceSignSet_of_localC2
    {d : Nat} {xi eps tau : Real} {y : PDE.Vec d}
    {u : TimeVelocity d -> Real}
    (hlocal : ∀ z ∈ movingLensActive xi eps tau y, ContDiffAt Real 2 u z) :
    MeasurableSet (movingLensSourceSignSet xi eps tau y u) := by
  let O : Set (TimeVelocity d) := {z | 0 < z.1 /\ z.1 < tau /\
    PDE.vecNormSq (movingLensDisplacement y z) < movingLensDenominator xi eps z.1}
  have hO : IsOpen O := by
    rw [show O = {z | 0 < z.1 /\
        PDE.vecNormSq (movingLensDisplacement y z) < movingLensDenominator xi eps z.1} ∩
          {z | z.1 < tau} by
      ext z
      change (0 < z.1 /\ z.1 < tau /\
          PDE.vecNormSq (movingLensDisplacement y z) < movingLensDenominator xi eps z.1) ↔
        ((0 < z.1 /\
          PDE.vecNormSq (movingLensDisplacement y z) < movingLensDenominator xi eps z.1) /\
          z.1 < tau)
      constructor
      · rintro ⟨ht0, httau, hspatial⟩
        exact ⟨⟨ht0, hspatial⟩, httau⟩
      · rintro ⟨⟨ht0, hspatial⟩, httau⟩
        exact ⟨ht0, httau, hspatial⟩]
    exact (isOpen_movingLensPositiveSpatialStrict xi eps y).inter
      (isOpen_Iio.preimage continuous_fst)
  have hO_active : O ⊆ movingLensActive xi eps tau y := by
    rintro z ⟨hzpos, hzlt, hzspatial⟩
    exact ⟨hzpos, hzlt.le, hzspatial⟩
  have huO : ContDiffOn Real 2 u O := fun z hz =>
    (hlocal z (hO_active hz)).contDiffWithinAt
  have hDu : ContDiffOn Real 1 (fderiv Real u) O :=
    huO.fderiv_of_isOpen hO (by norm_num)
  have hD2u : ContDiffOn Real 0 (fderiv Real (fderiv Real u)) O :=
    hDu.fderiv_of_isOpen hO (by norm_num)
  have hucont : ContinuousOn u O := huO.continuousOn
  have htime : ContinuousOn (timeDerivative u) O := by
    unfold timeDerivative
    simpa using hDu.continuousOn.clm_apply continuousOn_const
  have hhess : ContinuousOn (velocityHessian u) O := by
    change ContinuousOn (fun z i j => velocityHessian u z i j) O
    unfold velocityHessian
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    simpa using hD2u.continuousOn.clm_apply continuousOn_const |>.clm_apply continuousOn_const
  have hpsdclosed : IsClosed {H : PDE.Mat d | H.PosSemidef} := by
    have hhermitian : IsClosed {H : PDE.Mat d | H.IsHermitian} := by
      have hset :
          {H : PDE.Mat d | H.IsHermitian} =
            ⋂ i : Fin d, ⋂ j : Fin d, {H : PDE.Mat d | H j i = H i j} := by
        ext H
        simp only [Set.mem_setOf_eq, Set.mem_iInter]
        constructor
        · intro h i j
          simpa using h.apply i j
        · intro h
          apply Matrix.IsHermitian.ext
          intro i j
          simpa using h i j
      rw [hset]
      refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
      exact isClosed_eq (continuous_id.matrix_elem j i) (continuous_id.matrix_elem i j)
    have hset :
        {H : PDE.Mat d | H.PosSemidef} =
          {H : PDE.Mat d | H.IsHermitian} ∩
            ⋂ q : PDE.Vec d, {H : PDE.Mat d | 0 ≤ dotProduct q (H.mulVec q)} := by
      ext H
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
      simpa using (Matrix.posSemidef_iff_dotProduct_mulVec (M := H))
    rw [hset]
    refine hhermitian.inter (isClosed_iInter fun q => ?_)
    have hquad : Continuous (fun H : PDE.Mat d => dotProduct q (H.mulVec q)) :=
      continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
    exact isClosed_le continuous_const hquad
  have hpositive : MeasurableSet (O ∩ {z | 0 < u z}) :=
    (hucont.isOpen_inter_preimage hO isOpen_Ioi).measurableSet
  have hnonnegative : MeasurableSet (O ∩ {z | 0 ≤ timeDerivative u z}) := by
    rw [show O ∩ {z | 0 ≤ timeDerivative u z} =
        O \ (O ∩ (timeDerivative u) ⁻¹' Set.Iio 0) by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_preimage, Set.mem_setOf_eq,
        Set.mem_Iio]
      constructor
      · rintro ⟨hz, htimez⟩
        exact ⟨hz, fun hnegative => not_lt_of_ge htimez hnegative.2⟩
      · rintro ⟨hz, hnotnegative⟩
        exact ⟨hz, le_of_not_gt fun hnegative => hnotnegative ⟨hz, hnegative⟩⟩]
    exact hO.measurableSet.diff
      (htime.isOpen_inter_preimage hO isOpen_Iio).measurableSet
  have hpsd : MeasurableSet (O ∩ {z | (-velocityHessian u z).PosSemidef}) := by
    rw [show O ∩ {z | (-velocityHessian u z).PosSemidef} = O \ (O ∩
        (fun z => -velocityHessian u z) ⁻¹' {H : PDE.Mat d | H.PosSemidef}ᶜ) by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_preimage, Set.mem_setOf_eq,
        Set.mem_compl_iff]
      constructor
      · rintro ⟨hz, hzpsd⟩
        exact ⟨hz, fun hnotpsd => hnotpsd.2 hzpsd⟩
      · rintro ⟨hz, hnotpsd⟩
        exact ⟨hz, not_not.mp fun hzpsd => hnotpsd ⟨hz, hzpsd⟩⟩]
    exact hO.measurableSet.diff
      ((hhess.neg).isOpen_inter_preimage hO hpsdclosed.isOpen_compl).measurableSet
  rw [show movingLensSourceSignSet xi eps tau y u =
      (O ∩ {z | 0 < u z}) ∩ (O ∩ {z | 0 ≤ timeDerivative u z}) ∩
        (O ∩ {z | (-velocityHessian u z).PosSemidef}) by
    ext z
    change (0 < z.1 /\ z.1 < tau /\
      PDE.vecNormSq (movingLensDisplacement y z) < movingLensDenominator xi eps z.1 /\
      0 < u z /\ 0 ≤ timeDerivative u z /\ (-velocityHessian u z).PosSemidef) ↔
      ((z ∈ O /\ 0 < u z) /\ (z ∈ O /\ 0 ≤ timeDerivative u z)) /\
        (z ∈ O /\ (-velocityHessian u z).PosSemidef)
    constructor
    · rintro ⟨ht0, httau, hspatial, hpositivez, htimez, hpsdz⟩
      exact ⟨⟨⟨⟨ht0, httau, hspatial⟩, hpositivez⟩,
        ⟨⟨ht0, httau, hspatial⟩, htimez⟩⟩,
        ⟨⟨ht0, httau, hspatial⟩, hpsdz⟩⟩
    · rintro ⟨⟨⟨hOpositive, hpositivez⟩, ⟨hOtime, htimez⟩⟩, ⟨hOpsd, hpsdz⟩⟩
      exact ⟨hOpositive.1, hOpositive.2.1, hOpositive.2.2,
        hpositivez, htimez, hpsdz⟩]
  exact (hpositive.inter hnonnegative).inter hpsd

private theorem movingLens_wedge_le_source_lintegral
    {d : Nat} {lam kappa eps tau : Real} {y : PDE.Vec d}
    {A : CoefficientField d} {F u : TimeVelocity d -> Real} {M : Real}
    (hlam : 0 < lam)
    (hFcont : ContinuousOn F
      (movingLensClosed (movingLensSignXi kappa) eps tau y))
    (hulocal : ∀ z ∈ movingLensActive (movingLensSignXi kappa) eps tau y,
      ContDiffAt Real 2 u z)
    (hlower : HasLowerEllipticityOn lam A
      (movingLensActive (movingLensSignXi kappa) eps tau y))
    (hsub : ∀ z ∈ movingLensActive (movingLensSignXi kappa) eps tau y,
      parabolicOperator A u z <= F z)
    (hcoverage : movingLensSlopeInterceptWedge d
      (movingLensVelocityFootprint d kappa) M ⊆
        parabolicNormalMap u 0 ''
          movingLensSourceSignSet (movingLensSignXi kappa) eps tau y u) :
    volume (movingLensSlopeInterceptWedge d
      (movingLensVelocityFootprint d kappa) M) <=
      ∫⁻ z in movingLensClosed (movingLensSignXi kappa) eps tau y,
        ENNReal.ofReal (|F z| ^ (d + 1) /
          ((((d : Real) + 1) ^ (d + 1)) * lam ^ d)) ∂volume := by
  let xi := movingLensSignXi kappa
  let L := movingLensClosed xi eps tau y
  let S := movingLensSourceSignSet xi eps tau y u
  let q : Real := ((d : Real) + 1) ^ (d + 1)
  have hqpos : 0 < q := by
    dsimp [q]
    positivity
  have hlamPow : 0 < lam ^ d := pow_pos hlam d
  have hdenpos : 0 < q * lam ^ d := mul_pos hqpos hlamPow
  have harea := movingLensSlopeInterceptWedge_volume_le_lintegral_abs_det_fderiv
    hulocal hcoverage
  have hSL : S ⊆ L := by
    intro z hz
    exact movingLensActive_subset_movingLensClosed xi eps tau y
      ⟨hz.1, hz.2.1.le, hz.2.2.1⟩
  have hpointwise : ∀ z ∈ S,
      ENNReal.ofReal |((fderiv Real (parabolicNormalMap u 0) z).det)| <=
        ENNReal.ofReal (|F z| ^ (d + 1) / (q * lam ^ d)) := by
    intro z hz
    have hzActive : z ∈ movingLensActive xi eps tau y :=
      ⟨hz.1, hz.2.1.le, hz.2.2.1⟩
    have hlo := hlower.le hzActive
    have hposdef := posDef_of_loewner_lower hlam hlo
    have hdetlower := det_lower_of_loewner hlam hlo
    have hJ := abs_det_fderiv_parabolicNormalMap_le_source_of_signs (y₀ := 0)
      (hulocal z hzActive) hz.2.2.2.2.1 hz.2.2.2.2.2 hposdef (hsub z hzActive)
    have hdenle : q * lam ^ d <= q * (coefficientAt A z).det :=
      mul_le_mul_of_nonneg_left hdetlower hqpos.le
    have hfirst : |((fderiv Real (parabolicNormalMap u 0) z).det)| <=
        (max (F z) 0) ^ (d + 1) / (q * lam ^ d) := by
      calc
        |((fderiv Real (parabolicNormalMap u 0) z).det)| <=
            (max (F z) 0) ^ (d + 1) / (q * (coefficientAt A z).det) := by
          simpa only [q, mul_assoc] using hJ
        _ <= (max (F z) 0) ^ (d + 1) / (q * lam ^ d) :=
          div_le_div_of_nonneg_left (pow_nonneg (le_max_right _ _) _) hdenpos hdenle
    apply ENNReal.ofReal_le_ofReal
    calc
      |((fderiv Real (parabolicNormalMap u 0) z).det)| <=
          (max (F z) 0) ^ (d + 1) / (q * lam ^ d) := hfirst
      _ <= |F z| ^ (d + 1) / (q * lam ^ d) :=
        div_le_div_of_nonneg_right
          (pow_le_pow_left₀ (le_max_right _ _)
            (max_le (le_abs_self _) (abs_nonneg _)) _) hdenpos.le
  have hsign :
      (∫⁻ z in S,
        ENNReal.ofReal |((fderiv Real (parabolicNormalMap u 0) z).det)| ∂volume) <=
        ∫⁻ z in S, ENNReal.ofReal (|F z| ^ (d + 1) /
          (q * lam ^ d)) ∂volume := by
    apply MeasureTheory.setLIntegral_mono_ae
    · apply AEMeasurable.ennreal_ofReal
      exact ((hFcont.mono hSL).aemeasurable (by
        exact measurable_movingLensSourceSignSet_of_localC2 hulocal)).norm.pow_const
          (d + 1) |>.div_const _
    · exact ae_of_all _ fun z hz => hpointwise z hz
  calc
    volume (movingLensSlopeInterceptWedge d
        (movingLensVelocityFootprint d kappa) M) <=
        ∫⁻ z in S,
          ENNReal.ofReal |((fderiv Real (parabolicNormalMap u 0) z).det)| ∂volume := harea
    _ <= ∫⁻ z in S, ENNReal.ofReal (|F z| ^ (d + 1) /
        (q * lam ^ d)) ∂volume := hsign
    _ <= ∫⁻ z in L, ENNReal.ofReal (|F z| ^ (d + 1) /
        (q * lam ^ d)) ∂volume := MeasureTheory.lintegral_mono_set hSL
    _ = _ := by rfl

private theorem movingLensSourceConstant_mul_rpow_pow
    {d : Nat} {lam kappa I : Real}
    (hlam : 0 < lam) (hkappa : 0 < kappa) (hI : 0 <= I) :
    (movingLensSourceConstant d lam kappa *
      I ^ (1 / ((d : Real) + 1) : Real)) ^ (d + 1) =
      4 ^ (d + 1) * movingLensVelocityFootprint d kappa ^ d * I /
        ((((d : Real) + 1) ^ (d + 1)) *
          (volume (PDE.euclideanBall (0 : PDE.Vec d) 1)).toReal * lam ^ d) := by
  have hp : 0 < (d : Real) + 1 := by positivity
  have homega : 0 < (volume (PDE.euclideanBall (0 : PDE.Vec d) 1)).toReal :=
    PDE.volume_euclideanBall_toReal_pos (0 : PDE.Vec d) (by norm_num)
  have hlamPow : 0 < lam ^ d := pow_pos hlam d
  have hR : 0 < movingLensVelocityFootprint d kappa := by
    unfold movingLensVelocityFootprint
    exact add_pos_of_pos_of_nonneg hkappa
      (mul_nonneg (Real.sqrt_nonneg _) (zpow_nonneg (le_of_lt hkappa) _))
  have hratio : 0 <= movingLensVelocityFootprint d kappa ^ d /
      ((volume (PDE.euclideanBall (0 : PDE.Vec d) 1)).toReal * lam ^ d) :=
    div_nonneg (pow_nonneg hR.le _) (mul_nonneg homega.le hlamPow.le)
  have hrecip : 1 / ((d : Real) + 1) = ((d + 1 : Nat) : Real)⁻¹ := by
    norm_num [Nat.cast_add, one_div]
  have hpcast : (d : Real) + 1 = ((d + 1 : Nat) : Real) := by norm_num
  unfold movingLensSourceConstant
  rw [hpcast, mul_pow, mul_pow, one_div,
    Real.rpow_inv_natCast_pow hratio (Nat.succ_ne_zero d),
    Real.rpow_inv_natCast_pow hI (Nat.succ_ne_zero d)]
  rw [div_pow]
  field_simp [hp.ne', homega.ne', hlamPow.ne', hR.ne']

private theorem movingLens_source_height_le_constant_mul_norm
    {d : Nat} {lam kappa tau eps : Real} {y : PDE.Vec d}
    {A : CoefficientField d} {F u : TimeVelocity d -> Real}
    (hd : 0 < d) (hlam : 0 < lam) (hkappa : 0 < kappa)
    (hkappa_one : kappa <= 1) (htau : 0 < tau) (htau_kappa : tau <= kappa⁻¹)
    (heps : 0 < eps) (heps_small : 2 * eps ^ 2 < kappa ^ 2)
    (hy : PDE.vecNormSq y <= (d : Real) * kappa ^ (-4 : Int))
    (hucont : ContinuousOn u
      (movingLensClosed (movingLensSignXi kappa) eps tau y))
    (hFcont : ContinuousOn F
      (movingLensClosed (movingLensSignXi kappa) eps tau y))
    (hulocal : ∀ z ∈ movingLensActive (movingLensSignXi kappa) eps tau y,
      ContDiffAt Real 2 u z)
    (hlower : HasLowerEllipticityOn lam A
      (movingLensActive (movingLensSignXi kappa) eps tau y))
    (hsub : ∀ z ∈ movingLensActive (movingLensSignXi kappa) eps tau y,
      parabolicOperator A u z <= F z)
    (hboundary : ∀ z ∈ movingLensClosed (movingLensSignXi kappa) eps tau y \
      movingLensActive (movingLensSignXi kappa) eps tau y, u z <= 0) :
    u (tau, tau • y) <= movingLensSourceConstant d lam kappa *
      parabolicLpNormOn d F
        (movingLensClosed (movingLensSignXi kappa) eps tau y) := by
  let L := movingLensClosed (movingLensSignXi kappa) eps tau y
  let R := movingLensVelocityFootprint d kappa
  let omega := (volume (PDE.euclideanBall (0 : PDE.Vec d) 1)).toReal
  let q : Real := ((d : Real) + 1) ^ (d + 1)
  let I : Real := ∫ z in L, |F z| ^ (d + 1) ∂volume
  have hxi : 0 <= movingLensSignXi kappa := by
    unfold movingLensSignXi
    positivity
  have hLcompact : IsCompact L := isCompact_movingLensClosed hxi heps htau.le
  have hLmeas : MeasurableSet L := hLcompact.measurableSet
  have hFmem := source_memLp_movingLensClosed hkappa heps htau F hFcont
  have hFtop : parabolicELpNormOn d F L ≠ ∞ := by
    simpa only [parabolicELpNormOn] using hFmem.eLpNorm_ne_top
  have hnorm : parabolicLpNormOn d F L = I ^ (1 / ((d : Real) + 1) : Real) := by
    dsimp [I, L]
    exact parabolicLpNormOn_movingLensClosed_eq_integral_abs_pow hFmem
  have hR : 0 < R := by
    dsimp [R, movingLensVelocityFootprint]
    exact add_pos_of_pos_of_nonneg hkappa
      (mul_nonneg (Real.sqrt_nonneg _) (zpow_nonneg (le_of_lt hkappa) _))
  have homega : 0 < omega := by
    dsimp [omega]
    exact PDE.volume_euclideanBall_toReal_pos (0 : PDE.Vec d) (by norm_num)
  have hlamPow : 0 < lam ^ d := pow_pos hlam d
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hI : 0 <= I := by
    dsimp [I]
    exact integral_nonneg fun z => pow_nonneg (abs_nonneg _) _
  by_cases hMnonpos : u (tau, tau • y) <= 0
  · calc
      u (tau, tau • y) <= 0 := hMnonpos
      _ <= movingLensSourceConstant d lam kappa * parabolicLpNormOn d F L :=
        mul_nonneg (movingLensSourceConstant_pos d hlam hkappa).le
          (by unfold parabolicLpNormOn; exact ENNReal.toReal_nonneg)
  let M := u (tau, tau • y)
  have hM : 0 < M := lt_of_not_ge hMnonpos
  have hcoverage := movingLensSlopeInterceptWedge_subset_image_signSet_local
    d hd kappa tau eps y hkappa hkappa_one htau htau_kappa heps heps_small hy
    u hucont hulocal hboundary M hM (by rfl)
  have hwedge := movingLens_wedge_le_source_lintegral hlam hFcont hulocal hlower hsub hcoverage
  let g : TimeVelocity d -> Real := fun z => |F z| ^ (d + 1) / (q * lam ^ d)
  have hgcont : ContinuousOn g L := by
    apply (hFcont.norm.pow _).div continuousOn_const
    intro z hz
    exact (mul_pos hq hlamPow).ne'
  have hgint : IntegrableOn g L volume := hgcont.integrableOn_compact hLcompact
  have hgtop : (∫⁻ z in L, ENNReal.ofReal (g z) ∂volume) ≠ ∞ := by
    have hfinite := (MeasureTheory.hasFiniteIntegral_iff_norm _).mp
      hgint.integrable.hasFiniteIntegral
    apply ne_of_lt
    refine (lintegral_congr_ae ?_).symm ▸ hfinite
    filter_upwards [ae_restrict_mem hLmeas] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg]
    exact div_nonneg (pow_nonneg (abs_nonneg _) _) (mul_nonneg hq.le hlamPow.le)
  have hreal := ENNReal.toReal_mono hgtop hwedge
  have hg_real : (∫⁻ z in L, ENNReal.ofReal (g z) ∂volume).toReal =
      ∫ z in L, g z ∂volume := by
    symm
    refine integral_eq_lintegral_of_nonneg_ae ?_ hgint.aestronglyMeasurable
    filter_upwards [ae_restrict_mem hLmeas] with z hz
    exact div_nonneg (pow_nonneg (abs_nonneg _) _) (mul_nonneg hq.le hlamPow.le)
  have hpower : omega * M ^ (d + 1) /
      (4 ^ (d + 1) * R ^ d) <= I / (q * lam ^ d) := by
    rw [volume_movingLensSlopeInterceptWedge hR hM,
      ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (div_nonneg hM.le (by norm_num)),
      ENNReal.toReal_ofReal (pow_nonneg (div_nonneg hM.le
        (mul_nonneg (by norm_num) hR.le)) _)] at hreal
    rw [hg_real] at hreal
    have hleft : (M / 4) * ((M / (4 * R)) ^ d * omega) =
        omega * M ^ (d + 1) / (4 ^ (d + 1) * R ^ d) := by
      rw [div_pow]
      field_simp [hR.ne']
      ring
    rw [hleft, integral_div] at hreal
    exact hreal
  have hscaled : M ^ (d + 1) <=
      4 ^ (d + 1) * R ^ d * I / (q * omega * lam ^ d) := by
    calc
      M ^ (d + 1) =
          (omega * M ^ (d + 1) / (4 ^ (d + 1) * R ^ d)) *
      (4 ^ (d + 1) * R ^ d / omega) := by
        field_simp [homega.ne', hR.ne']
      _ <= (I / (q * lam ^ d)) * (4 ^ (d + 1) * R ^ d / omega) :=
        mul_le_mul_of_nonneg_right hpower (div_nonneg
          (mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg hR.le _)) homega.le)
      _ = 4 ^ (d + 1) * R ^ d * I / (q * omega * lam ^ d) := by
        field_simp [homega.ne', hq.ne', hlamPow.ne']
  have hconstpow := movingLensSourceConstant_mul_rpow_pow (d := d) hlam hkappa hI
  have hrootpower : M ^ (d + 1) <=
      (movingLensSourceConstant d lam kappa *
        I ^ (1 / ((d : Real) + 1) : Real)) ^ (d + 1) := by
    rw [hconstpow]
    simpa only [q, omega, R, mul_assoc] using hscaled
  have hrootnonneg : 0 <= movingLensSourceConstant d lam kappa *
      I ^ (1 / ((d : Real) + 1) : Real) :=
    mul_nonneg (movingLensSourceConstant_pos d hlam hkappa).le
      (Real.rpow_nonneg hI _)
  have hroot := le_of_pow_le_pow_left₀ (Nat.succ_ne_zero d) hrootnonneg hrootpower
  calc
    u (tau, tau • y) = M := rfl
    _ <= movingLensSourceConstant d lam kappa * I ^ (1 / ((d : Real) + 1) : Real) := hroot
    _ = movingLensSourceConstant d lam kappa * parabolicLpNormOn d F L := by rw [hnorm]

/-- A nonnegative supplied source bounds the lower terminal height on a
physical moving lens by its finite restricted parabolic `L^(d + 1)` norm. -/
theorem exists_movingLens_source_lower_bound
    (d : Nat) (hd : 0 < d) (lam Lam kappa : Real)
    (hlam : 0 < lam) (hlamLam : lam <= Lam)
    (hkappa : 0 < kappa) (hkappa_one : kappa <= 1) :
    ∃ C : Real, 0 < C ∧
      ∀ (A : CoefficientField d) (U : Set (TimeVelocity d))
        (F w : TimeVelocity d -> Real) (tau eps : Real) (y : PDE.Vec d),
        0 < tau -> tau <= kappa⁻¹ -> 0 < eps ->
        2 * eps ^ 2 < kappa ^ 2 ->
        PDE.vecNormSq y <= (d : Real) * kappa ^ (-4 : Int) ->
        IsOpen U ->
        movingLensClosed (movingLensSignXi kappa) eps tau y ⊆ U ->
        IsContinuousCoefficientOn A U ->
        ContinuousOn F U ->
        ContinuousOn w (movingLensClosed (movingLensSignXi kappa) eps tau y) ->
        (∀ z ∈ movingLensActive (movingLensSignXi kappa) eps tau y,
          ContDiffAt Real 2 w z) ->
        HasLowerEllipticityOn lam A
          (movingLensActive (movingLensSignXi kappa) eps tau y) ->
        HasUpperEllipticityOn Lam A
          (movingLensActive (movingLensSignXi kappa) eps tau y) ->
        IsNonnegativeOn F (movingLensActive (movingLensSignXi kappa) eps tau y) ->
        IsParabolicSupersolutionOn A (fun z => -F z) w
          (movingLensActive (movingLensSignXi kappa) eps tau y) ->
        (∀ z ∈ movingLensClosed (movingLensSignXi kappa) eps tau y \
          movingLensActive (movingLensSignXi kappa) eps tau y, 0 <= w z) ->
        -C * parabolicLpNormOn d F
          (movingLensClosed (movingLensSignXi kappa) eps tau y) <=
          w (tau, tau • y) := by
  refine ⟨movingLensSourceConstant d lam kappa,
    movingLensSourceConstant_pos d hlam hkappa, ?_⟩
  intro A U F w tau eps y htau htau_kappa heps heps_small hy hU hLU hAcont hF hwcont
    hwlocal hlower hupper hFnonneg hsuper hboundary
  let u : TimeVelocity d -> Real := fun z => -w z
  have hucont : ContinuousOn u
      (movingLensClosed (movingLensSignXi kappa) eps tau y) := hwcont.neg
  have hFcont : ContinuousOn F
      (movingLensClosed (movingLensSignXi kappa) eps tau y) := hF.mono hLU
  have hulocal : ∀ z ∈ movingLensActive (movingLensSignXi kappa) eps tau y,
      ContDiffAt Real 2 u z := by
    intro z hz
    exact (hwlocal z hz).neg
  have hsub : ∀ z ∈ movingLensActive (movingLensSignXi kappa) eps tau y,
      parabolicOperator A u z <= F z := by
    intro z hz
    have h := hsuper z hz
    change parabolicOperator A (fun q => -w q) z <= F z
    rw [parabolicOperator_neg]
    change -F z <= parabolicOperator A w z at h
    linarith
  have huboundary : ∀ z ∈ movingLensClosed (movingLensSignXi kappa) eps tau y \
      movingLensActive (movingLensSignXi kappa) eps tau y, u z <= 0 := by
    intro z hz
    change -w z <= 0
    linarith [hboundary z hz]
  have hheight := movingLens_source_height_le_constant_mul_norm
    hd hlam hkappa hkappa_one htau htau_kappa heps heps_small hy hucont hFcont hulocal
    hlower hsub huboundary
  change -movingLensSourceConstant d lam kappa *
      parabolicLpNormOn d F (movingLensClosed (movingLensSignXi kappa) eps tau y) <=
      w (tau, tau • y)
  have hheight' : -w (tau, tau • y) <= movingLensSourceConstant d lam kappa *
      parabolicLpNormOn d F (movingLensClosed (movingLensSignXi kappa) eps tau y) := by
    simpa only [u] using hheight
  linarith

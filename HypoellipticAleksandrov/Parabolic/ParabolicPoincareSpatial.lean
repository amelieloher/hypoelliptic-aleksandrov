module

public import HypoellipticAleksandrov.Parabolic.ParabolicPoincareVelocityMoments
public import HypoellipticAleksandrov.Parabolic.ParabolicPoincareProduct
public import PDEFoundation.Sobolev.Inequalities.ConvexPoincare
public import PDEFoundation.Sobolev.W1p.Smooth
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Spatial-slice transport for parabolic Poincare

This module identifies the native unit velocity cube with the PDEFoundation
axis cube and proves the private fixed-time gradient-mean affine Poincare
estimate and canonical-projection comparison, then lifts them globally through
the two public spatial inequalities.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory

private theorem velocityCube_zero_one_eq_axisCube_neg_one_two (d : Nat) :
    velocityCube (0 : PDE.Vec d) 1 =
      PDE.axisCube (-1 : PDE.Vec d) 2 := by
  ext v
  simp only [mem_velocityCube_iff, PDE.axisCube, Set.mem_pi]
  constructor
  · intro hv i _
    have hvi := hv i
    rw [abs_lt] at hvi
    simp only [Pi.zero_apply, Pi.neg_apply, Pi.one_apply, sub_zero] at hvi ⊢
    constructor <;> linarith
  · intro hv i
    have hvi := hv i (Set.mem_univ i)
    simp only [Pi.neg_apply, Pi.one_apply] at hvi
    change -1 < v i ∧ v i < -1 + 2 at hvi
    rw [abs_lt]
    simp only [Pi.zero_apply, sub_zero]
    constructor <;> linarith

private theorem volumeOn_velocityCube_zero_one_eq_axisCube (d : Nat) :
    (volume : Measure (PDE.Vec d)).restrict
        (velocityCube (0 : PDE.Vec d) 1) =
      volume.restrict (PDE.axisCube (-1 : PDE.Vec d) 2) := by
  rw [velocityCube_zero_one_eq_axisCube_neg_one_two d]

private theorem eLpNormOn_velocityCube_zero_one_eq_axisCube (d : Nat)
    (p : ENNReal) (f : PDE.Vec d -> Real) :
    PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1) p f =
      PDE.eLpNormOn (PDE.axisCube (-1 : PDE.Vec d) 2) p f := by
  rw [velocityCube_zero_one_eq_axisCube_neg_one_two d]

private theorem euclideanFieldELpNormOn_velocityCube_zero_one_eq_axisCube
    (d : Nat) (p : ENNReal) (F : PDE.Vec d -> PDE.Vec d) :
    PDE.euclideanFieldELpNormOn (velocityCube (0 : PDE.Vec d) 1) p F =
      PDE.euclideanFieldELpNormOn (PDE.axisCube (-1 : PDE.Vec d) 2) p F := by
  rw [velocityCube_zero_one_eq_axisCube_neg_one_two d]

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

private theorem parabolicExponent_eq_ofReal (d : Nat) :
    parabolicExponent d = ENNReal.ofReal ((d : Real) + 1) := by
  rw [show ((d : Real) + 1) = ((d + 1 : Nat) : Real) by norm_num]
  simpa only [parabolicExponent, Nat.cast_add, Nat.cast_one] using
    (ENNReal.ofReal_natCast (d + 1)).symm

private theorem contDiff_velocityGradient_slice
    {d : Nat} {u : TimeVelocity d -> Real}
    (hu : ContDiff Real 2 u) (t : Real) (i : Fin d) :
    ContDiff Real 1 (fun v : PDE.Vec d => velocityGradient u (t, v) i) := by
  exact (contDiff_pi.mp ((contDiff_velocityGradient hu).comp
    (contDiff_const.prodMk contDiff_id))) i

private theorem fderiv_velocityGradient_apply
    {d : Nat} {u : TimeVelocity d -> Real}
    (hu : ContDiff Real 2 u) (z qi qj : TimeVelocity d) :
    fderiv Real (fun x => fderiv Real u x qi) z qj =
      fderiv Real (fderiv Real u) z qj qi := by
  have hderiv : DifferentiableAt Real (fderiv Real u) z :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) z
  rw [fderiv_clm_apply hderiv (differentiableAt_const (c := qi))]
  simp

private theorem classicalGradient_velocityGradient_slice_apply
    {d : Nat} {u : TimeVelocity d -> Real}
    (hu : ContDiff Real 2 u) (t : Real) (v : PDE.Vec d)
    (i j : Fin d) :
    PDE.classicalGradient
        (fun w : PDE.Vec d => velocityGradient u (t, w) i) v j =
      velocityHessian u (t, v) i j := by
  rw [PDE.classicalGradient_apply]
  have hdiff : DifferentiableAt Real (fun z => velocityGradient u z i) (t, v) :=
    ((contDiff_pi.mp (contDiff_velocityGradient hu) i).differentiable
      (by norm_num)) (t, v)
  have hslice := hdiff.hasFDerivAt.comp v (hasFDerivAt_prodMk_right t v)
  change (fderiv Real ((fun z => velocityGradient u z i) ∘ Prod.mk t) v)
      (PDE.basisVec j) = velocityHessian u (t, v) i j
  rw [hslice.fderiv]
  change fderiv Real (fun z => velocityGradient u z i) (t, v)
      (0, Pi.single j 1) = velocityHessian u (t, v) i j
  calc
    fderiv Real (fun z => velocityGradient u z i) (t, v) (0, Pi.single j 1) =
        velocityHessian u (t, v) j i :=
      fderiv_velocityGradient_apply hu (t, v)
        (0, Pi.single i 1) (0, Pi.single j 1)
    _ = velocityHessian u (t, v) i j := by
      exact congrFun (congrFun (velocityHessian_isSymm hu (t, v)).eq i) j

private theorem velocityGradient_axisCube_subAverage_eLpNorm_le_hessian_sum
    (d : Nat) (u : TimeVelocity d -> Real)
    (hu : ContDiff Real 2 u) (t : Real) (i : Fin d) :
    PDE.eLpNormOn (PDE.axisCube (-1 : PDE.Vec d) 2)
        (parabolicExponent d)
        (fun v => velocityGradient u (t, v) i -
          PDE.integralAverage (PDE.axisCube (-1 : PDE.Vec d) 2)
            (fun w => velocityGradient u (t, w) i)) <=
      ENNReal.ofReal (((2 : Real)^d) * (Real.sqrt d * 2)) *
        ∑ j : Fin d,
          PDE.eLpNormOn (PDE.axisCube (-1 : PDE.Vec d) 2)
            (parabolicExponent d)
            (fun v => velocityHessian u (t, v) i j) := by
  let p : Real := (d : Real) + 1
  let V : Set (PDE.Vec d) := PDE.axisCube (-1 : PDE.Vec d) 2
  let g : PDE.Vec d -> Real := fun v => velocityGradient u (t, v) i
  let w : PDE.W1pFunction V (ENNReal.ofReal p) :=
    PDE.W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain
      (PDE.isOpenBoundedConvexDomain_axisCube (-1 : PDE.Vec d) 2)
      (contDiff_velocityGradient_slice hu t i)
  have hp : 1 <= p := by
    dsimp [p]
    have hdnonneg : (0 : Real) <= (d : Real) := Nat.cast_nonneg d
    linarith
  letI : Fact (1 <= ENNReal.ofReal p) := by
    refine ⟨?_⟩
    rw [ENNReal.one_le_ofReal]
    exact hp
  letI : MeasureTheory.IsFiniteMeasure (PDE.volumeOn V) := by
    dsimp [V]
    exact PDE.isFiniteMeasure_volumeOn_axisCube (-1 : PDE.Vec d) 2
  have hPoincare := PDE.meanZeroPoincare_on_axisCube_unnormalized
    hp (-1 : PDE.Vec d) (by norm_num) w.subAverage
    (w.meanZeroOn_subAverage
      (PDE.volume_axisCube_pos (-1 : PDE.Vec d) (by norm_num))
      (lt_top_iff_ne_top.mpr
        (PDE.volume_axisCube_ne_top (-1 : PDE.Vec d) 2)))
  have hsubAverageToFun :
      w.subAverage.toFun = fun v => g v - PDE.integralAverage V g := by
    funext v
    rw [PDE.W1pFunction.subAverage_apply]
    rfl
  have hsubAverageGrad :
      w.subAverage.grad = fun v => PDE.classicalGradient g v := by
    funext v
    rw [PDE.W1pFunction.subAverage_grad]
    rfl
  have hPoincare' :
      PDE.eLpNormOn V (ENNReal.ofReal p)
          (fun v => g v - PDE.integralAverage V g) <=
        ENNReal.ofReal (((2 : Real)^d) * (Real.sqrt d * 2)) *
          PDE.euclideanFieldELpNormOn V (ENNReal.ofReal p)
            (fun v => PDE.classicalGradient g v) := by
    rw [hsubAverageToFun, hsubAverageGrad] at hPoincare
    exact hPoincare
  have hHessianContinuous :
      ∀ j : Fin d, Continuous (fun v => velocityHessian u (t, v) i j) := by
    intro j
    have hContinuous : Continuous
        (fun v => PDE.classicalGradient
          (fun w : PDE.Vec d => velocityGradient u (t, w) i) v j) := by
      simpa only [PDE.classicalGradient_apply] using
        ((contDiff_velocityGradient_slice hu t i).continuous_fderiv
          (by norm_num)).clm_apply continuous_const
    simpa only [classicalGradient_velocityGradient_slice_apply hu t] using hContinuous
  let F : PDE.Vec d -> PDE.Vec d :=
    fun v j => velocityHessian u (t, v) i j
  have hGradient :
      PDE.euclideanFieldELpNormOn V (ENNReal.ofReal p)
          (fun v => PDE.classicalGradient g v) <=
        ∑ j : Fin d,
          PDE.eLpNormOn V (ENNReal.ofReal p)
            (fun v => velocityHessian u (t, v) i j) := by
    calc
      PDE.euclideanFieldELpNormOn V (ENNReal.ofReal p)
          (fun v => PDE.classicalGradient g v) =
          PDE.euclideanFieldELpNormOn V (ENNReal.ofReal p) F := by
        apply PDE.euclideanFieldELpNormOn_congr_ae
        filter_upwards with v
        ext j
        exact classicalGradient_velocityGradient_slice_apply hu t v i j
      _ = MeasureTheory.eLpNorm (fun v => PDE.vecEuclideanNorm (F v))
          (ENNReal.ofReal p) (PDE.volumeOn V) := rfl
      _ <= MeasureTheory.eLpNorm (fun v => ∑ j : Fin d, |F v j|)
          (ENNReal.ofReal p) (PDE.volumeOn V) := by
        apply MeasureTheory.eLpNorm_mono_ae
          (PDE.continuous_vecEuclideanNorm.comp
            (continuous_pi fun j => hHessianContinuous j)).aestronglyMeasurable
        filter_upwards with v
        have hsumNonneg : 0 <= ∑ j : Fin d, |F v j| :=
          Finset.sum_nonneg fun j _ => abs_nonneg (F v j)
        simpa only [Function.comp_def, F, Real.norm_eq_abs,
          abs_of_nonneg (PDE.vecEuclideanNorm_nonneg (F v)),
          abs_of_nonneg hsumNonneg] using
          PDE.vecEuclideanNorm_le_sum_abs (F v)
      _ <= ∑ j : Fin d,
          MeasureTheory.eLpNorm (fun v => |F v j|) (ENNReal.ofReal p)
            (PDE.volumeOn V) := by
        rw [← Finset.sum_fn]
        exact MeasureTheory.eLpNorm_sum_le Fact.out
      _ = ∑ j : Fin d,
          PDE.eLpNormOn V (ENNReal.ofReal p)
            (fun v => velocityHessian u (t, v) i j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simpa only [F, PDE.eLpNormOn, Real.norm_eq_abs] using
          (MeasureTheory.eLpNorm_norm
            (μ := PDE.volumeOn V) (p := ENNReal.ofReal p)
            (fun v => velocityHessian u (t, v) i j)
            (hHessianContinuous j).aestronglyMeasurable)
  rw [parabolicExponent_eq_ofReal]
  simpa only [p, V, g] using
    hPoincare'.trans (mul_le_mul_right hGradient _)

private theorem velocityGradient_slice_subAverage_eLpNorm_le_hessian_sum
    (d : Nat) (u : TimeVelocity d -> Real)
    (hu : ContDiff Real 2 u) (t : Real) (i : Fin d) :
    PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1)
        (parabolicExponent d)
        (fun v => velocityGradient u (t, v) i -
          PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1)
            (fun w => velocityGradient u (t, w) i)) <=
      ENNReal.ofReal (((2 : Real)^d) * (Real.sqrt d * 2)) *
        ∑ j : Fin d,
          PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1)
            (parabolicExponent d)
            (fun v => velocityHessian u (t, v) i j) := by
  simpa only [velocityCube_zero_one_eq_axisCube_neg_one_two d] using
    velocityGradient_axisCube_subAverage_eLpNorm_le_hessian_sum d u hu t i

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory

private theorem velocitySlice_sub_gradientMeanAffine_eLpNorm_le
    (d : Nat) (u : TimeVelocity d -> Real)
    (hu : ContDiff Real 2 u) (t : Real) :
    PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1)
        (parabolicExponent d)
        (fun v => u (t, v) -
          (PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1)
              (fun w => u (t, w)) +
            ∑ i : Fin d,
              PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1)
                (fun w => velocityGradient u (t, w) i) * v i)) <=
      ENNReal.ofReal (((2 : Real)^d) * (Real.sqrt d * 2)) *
        ∑ i : Fin d,
          PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1)
            (parabolicExponent d)
            (fun v => velocityGradient u (t, v) i -
              PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1)
                (fun w => velocityGradient u (t, w) i)) := by
  let p : Real := (d : Real) + 1
  let V : Set (PDE.Vec d) := PDE.axisCube (-1 : PDE.Vec d) 2
  let V0 : Set (PDE.Vec d) := velocityCube (0 : PDE.Vec d) 1
  let m : Fin d -> Real := fun i => PDE.integralAverage V0
    (fun w => velocityGradient u (t, w) i)
  let a : PDE.Vec d -> Real := fun v => ∑ i : Fin d, m i * v i
  let g : PDE.Vec d -> Real := fun v => u (t, v) - a v
  have huSlice : ContDiff Real 2 (fun v : PDE.Vec d => u (t, v)) :=
    hu.comp (contDiff_const.prodMk contDiff_id)
  have ha : ContDiff Real 2 a := by
    exact ContDiff.sum (s := Finset.univ) fun i _ =>
      contDiff_const.mul (contDiff_apply Real Real i)
  let w : PDE.W1pFunction V (ENNReal.ofReal p) :=
    PDE.W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain
      (PDE.isOpenBoundedConvexDomain_axisCube (-1 : PDE.Vec d) 2)
      ((huSlice.sub ha).of_le (by norm_num))
  have hp : 1 <= p := by
    dsimp [p]
    have hdnonneg : (0 : Real) <= (d : Real) := Nat.cast_nonneg d
    linarith
  letI : Fact (1 <= ENNReal.ofReal p) := by
    refine ⟨?_⟩
    rw [ENNReal.one_le_ofReal]
    exact hp
  letI : MeasureTheory.IsFiniteMeasure (PDE.volumeOn V) := by
    dsimp [V]
    exact PDE.isFiniteMeasure_volumeOn_axisCube (-1 : PDE.Vec d) 2
  have hVPos : 0 < volume V := by
    dsimp [V]
    exact PDE.volume_axisCube_pos (-1 : PDE.Vec d) (by norm_num)
  have hVTop : volume V < ⊤ := by
    dsimp [V]
    exact lt_top_iff_ne_top.mpr
      (PDE.volume_axisCube_ne_top (-1 : PDE.Vec d) 2)
  have hcomponent : ∀ i : Fin d, Integrable (fun v : PDE.Vec d => m i * v i)
      (volume.restrict V0) := by
    intro i
    have hcont : Continuous (fun v : PDE.Vec d => m i * v i) :=
      continuous_const.mul (continuous_apply i)
    let K : Set (PDE.Vec d) := velocityClosedCube (0 : PDE.Vec d) 1
    have hKcompact : IsCompact K :=
      isCompact_velocityClosedCube (0 : PDE.Vec d) 1
    have hsubset : V0 ⊆ K := by
      intro v hv
      change ∀ i : Fin d, |v i - (0 : PDE.Vec d) i| < 1 at hv
      change ∀ i : Fin d, |v i - (0 : PDE.Vec d) i| <= 1
      intro j
      exact (hv j).le
    exact (hcont.continuousOn.integrableOn_compact hKcompact).mono_set hsubset
  have haIntegrable : Integrable a (volume.restrict V0) := by
    simpa only [a, Finset.sum_apply] using
      integrable_finset_sum (Finset.univ : Finset (Fin d)) fun i _ => hcomponent i
  have haAverage : PDE.integralAverage V a = 0 := by
    have hVV : V = V0 := by
      dsimp [V, V0]
      exact (velocityCube_zero_one_eq_axisCube_neg_one_two d).symm
    rw [hVV]
    unfold PDE.integralAverage
    rw [show (fun v : PDE.Vec d => ∑ i : Fin d, m i * v i) =
        fun v => ∑ i ∈ (Finset.univ : Finset (Fin d)), m i * v i by
          ext v
          rfl,
      integral_finset_sum (Finset.univ : Finset (Fin d))
        (fun i _ => hcomponent i), Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [integral_const_mul]
    calc
      (volume V0).toReal⁻¹ * (m i * ∫ v in V0, v i) =
          m i * ((volume V0).toReal⁻¹ * ∫ v in V0, v i) := by ring
      _ = 0 := by
        rw [← PDE.integralAverage, parabolicMorreyUnitVelocityAverage_eval]
        ring
  have hwIntegrable : Integrable g (volume.restrict V0) := by
    have hw : Integrable g (volume.restrict V) := by
      simpa only [w, g,
        PDE.W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain_toFun, IntegrableOn] using
        w.integrableOn
    have hVV : V = V0 := by
      dsimp [V, V0]
      exact (velocityCube_zero_one_eq_axisCube_neg_one_two d).symm
    simpa only [hVV] using hw
  have huIntegrable : Integrable (fun v : PDE.Vec d => u (t, v))
      (volume.restrict V0) := by
    have hsum : g + a = fun v => u (t, v) := by
      funext v
      dsimp [g]
      ring
    rw [← hsum]
    exact hwIntegrable.add haIntegrable
  have hgAverage : PDE.integralAverage V g = PDE.integralAverage V0
      (fun v => u (t, v)) := by
    have hVV : V = V0 := by
      dsimp [V, V0]
      exact (velocityCube_zero_one_eq_axisCube_neg_one_two d).symm
    have haAverage0 : PDE.integralAverage V0 a = 0 := by
      simpa only [hVV] using haAverage
    rw [hVV]
    unfold g
    calc
      PDE.integralAverage V0 (fun v => u (t, v) - a v) =
          PDE.integralAverage V0 (fun v => u (t, v)) -
            PDE.integralAverage V0 a := by
        unfold PDE.integralAverage
        rw [integral_sub huIntegrable haIntegrable]
        ring
      _ = PDE.integralAverage V0 (fun v => u (t, v)) := by
        rw [haAverage0]
        ring
  have hPoincare := PDE.meanZeroPoincare_on_axisCube_unnormalized
    hp (-1 : PDE.Vec d) (by norm_num) w.subAverage
    (w.meanZeroOn_subAverage hVPos hVTop)
  have hsubAverageToFun :
      w.subAverage.toFun = fun v => u (t, v) -
        (PDE.integralAverage V0 (fun z => u (t, z)) + a v) := by
    funext v
    rw [PDE.W1pFunction.subAverage_apply]
    change g v - PDE.integralAverage V g =
      u (t, v) - (PDE.integralAverage V0 (fun z => u (t, z)) + a v)
    rw [hgAverage]
    dsimp [g]
    ring
  have hgradient : ∀ v : PDE.Vec d, ∀ i : Fin d,
      PDE.classicalGradient g v i = velocityGradient u (t, v) i - m i := by
    intro v i
    rw [PDE.classicalGradient_apply]
    have huDiff : DifferentiableAt Real (fun z : PDE.Vec d => u (t, z)) v :=
      huSlice.differentiable (by norm_num) v
    have haDiff : DifferentiableAt Real a v := ha.differentiable (by norm_num) v
    rw [show g = (fun z : PDE.Vec d => u (t, z)) - a by rfl,
      fderiv_sub huDiff haDiff]
    have hslice := (hu.differentiable (by norm_num) (t, v)).hasFDerivAt.comp v
      (hasFDerivAt_prodMk_right t v)
    have huDeriv : fderiv Real (fun z : PDE.Vec d => u (t, z)) v
        (PDE.basisVec i) = velocityGradient u (t, v) i := by
      change fderiv Real (u ∘ Prod.mk t) v (PDE.basisVec i) =
        velocityGradient u (t, v) i
      rw [hslice.fderiv]
      change fderiv Real u (t, v) (0, Pi.single i 1) =
        velocityGradient u (t, v) i
      rfl
    have haFDeriv : HasFDerivAt a
        (∑ j : Fin d, m j • (ContinuousLinearMap.proj j : PDE.Vec d →L[Real] Real)) v := by
      have h := HasFDerivAt.sum (u := Finset.univ) fun j _ =>
        (hasFDerivAt_apply (𝕜 := Real) j v).const_mul (m j)
      convert h using 1
      ext x
      simp only [a, Finset.sum_apply]
    have haDeriv : fderiv Real a v (PDE.basisVec i) = m i := by
      rw [haFDeriv.fderiv]
      simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.proj_apply, PDE.basisVec, Pi.single_apply]
      simp
    simp only [ContinuousLinearMap.sub_apply]
    rw [huDeriv, haDeriv]
  have hsubAverageGrad :
      w.subAverage.grad = fun v => PDE.classicalGradient g v := by
    funext v
    rw [PDE.W1pFunction.subAverage_grad]
    rfl
  have hPoincare' :
      PDE.eLpNormOn V (ENNReal.ofReal p)
          (fun v => u (t, v) -
            (PDE.integralAverage V0 (fun z => u (t, z)) + a v)) <=
        ENNReal.ofReal (((2 : Real)^d) * (Real.sqrt d * 2)) *
          PDE.euclideanFieldELpNormOn V (ENNReal.ofReal p)
            (fun v => PDE.classicalGradient g v) := by
    rw [hsubAverageToFun, hsubAverageGrad] at hPoincare
    exact hPoincare
  have hgradientContinuous : ∀ i : Fin d, Continuous
      (fun v => velocityGradient u (t, v) i - m i) := by
    intro i
    exact (contDiff_velocityGradient_slice hu t i).continuous.sub continuous_const
  let F : PDE.Vec d -> PDE.Vec d :=
    fun v i => velocityGradient u (t, v) i - m i
  have hGradient :
      PDE.euclideanFieldELpNormOn V (ENNReal.ofReal p)
          (fun v => PDE.classicalGradient g v) <=
        ∑ i : Fin d,
          PDE.eLpNormOn V (ENNReal.ofReal p)
            (fun v => velocityGradient u (t, v) i - m i) := by
    calc
      PDE.euclideanFieldELpNormOn V (ENNReal.ofReal p)
          (fun v => PDE.classicalGradient g v) =
          PDE.euclideanFieldELpNormOn V (ENNReal.ofReal p) F := by
        apply PDE.euclideanFieldELpNormOn_congr_ae
        filter_upwards with v
        ext i
        exact hgradient v i
      _ = MeasureTheory.eLpNorm (fun v => PDE.vecEuclideanNorm (F v))
          (ENNReal.ofReal p) (PDE.volumeOn V) := rfl
      _ <= MeasureTheory.eLpNorm (fun v => ∑ i : Fin d, |F v i|)
          (ENNReal.ofReal p) (PDE.volumeOn V) := by
        apply MeasureTheory.eLpNorm_mono_ae
          (PDE.continuous_vecEuclideanNorm.comp
            (continuous_pi fun i => hgradientContinuous i)).aestronglyMeasurable
        filter_upwards with v
        have hsumNonneg : 0 <= ∑ i : Fin d, |F v i| :=
          Finset.sum_nonneg fun i _ => abs_nonneg (F v i)
        simpa only [Function.comp_def, F, Real.norm_eq_abs,
          abs_of_nonneg (PDE.vecEuclideanNorm_nonneg (F v)),
          abs_of_nonneg hsumNonneg] using PDE.vecEuclideanNorm_le_sum_abs (F v)
      _ <= ∑ i : Fin d,
          MeasureTheory.eLpNorm (fun v => |F v i|) (ENNReal.ofReal p)
            (PDE.volumeOn V) := by
        rw [← Finset.sum_fn]
        exact MeasureTheory.eLpNorm_sum_le Fact.out
      _ = ∑ i : Fin d,
          PDE.eLpNormOn V (ENNReal.ofReal p)
            (fun v => velocityGradient u (t, v) i - m i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simpa only [F, PDE.eLpNormOn, Real.norm_eq_abs] using
          (MeasureTheory.eLpNorm_norm (μ := PDE.volumeOn V)
            (p := ENNReal.ofReal p) (fun v => velocityGradient u (t, v) i - m i)
            (hgradientContinuous i).aestronglyMeasurable)
  rw [parabolicExponent_eq_ofReal]
  simpa only [V, V0, m, a, p,
    velocityCube_zero_one_eq_axisCube_neg_one_two d] using
    hPoincare'.trans (mul_le_mul_right hGradient _)

private theorem velocitySlice_sub_gradientMeanAffine_eLpNorm_le_hessian_sum
    (d : Nat) (u : TimeVelocity d -> Real)
    (hu : ContDiff Real 2 u) (t : Real) :
    PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1)
        (parabolicExponent d)
        (fun v => u (t, v) -
          (PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1)
              (fun w => u (t, w)) +
            ∑ i : Fin d,
              PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1)
                (fun w => velocityGradient u (t, w) i) * v i)) <=
      (ENNReal.ofReal (((2 : Real)^d) * (Real.sqrt d * 2)))^2 *
        ∑ i : Fin d, ∑ j : Fin d,
          PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1)
            (parabolicExponent d)
            (fun v => velocityHessian u (t, v) i j) := by
  let K : ENNReal := ENNReal.ofReal (((2 : Real)^d) * (Real.sqrt d * 2))
  have hsum :
      ∑ i : Fin d,
        PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1)
          (parabolicExponent d)
          (fun v => velocityGradient u (t, v) i -
            PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1)
              (fun w => velocityGradient u (t, w) i)) <=
        ∑ i : Fin d, K * ∑ j : Fin d,
          PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1)
            (parabolicExponent d)
            (fun v => velocityHessian u (t, v) i j) := by
    apply Finset.sum_le_sum
    intro i _
    simpa only [K] using
      velocityGradient_slice_subAverage_eLpNorm_le_hessian_sum d u hu t i
  calc
    PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1)
        (parabolicExponent d)
        (fun v => u (t, v) -
          (PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1)
              (fun w => u (t, w)) +
            ∑ i : Fin d,
              PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1)
                (fun w => velocityGradient u (t, w) i) * v i)) <=
        K * ∑ i : Fin d,
          PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1)
            (parabolicExponent d)
            (fun v => velocityGradient u (t, v) i -
              PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1)
                (fun w => velocityGradient u (t, w) i)) := by
      simpa only [K] using velocitySlice_sub_gradientMeanAffine_eLpNorm_le d u hu t
    _ <= K * ∑ i : Fin d, K * ∑ j : Fin d,
        PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1)
          (parabolicExponent d)
          (fun v => velocityHessian u (t, v) i j) :=
      mul_le_mul_right hsum K
    _ = K^2 * ∑ i : Fin d, ∑ j : Fin d,
        PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1)
          (parabolicExponent d)
          (fun v => velocityHessian u (t, v) i j) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_two]
      ac_rfl
    _ = (ENNReal.ofReal (((2 : Real)^d) * (Real.sqrt d * 2)))^2 *
        ∑ i : Fin d, ∑ j : Fin d,
          PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1)
            (parabolicExponent d)
            (fun v => velocityHessian u (t, v) i j) := by rfl

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory

private theorem velocitySlice_sub_canonicalMomentAffine_eq_sub_velocityMomentProjection
    (d : Nat) (u : TimeVelocity d -> Real)
    (hu : ContDiff Real 2 u) (t : Real) :
    (fun v : PDE.Vec d =>
      u (t, v) - parabolicMorreyUnitSpatialAffineProjection u (t, v)) =
      fun v =>
        (u (t, v) -
          (PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1)
            (fun w => u (t, w)) + ∑ i : Fin d,
              PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1)
                (fun w => velocityGradient u (t, w) i) * v i)) -
        parabolicMorreyUnitVelocityAffineProjection (fun w =>
          u (t, w) - (PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1)
            (fun q => u (t, q)) + ∑ i : Fin d,
              PDE.integralAverage (velocityCube (0 : PDE.Vec d) 1)
                (fun q => velocityGradient u (t, q) i) * w i)) v := by
  let V : Set (PDE.Vec d) := velocityCube (0 : PDE.Vec d) 1
  let f : PDE.Vec d -> Real := fun v => u (t, v)
  let L : PDE.Vec d -> Real := fun v => PDE.integralAverage V f + ∑ i : Fin d,
    PDE.integralAverage V (fun w => velocityGradient u (t, w) i) * v i
  have hfContinuous : Continuous f :=
    (hu.comp (contDiff_const.prodMk contDiff_id)).continuous
  have hLContinuous : Continuous L := by
    apply continuous_const.add
    exact continuous_finset_sum Finset.univ fun i _ =>
      continuous_const.mul (continuous_apply i)
  have hclosedCompact : IsCompact (velocityClosedCube (0 : PDE.Vec d) 1) :=
    isCompact_velocityClosedCube (0 : PDE.Vec d) 1
  have hsubset : V ⊆ velocityClosedCube (0 : PDE.Vec d) 1 := by
    intro v hv
    change ∀ i : Fin d, |v i - (0 : PDE.Vec d) i| < 1 at hv
    change ∀ i : Fin d, |v i - (0 : PDE.Vec d) i| <= 1
    intro i
    exact (hv i).le
  have hf : Integrable f (volume.restrict V) :=
    (hfContinuous.continuousOn.integrableOn_compact hclosedCompact).mono_set hsubset
  have hL : Integrable L (volume.restrict V) :=
    (hLContinuous.continuousOn.integrableOn_compact hclosedCompact).mono_set hsubset
  have hfv : ∀ i : Fin d, Integrable (fun v => f v * v i) (volume.restrict V) := by
    intro i
    have hcontinuous : Continuous (fun v : PDE.Vec d => f v * v i) :=
      hfContinuous.mul (continuous_apply i)
    exact (hcontinuous.continuousOn.integrableOn_compact hclosedCompact).mono_set hsubset
  have hLv : ∀ i : Fin d, Integrable (fun v => L v * v i) (volume.restrict V) := by
    intro i
    have hcontinuous : Continuous (fun v : PDE.Vec d => L v * v i) :=
      hLContinuous.mul (continuous_apply i)
    exact (hcontinuous.continuousOn.integrableOn_compact hclosedCompact).mono_set hsubset
  have hsub : parabolicMorreyUnitVelocityAffineProjection (f - L) =
      parabolicMorreyUnitVelocityAffineProjection f -
        parabolicMorreyUnitVelocityAffineProjection L := by
    simpa only [V] using
      parabolicMorreyUnitVelocityAffineProjection_sub f L hf hL hfv hLv
  have hreproduces : parabolicMorreyUnitVelocityAffineProjection L = L := by
    simpa only [L] using parabolicMorreyUnitVelocityAffineProjection_reproduces_affine
      (PDE.integralAverage V f)
      (fun i => PDE.integralAverage V (fun w => velocityGradient u (t, w) i))
  have hslice : (fun v : PDE.Vec d => parabolicMorreyUnitSpatialAffineProjection u (t, v)) =
      parabolicMorreyUnitVelocityAffineProjection f := by
    simpa only [f] using
      parabolicMorreyUnitSpatialAffineProjection_eq_velocityAffineProjection u t
  funext v
  rw [congrFun hslice v]
  change f v - parabolicMorreyUnitVelocityAffineProjection f v =
    (f v - L v) - parabolicMorreyUnitVelocityAffineProjection (f - L) v
  rw [hsub, hreproduces]
  change f v - parabolicMorreyUnitVelocityAffineProjection f v =
    (f v - L v) - (parabolicMorreyUnitVelocityAffineProjection f v - L v)
  ring

private theorem velocitySlice_sub_canonicalMomentAffine_eLpNorm_le_hessian_sum
    (d : Nat) (u : TimeVelocity d -> Real)
    (hu : ContDiff Real 2 u) (t : Real) :
    PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1) (parabolicExponent d)
        (fun v => u (t, v) - parabolicMorreyUnitSpatialAffineProjection u (t, v)) <=
      ENNReal.ofReal (2 + 3 * (d : Real)) *
        (ENNReal.ofReal (((2 : Real)^d) * (Real.sqrt d * 2)))^2 *
          ∑ i : Fin d, ∑ j : Fin d,
            PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1) (parabolicExponent d)
              (fun v => velocityHessian u (t, v) i j) := by
  let V : Set (PDE.Vec d) := velocityCube (0 : PDE.Vec d) 1
  let R : PDE.Vec d -> Real := fun v => u (t, v) -
    (PDE.integralAverage V (fun w => u (t, w)) + ∑ i : Fin d,
      PDE.integralAverage V (fun w => velocityGradient u (t, w) i) * v i)
  have huSlice : Continuous (fun v : PDE.Vec d => u (t, v)) :=
    (hu.comp (contDiff_const.prodMk contDiff_id)).continuous
  have hLContinuous : Continuous (fun v : PDE.Vec d =>
      PDE.integralAverage V (fun w => u (t, w)) + ∑ i : Fin d,
        PDE.integralAverage V (fun w => velocityGradient u (t, w) i) * v i) := by
    apply continuous_const.add
    exact continuous_finset_sum Finset.univ fun i _ =>
      continuous_const.mul (continuous_apply i)
  have hRMeasurable : AEStronglyMeasurable R (volume.restrict V) := by
    simpa only [R, Pi.sub_def] using
      (huSlice.sub hLContinuous).aestronglyMeasurable
  have hProjectionContinuous :
      Continuous (parabolicMorreyUnitVelocityAffineProjection R) := by
    unfold parabolicMorreyUnitVelocityAffineProjection
    apply continuous_const.add
    exact continuous_finset_sum Finset.univ fun i _ =>
      continuous_const.mul (continuous_apply i)
  have hProjectionMeasurable : AEStronglyMeasurable
      (parabolicMorreyUnitVelocityAffineProjection R) (volume.restrict V) :=
    hProjectionContinuous.aestronglyMeasurable
  have hp : (1 : ENNReal) <= parabolicExponent d := by
    simpa only [parabolicExponent] using
      (le_add_of_nonneg_left (show (0 : ENNReal) <= d from bot_le))
  have htriangle : PDE.eLpNormOn V (parabolicExponent d)
      (R - parabolicMorreyUnitVelocityAffineProjection R) <=
      PDE.eLpNormOn V (parabolicExponent d) R + PDE.eLpNormOn V (parabolicExponent d)
        (parabolicMorreyUnitVelocityAffineProjection R) := by
    simpa only [PDE.eLpNormOn] using
      MeasureTheory.eLpNorm_sub_le hp
  have hprojection : PDE.eLpNormOn V (parabolicExponent d)
      (parabolicMorreyUnitVelocityAffineProjection R) <=
      ENNReal.ofReal (1 + 3 * (d : Real)) * PDE.eLpNormOn V (parabolicExponent d) R := by
    simpa only [V] using
      eLpNormOn_parabolicMorreyUnitVelocityAffineProjection_le R hRMeasurable
  have hfactor : 1 + ENNReal.ofReal (1 + 3 * (d : Real)) =
      ENNReal.ofReal (2 + 3 * (d : Real)) := by
    rw [ENNReal.ofReal_add (by norm_num) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity)]
    norm_num
    rw [show (2 : ENNReal) = 1 + 1 by norm_num]
    ac_rfl
  have hS3 := velocitySlice_sub_gradientMeanAffine_eLpNorm_le_hessian_sum d u hu t
  rw [velocitySlice_sub_canonicalMomentAffine_eq_sub_velocityMomentProjection d u hu t]
  change PDE.eLpNormOn V (parabolicExponent d)
      (R - parabolicMorreyUnitVelocityAffineProjection R) <= _
  calc
    PDE.eLpNormOn V (parabolicExponent d)
        (R - parabolicMorreyUnitVelocityAffineProjection R) <=
        PDE.eLpNormOn V (parabolicExponent d) R + PDE.eLpNormOn V (parabolicExponent d)
          (parabolicMorreyUnitVelocityAffineProjection R) := htriangle
    _ <= PDE.eLpNormOn V (parabolicExponent d) R +
        ENNReal.ofReal (1 + 3 * (d : Real)) * PDE.eLpNormOn V (parabolicExponent d) R :=
      add_le_add_right hprojection _
    _ = ENNReal.ofReal (2 + 3 * (d : Real)) * PDE.eLpNormOn V (parabolicExponent d) R := by
      rw [← hfactor, add_mul, one_mul]
    _ <= ENNReal.ofReal (2 + 3 * (d : Real)) *
        ((ENNReal.ofReal (((2 : Real)^d) * (Real.sqrt d * 2)))^2 *
          ∑ i : Fin d, ∑ j : Fin d, PDE.eLpNormOn V (parabolicExponent d)
            (fun v => velocityHessian u (t, v) i j)) := by
      exact mul_le_mul_right (by simpa only [R, V] using hS3) _
    _ = ENNReal.ofReal (2 + 3 * (d : Real)) *
        (ENNReal.ofReal (((2 : Real)^d) * (Real.sqrt d * 2)))^2 *
          ∑ i : Fin d, ∑ j : Fin d,
            PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1) (parabolicExponent d)
              (fun v => velocityHessian u (t, v) i j) := by
      simp only [V]
      ac_rfl

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory

private theorem velocityHessian_continuous_for_spatial_global
    {d : Nat} {u : TimeVelocity d -> Real} {i j : Fin d}
    (hu : ContDiff Real 2 u) :
    Continuous (fun z => velocityHessian u z i j) := by
  unfold velocityHessian
  have hfirst : ContDiff Real 1 (fderiv Real u) :=
    hu.fderiv_right (m := 1) (by norm_num)
  simpa using
    (hfirst.continuous_fderiv (by norm_num)).clm_apply continuous_const |>.clm_apply
      continuous_const

private theorem aemeasurable_spatialAffine_residual
    {d : Nat} {u : TimeVelocity d -> Real}
    (hu : ContDiff Real 2 u) :
    AEMeasurable
      (fun z => u z - parabolicMorreyUnitSpatialAffineProjection u z)
      (volume.restrict (parabolicMorreyUnitBox d)) := by
  let V : Set (PDE.Vec d) := velocityCube (0 : PDE.Vec d) 1
  let ν : Measure (PDE.Vec d) := volume.restrict V
  have huStrong : StronglyMeasurable
      (Function.uncurry fun t : Real => fun v : PDE.Vec d => u (t, v)) := by
    change StronglyMeasurable u
    exact hu.continuous.stronglyMeasurable
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
      exact (hu.continuous.mul ((continuous_apply i).comp continuous_snd)).stronglyMeasurable
    unfold parabolicMorreyUnitVelocityCoeffAt
    apply stronglyMeasurable_const.mul
    simpa only [ν, V] using (huCoordinate.integral_prod_right (ν := ν))
  have hProjection : StronglyMeasurable (parabolicMorreyUnitSpatialAffineProjection u) := by
    unfold parabolicMorreyUnitSpatialAffineProjection
    apply (hAverage.comp_measurable measurable_fst).add
    rw [← Finset.sum_fn]
    refine Finset.stronglyMeasurable_sum Finset.univ fun i _ => ?_
    exact ((hCoeff i).comp_measurable measurable_fst).mul
      (((continuous_apply i).comp continuous_snd).stronglyMeasurable)
  exact (hu.continuous.stronglyMeasurable.sub hProjection).aestronglyMeasurable.aemeasurable

private theorem spatialAffinePoincareGlobalConst_pos (d : Nat) (hd : 1 <= d) :
    0 < (2 + 3 * (d : Real)) * (((2 : Real)^d) * (Real.sqrt d * 2))^2 := by
  have hdpos : 0 < (d : Real) := by
    exact_mod_cast hd
  have hsqrt : 0 < Real.sqrt (d : Real) := Real.sqrt_pos.2 hdpos
  positivity

private theorem parabolicMorreyUnitSpatialAffinePoincareELp
    (d : Nat) (u : TimeVelocity d -> Real) (hu : ContDiff Real 2 u) :
    parabolicELpNormOn d
        (fun z => u z - parabolicMorreyUnitSpatialAffineProjection u z)
        (parabolicMorreyUnitBox d) <=
      ENNReal.ofReal
          ((2 + 3 * (d : Real)) *
            (((2 : Real)^d) * (Real.sqrt d * 2))^2) *
        ∑ i : Fin d, ∑ j : Fin d,
          parabolicELpNormOn d
            (fun z => velocityHessian u z i j)
            (parabolicMorreyUnitBox d) := by
  let I : Set Real := Set.Ioo (0 : Real) 1
  let V : Set (PDE.Vec d) := velocityCube (0 : PDE.Vec d) 1
  let μ : Measure Real := volume.restrict I
  let p : ENNReal := parabolicExponent d
  let K : ENNReal := ENNReal.ofReal (((2 : Real)^d) * (Real.sqrt d * 2))
  let B : ENNReal := ENNReal.ofReal (2 + 3 * (d : Real)) * K ^ 2
  let R : TimeVelocity d -> Real := fun z =>
    u z - parabolicMorreyUnitSpatialAffineProjection u z
  let q : Fin d -> Fin d -> Real -> ENNReal := fun i j t =>
    PDE.eLpNormOn V p (fun v => velocityHessian u (t, v) i j)
  have hp : (1 : ENNReal) <= p := by
    simpa only [p, parabolicExponent] using
      (le_add_of_nonneg_left (show (0 : ENNReal) <= d from bot_le))
  have hRAE : AEMeasurable R (volume.restrict (parabolicMorreyUnitBox d)) := by
    simpa only [R] using aemeasurable_spatialAffine_residual hu
  have hHAE : ∀ i j : Fin d,
      AEMeasurable (fun z => velocityHessian u z i j)
        (volume.restrict (parabolicMorreyUnitBox d)) := by
    intro i j
    exact (velocityHessian_continuous_for_spatial_global hu).aestronglyMeasurable.aemeasurable
  have hqAE : ∀ i j : Fin d, AEMeasurable (q i j) μ := by
    intro i j
    simpa only [q, μ, I, V, p] using
      aemeasurable_parabolicMorreyUnitVelocitySlice_eLpNorm
        (fun z => velocityHessian u z i j) (hHAE i j)
  have hqASM : ∀ i j : Fin d, AEStronglyMeasurable (q i j) μ := by
    intro i j
    exact (hqAE i j).aestronglyMeasurable
  have hsumASM : AEStronglyMeasurable
      (fun t => ∑ i : Fin d, ∑ j : Fin d, q i j t) μ := by
    rw [← Finset.sum_fn]
    refine Finset.aestronglyMeasurable_sum Finset.univ fun i _ => ?_
    rw [← Finset.sum_fn]
    exact Finset.aestronglyMeasurable_sum Finset.univ fun j _ => hqASM i j
  have hslice : ∀ t : Real,
      PDE.eLpNormOn V p (fun v => R (t, v)) <=
        B * ∑ i : Fin d, ∑ j : Fin d, q i j t := by
    intro t
    simpa only [R, V, p, B, K, q] using
      velocitySlice_sub_canonicalMomentAffine_eLpNorm_le_hessian_sum d u hu t
  have houter : eLpNorm (fun t => PDE.eLpNormOn V p (fun v => R (t, v))) p μ <=
      B * eLpNorm (fun t => ∑ i : Fin d, ∑ j : Fin d, q i j t) p μ := by
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' p
      (by simpa only [V, p, μ, I] using
        (aemeasurable_parabolicMorreyUnitVelocitySlice_eLpNorm R hRAE).aestronglyMeasurable) ?_
    filter_upwards with t
    simpa only [enorm_eq_self] using hslice t
  have houterSum : eLpNorm (fun t => ∑ i : Fin d, ∑ j : Fin d, q i j t) p μ <=
      ∑ i : Fin d, ∑ j : Fin d, eLpNorm (q i j) p μ := by
    calc
      eLpNorm (fun t => ∑ i : Fin d, ∑ j : Fin d, q i j t) p μ =
          eLpNorm (∑ i : Fin d, fun t => ∑ j : Fin d, q i j t) p μ := by
        rw [Finset.sum_fn]
      _ <= ∑ i : Fin d, eLpNorm (fun t => ∑ j : Fin d, q i j t) p μ := by
        exact eLpNorm_sum_le hp
      _ <= ∑ i : Fin d, ∑ j : Fin d, eLpNorm (q i j) p μ := by
        apply Finset.sum_le_sum
        intro i _
        rw [← Finset.sum_fn]
        exact eLpNorm_sum_le hp
  have hCnonneg : 0 <= 2 + 3 * (d : Real) := by positivity
  have hLnonneg : 0 <= ((2 : Real)^d) * (Real.sqrt d * 2) := by positivity
  have hCnormalize :
      ENNReal.ofReal
          ((2 + 3 * (d : Real)) * (((2 : Real)^d) * (Real.sqrt d * 2))^2) = B := by
    dsimp only [B, K]
    rw [ENNReal.ofReal_mul hCnonneg, ENNReal.ofReal_pow hLnonneg]
  calc
    parabolicELpNormOn d R (parabolicMorreyUnitBox d) =
        eLpNorm (fun t => PDE.eLpNormOn V p (fun v => R (t, v))) p μ := by
      simpa only [R, μ, I, V, p] using
        parabolicELpNormOn_parabolicMorreyUnitBox_eq_time_eLpNorm_velocitySlice R hRAE
    _ <= B * eLpNorm (fun t => ∑ i : Fin d, ∑ j : Fin d, q i j t) p μ := houter
    _ <= B * ∑ i : Fin d, ∑ j : Fin d, eLpNorm (q i j) p μ := by
      exact mul_le_mul_right houterSum B
    _ = B * ∑ i : Fin d, ∑ j : Fin d,
        parabolicELpNormOn d
          (fun z => velocityHessian u z i j)
          (parabolicMorreyUnitBox d) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      symm
      simpa only [q, μ, I, V, p] using
        parabolicELpNormOn_parabolicMorreyUnitBox_eq_time_eLpNorm_velocitySlice
          (fun z => velocityHessian u z i j) (hHAE i j)
    _ = ENNReal.ofReal
          ((2 + 3 * (d : Real)) *
            (((2 : Real)^d) * (Real.sqrt d * 2))^2) *
        ∑ i : Fin d, ∑ j : Fin d,
          parabolicELpNormOn d
            (fun z => velocityHessian u z i j)
            (parabolicMorreyUnitBox d) := by
      rw [hCnormalize]

/-- Smooth spatial second-order Poincare inequality on the fixed unit
parabolic box, modulo the per-time canonical velocity-affine moment projection. -/
theorem exists_parabolicMorreyUnitSpatialAffinePoincareELpConst (d : Nat)
    (hd : 1 <= d) :
    ∃ C : Real, 0 < C ∧
      ∀ u : TimeVelocity d -> Real,
        ContDiff Real 2 u ->
        parabolicELpNormOn d
            (fun z => u z - parabolicMorreyUnitSpatialAffineProjection u z)
            (parabolicMorreyUnitBox d) <=
          ENNReal.ofReal C *
            ∑ i : Fin d, ∑ j : Fin d,
              parabolicELpNormOn d
                (fun z => velocityHessian u z i j)
                (parabolicMorreyUnitBox d) := by
  let C : Real :=
    (2 + 3 * (d : Real)) * (((2 : Real)^d) * (Real.sqrt d * 2))^2
  refine ⟨C, ?_, ?_⟩
  · simpa only [C] using spatialAffinePoincareGlobalConst_pos d hd
  · intro u hu
    simpa only [C] using parabolicMorreyUnitSpatialAffinePoincareELp d u hu

/-- Real-valued corollary of the smooth spatial second-order Poincare estimate
on the fixed unit parabolic box. -/
theorem exists_parabolicMorreyUnitSpatialAffinePoincareConst (d : Nat)
    (hd : 1 <= d) :
    ∃ C : Real, 0 < C ∧
      ∀ u : TimeVelocity d -> Real,
        ContDiff Real 2 u ->
        parabolicLpNormOn d
            (fun z => u z - parabolicMorreyUnitSpatialAffineProjection u z)
            (parabolicMorreyUnitBox d) <=
          C *
            ∑ i : Fin d, ∑ j : Fin d,
              parabolicLpNormOn d
                (fun z => velocityHessian u z i j)
                (parabolicMorreyUnitBox d) := by
  let C : Real :=
    (2 + 3 * (d : Real)) * (((2 : Real)^d) * (Real.sqrt d * 2))^2
  refine ⟨C, ?_, ?_⟩
  · simpa only [C] using spatialAffinePoincareGlobalConst_pos d hd
  · intro u hu
    let R : TimeVelocity d -> Real := fun z =>
      u z - parabolicMorreyUnitSpatialAffineProjection u z
    let H : Fin d -> Fin d -> TimeVelocity d -> Real := fun i j z =>
      velocityHessian u z i j
    have hENN : parabolicELpNormOn d R (parabolicMorreyUnitBox d) <=
        ENNReal.ofReal C * ∑ i : Fin d, ∑ j : Fin d,
          parabolicELpNormOn d (H i j) (parabolicMorreyUnitBox d) := by
      simpa only [C, R, H] using parabolicMorreyUnitSpatialAffinePoincareELp d u hu
    have hHmem : ∀ i j : Fin d,
        MemLp (H i j) (parabolicExponent d)
          (volume.restrict (parabolicMorreyUnitBox d)) := by
      intro i j
      have hContinuous : Continuous (fun z => velocityHessian u z i j) :=
        velocityHessian_continuous_for_spatial_global (i := i) (j := j) hu
      simpa only [H] using Continuous.memLp_parabolicMorreyUnitBox hContinuous
    have hHneTop : ∀ i j : Fin d,
        parabolicELpNormOn d (H i j) (parabolicMorreyUnitBox d) ≠ ⊤ := by
      intro i j
      exact (hHmem i j).eLpNorm_ne_top
    have hsumNeTop :
        (∑ i : Fin d, ∑ j : Fin d,
          parabolicELpNormOn d (H i j) (parabolicMorreyUnitBox d)) ≠ ⊤ := by
      apply ENNReal.sum_ne_top.mpr
      intro i _
      apply ENNReal.sum_ne_top.mpr
      intro j _
      exact hHneTop i j
    have hRhsNeTop :
        ENNReal.ofReal C * ∑ i : Fin d, ∑ j : Fin d,
          parabolicELpNormOn d (H i j) (parabolicMorreyUnitBox d) ≠ ⊤ := by
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsumNeTop
    have hReal := ENNReal.toReal_mono hRhsNeTop hENN
    have hCnonneg : 0 <= C := by
      exact (spatialAffinePoincareGlobalConst_pos d hd).le
    change (parabolicELpNormOn d R (parabolicMorreyUnitBox d)).toReal <=
      C * ∑ i : Fin d, ∑ j : Fin d,
        (parabolicELpNormOn d (H i j) (parabolicMorreyUnitBox d)).toReal
    calc
      (parabolicELpNormOn d R (parabolicMorreyUnitBox d)).toReal <=
          (ENNReal.ofReal C * ∑ i : Fin d, ∑ j : Fin d,
            parabolicELpNormOn d (H i j) (parabolicMorreyUnitBox d)).toReal := hReal
      _ = C * (∑ i : Fin d, ∑ j : Fin d,
          parabolicELpNormOn d (H i j) (parabolicMorreyUnitBox d)).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCnonneg]
      _ = C * ∑ i : Fin d, (∑ j : Fin d,
          parabolicELpNormOn d (H i j) (parabolicMorreyUnitBox d)).toReal := by
        congr 1
        exact ENNReal.toReal_sum fun i _ => ENNReal.sum_ne_top.mpr fun j _ => hHneTop i j
      _ = C * ∑ i : Fin d, ∑ j : Fin d,
          (parabolicELpNormOn d (H i j) (parabolicMorreyUnitBox d)).toReal := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        exact ENNReal.toReal_sum fun j _ => hHneTop i j

end HypoellipticAleksandrov.Parabolic

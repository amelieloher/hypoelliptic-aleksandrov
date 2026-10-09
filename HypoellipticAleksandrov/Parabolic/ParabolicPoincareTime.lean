module

public import HypoellipticAleksandrov.Parabolic.ParabolicPoincareSlices
public import HypoellipticAleksandrov.Parabolic.ParabolicPoincareProduct
public import HypoellipticAleksandrov.Parabolic.ParabolicPoincareVelocityMoments
public import PDEFoundation.Measure.LpPower
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Temporal derivatives of time-slice velocity projections

This module proves the temporal moment-affine Poincare estimate and its finite
real corollary from private smooth-calculus, scalar Poincare, and Fubini layers.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped BigOperators Topology

private theorem timeSlice_hasDerivAt
    {d : Nat} {u : TimeVelocity d -> Real}
    (hu : ContDiff Real 2 u) (z : TimeVelocity d) :
    HasDerivAt (fun s : Real => u (s, z.2)) (timeDerivative u z) z.1 := by
  have huDiff : Differentiable Real u := hu.differentiable (by norm_num)
  have hline : HasDerivAt (fun s : Real => (s, z.2))
      ((1, 0) : TimeVelocity d) z.1 := by
    simpa using
      ((hasDerivAt_id' (𝕜 := Real) z.1).prodMk
        (hasDerivAt_const (x := z.1) (c := z.2)))
  simpa only [timeDerivative, Function.comp_def] using
    (huDiff z).hasFDerivAt.comp_hasDerivAt z.1 hline

private theorem continuous_timeDerivative
    {d : Nat} {u : TimeVelocity d -> Real}
    (hu : ContDiff Real 2 u) : Continuous (timeDerivative u) := by
  change Continuous (fun z : TimeVelocity d => fderiv Real u z (1, 0))
  exact ((hu.contDiff_fderiv_apply (m := 0) (by norm_num)).comp
    (contDiff_id.prodMk contDiff_const)).continuous

private theorem hasDerivAt_integral_velocity_weighted
    {d : Nat} {u : TimeVelocity d -> Real}
    (hu : ContDiff Real 2 u) (w : PDE.Vec d -> Real)
    (hw : Continuous w) (t : Real) :
    HasDerivAt
      (fun s : Real =>
        ∫ v in velocityCube (0 : PDE.Vec d) 1, u (s, v) * w v)
      (∫ v in velocityCube (0 : PDE.Vec d) 1,
        timeDerivative u (t, v) * w v)
      t := by
  let V : Set (PDE.Vec d) := velocityCube (0 : PDE.Vec d) 1
  let W : Set (PDE.Vec d) := velocityClosedCube (0 : PDE.Vec d) 1
  let K : Set (TimeVelocity d) := Set.Icc (t - 1) (t + 1) ×ˢ W
  let F : Real -> PDE.Vec d -> Real := fun s v => u (s, v) * w v
  let F' : Real -> PDE.Vec d -> Real := fun s v => timeDerivative u (s, v) * w v
  have hVW : V ⊆ W := by
    intro v hv i
    exact (hv i).le
  have hFcont : ∀ s : Real, Continuous (F s) := by
    intro s
    exact (hu.continuous.comp (continuous_const.prodMk continuous_id)).mul hw
  have htimeDerivative : Continuous (timeDerivative u) :=
    continuous_timeDerivative hu
  have hF'cont : Continuous (fun z : TimeVelocity d =>
      timeDerivative u z * w z.2) :=
    htimeDerivative.mul (hw.comp continuous_snd)
  have hF'contSlice : ∀ s : Real, Continuous (F' s) := by
    intro s
    exact hF'cont.comp (continuous_const.prodMk continuous_id)
  have hKcompact : IsCompact K :=
    isCompact_Icc.prod (isCompact_velocityClosedCube (0 : PDE.Vec d) 1)
  obtain ⟨C, hC⟩ :=
    hKcompact.exists_bound_of_continuousOn hF'cont.continuousOn
  have hF_meas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (F s) (volume.restrict V) :=
    Filter.Eventually.of_forall fun s => (hFcont s).aestronglyMeasurable
  have hF_int : Integrable (F t) (volume.restrict V) := by
    have hF_int_closed : IntegrableOn (F t) W volume :=
      (hFcont t).continuousOn.integrableOn_compact
        (isCompact_velocityClosedCube (0 : PDE.Vec d) 1)
    simpa only [IntegrableOn] using hF_int_closed.mono_set hVW
  have hF'_meas : AEStronglyMeasurable (F' t) (volume.restrict V) :=
    (hF'contSlice t).aestronglyMeasurable
  have h_bound : ∀ᵐ v ∂volume.restrict V,
      ∀ s ∈ Metric.ball t 1, ‖F' s v‖ ≤ (fun _ : PDE.Vec d => C) v := by
    filter_upwards [ae_restrict_mem (measurableSet_velocityCube (0 : PDE.Vec d) 1)]
      with v hv
    intro s hs
    apply hC (s, v)
    constructor
    · rw [Metric.mem_ball, Real.dist_eq] at hs
      rcases abs_lt.mp hs with ⟨hleft, hright⟩
      constructor <;> linarith
    · exact hVW hv
  have hbound_int : Integrable (fun _ : PDE.Vec d => C) (volume.restrict V) := by
    have hbound_int_closed : IntegrableOn (fun _ : PDE.Vec d => C) W volume :=
      continuousOn_const.integrableOn_compact
        (isCompact_velocityClosedCube (0 : PDE.Vec d) 1)
    simpa only [IntegrableOn] using hbound_int_closed.mono_set hVW
  have hdiff : ∀ᵐ v ∂volume.restrict V,
      ∀ s ∈ Metric.ball t 1, HasDerivAt (F · v) (F' s v) s :=
    Filter.Eventually.of_forall fun v s _ => by
      simpa only [F, F'] using (timeSlice_hasDerivAt hu (s, v)).mul_const (w v)
  simpa only [F, F'] using
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict V)
      (x₀ := t) (s := Metric.ball t 1)
      (F := F)
      (F' := F')
      (bound := fun _ : PDE.Vec d => C)
      (Metric.ball_mem_nhds t zero_lt_one) hF_meas hF_int hF'_meas h_bound hbound_int hdiff).2

private theorem hasDerivAt_parabolicMorreyUnitVelocityAverage
    {d : Nat} {u : TimeVelocity d -> Real}
    (hu : ContDiff Real 2 u) (t : Real) :
    HasDerivAt (parabolicMorreyUnitVelocityAverage u)
      (parabolicMorreyUnitVelocityAverage (timeDerivative u) t) t := by
  change HasDerivAt
    (fun s => ((volume (velocityCube (0 : PDE.Vec d) 1)).toReal)⁻¹ *
      ∫ v in velocityCube 0 1, u (s, v)) _ t
  simpa only [Function.comp_def, Pi.mul_def, parabolicMorreyUnitVelocityAverage, mul_one] using
    (hasDerivAt_integral_velocity_weighted hu (fun _ : PDE.Vec d => 1)
      continuous_const t).const_mul
      ((volume (velocityCube (0 : PDE.Vec d) 1)).toReal)⁻¹

private theorem hasDerivAt_parabolicMorreyUnitVelocityCoeffAt
    {d : Nat} {u : TimeVelocity d -> Real}
    (hu : ContDiff Real 2 u) (i : Fin d) (t : Real) :
    HasDerivAt (fun s : Real => parabolicMorreyUnitVelocityCoeffAt u s i)
      (parabolicMorreyUnitVelocityCoeffAt (timeDerivative u) t i) t := by
  simpa only [Function.comp_def, Pi.mul_def, parabolicMorreyUnitVelocityCoeffAt] using
    (hasDerivAt_integral_velocity_weighted hu (fun v : PDE.Vec d => v i)
      (continuous_apply i) t).const_mul
      (3 * ((volume (velocityCube (0 : PDE.Vec d) 1)).toReal)⁻¹)

private theorem hasDerivAt_parabolicMorreyUnitSpatialAffineProjection
    {d : Nat} {u : TimeVelocity d -> Real}
    (hu : ContDiff Real 2 u) (v : PDE.Vec d) (t : Real) :
    HasDerivAt
      (fun s : Real => parabolicMorreyUnitSpatialAffineProjection u (s, v))
      (parabolicMorreyUnitSpatialAffineProjection (timeDerivative u) (t, v))
      t := by
  have haverage : HasDerivAt
      (fun s : Real => parabolicMorreyUnitVelocityAverage u s)
      (parabolicMorreyUnitVelocityAverage (timeDerivative u) t) t :=
    hasDerivAt_parabolicMorreyUnitVelocityAverage hu t
  have hsum : HasDerivAt
      (∑ i : Fin d, fun s : Real => parabolicMorreyUnitVelocityCoeffAt u s i * v i)
      (∑ i : Fin d,
        parabolicMorreyUnitVelocityCoeffAt (timeDerivative u) t i * v i) t :=
    HasDerivAt.sum (u := (Finset.univ : Finset (Fin d))) fun i _ =>
      (hasDerivAt_parabolicMorreyUnitVelocityCoeffAt hu i t).mul_const (v i)
  have hfun :
      (fun s : Real => parabolicMorreyUnitVelocityAverage u s +
        ∑ i : Fin d, parabolicMorreyUnitVelocityCoeffAt u s i * v i) =
        (fun s : Real => parabolicMorreyUnitVelocityAverage u s) +
          ∑ i : Fin d, fun s : Real => parabolicMorreyUnitVelocityCoeffAt u s i * v i := by
    funext s
    simp only [Pi.add_apply, Finset.sum_apply]
  change HasDerivAt
    (fun s : Real => parabolicMorreyUnitVelocityAverage u s +
      ∑ i : Fin d, parabolicMorreyUnitVelocityCoeffAt u s i * v i)
    (parabolicMorreyUnitVelocityAverage (timeDerivative u) t +
      ∑ i : Fin d, parabolicMorreyUnitVelocityCoeffAt (timeDerivative u) t i * v i) t
  rw [hfun]
  exact haverage.add hsum

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory

private theorem unitTime_meanPoincare_rpow
    {p : ℝ} {f f' : ℝ → ℝ}
    (hp : 1 ≤ p) (hf' : Continuous f')
    (hderiv : ∀ t : ℝ, HasDerivAt f (f' t) t) :
    ∫ t in Set.Ioo (0 : ℝ) 1,
        |f t - ∫ s in Set.Ioo (0 : ℝ) 1, f s| ^ p ≤
      ∫ t in Set.Ioo (0 : ℝ) 1, |f' t| ^ p := by
  classical
  let J : Set ℝ := Set.Icc 0 1
  let A : ℝ := ∫ s in J, f s
  let B : ℝ := ∫ s in J, |f' s|
  have hp0 : 0 ≤ p := by linarith
  have hf : Continuous f :=
    continuous_iff_continuousAt.mpr fun t => (hderiv t).continuousAt
  have hJmeas : MeasurableSet J := by
    exact measurableSet_Icc
  have hvol : volume.real J = 1 := by
    change volume.real (Set.Icc 0 1) = 1
    rw [Real.volume_real_Icc_of_le]
    norm_num
    norm_num
  have hvol_top : volume J ≠ ⊤ := by
    simpa only [J] using (measure_Icc_lt_top : volume (Set.Icc (0 : ℝ) 1) < ⊤).ne
  have hvol_ne : volume J ≠ 0 := by
    simp only [J, Real.volume_Icc]
    norm_num
  have hf_int : IntegrableOn f J volume := by
    simpa only [J] using hf.integrableOn_Icc
  have hfp_abs_int : IntegrableOn (fun s : ℝ => |f' s|) J volume := by
    simpa only [J] using hf'.abs.integrableOn_Icc
  have hfp_pow_cont : Continuous (fun s : ℝ => |f' s| ^ p) :=
    (Real.continuous_rpow_const hp0).comp hf'.abs
  have hfp_pow_int : IntegrableOn (fun s : ℝ => |f' s| ^ p) J volume := by
    simpa only [J] using hfp_pow_cont.integrableOn_Icc
  have hosc : ∀ ⦃t s : ℝ⦄, t ∈ J → s ∈ J → |f t - f s| ≤ B := by
    intro t s ht hs
    have hft : ∫ x in s..t, f' x = f t - f s :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _hx => hderiv x) (hf'.intervalIntegrable s t)
    rw [← hft]
    calc
      |∫ x in s..t, f' x| = ‖∫ x in s..t, f' x‖ := by
        exact (Real.norm_eq_abs _).symm
      _ ≤ ∫ x in Set.uIoc s t, ‖f' x‖ :=
        intervalIntegral.norm_integral_le_integral_norm_uIoc
      _ ≤ ∫ x in J, |f' x| := by
        apply MeasureTheory.setIntegral_mono_set hfp_abs_int
          (Filter.Eventually.of_forall fun x => abs_nonneg (f' x))
        exact (Set.uIoc_subset_uIcc.trans (Set.uIcc_subset_Icc hs ht)).eventuallyLE
      _ = B := rfl
  have hmean : ∀ t : ℝ, f t - A = ∫ s in J, (f t - f s) := by
    intro t
    have hconst : IntegrableOn (fun _ : ℝ => f t) J volume :=
      integrableOn_const hvol_top
    calc
      f t - A = (∫ s in J, f t) - ∫ s in J, f s := by
        rw [MeasureTheory.setIntegral_const, smul_eq_mul, hvol]
        simp only [one_mul, A]
      _ = ∫ s in J, (f t - f s) :=
        (MeasureTheory.integral_sub hconst hf_int).symm
  have hpoint : ∀ ⦃t : ℝ⦄, t ∈ J → |f t - A| ≤ B := by
    intro t ht
    rw [hmean]
    calc
      |∫ s in J, (f t - f s)| = ‖∫ s in J, (f t - f s)‖ := by
        exact (Real.norm_eq_abs _).symm
      _ ≤ ∫ s in J, ‖f t - f s‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ s in J, B := by
        refine MeasureTheory.setIntegral_mono_on
          (by simpa only [J, Function.comp_def, Pi.sub_def, Real.norm_eq_abs] using
            (continuous_const.sub hf).abs.integrableOn_Icc)
          (integrableOn_const hvol_top)
          hJmeas fun s hs => ?_
        simpa only [Real.norm_eq_abs] using hosc (t := t) (s := s) ht hs
      _ = B := by
        rw [MeasureTheory.setIntegral_const, smul_eq_mul, hvol]
        simp only [one_mul]
  have hpoint_pow : ∀ ⦃t : ℝ⦄, t ∈ J → |f t - A| ^ p ≤ B ^ p := by
    intro t ht
    exact Real.rpow_le_rpow (abs_nonneg _) (hpoint ht) hp0
  have hjensen : B ^ p ≤ ∫ s in J, |f' s| ^ p := by
    have h := (convexOn_rpow hp).map_set_average_le
      (Real.continuous_rpow_const hp0).continuousOn isClosed_Ici hvol_ne hvol_top
      (by
        filter_upwards [ae_restrict_mem hJmeas] with x hx
        exact abs_nonneg (f' x)) hfp_abs_int
      (by simpa only [Function.comp_def] using hfp_pow_int)
    simpa only [MeasureTheory.setAverage_eq, hvol, inv_one, one_smul, B] using h
  have hleft_cont : Continuous (fun t : ℝ => |f t - A| ^ p) :=
    (Real.continuous_rpow_const hp0).comp ((hf.sub continuous_const).abs)
  have hleft_int : IntegrableOn (fun t : ℝ => |f t - A| ^ p) J volume := by
    simpa only [J] using hleft_cont.integrableOn_Icc
  have hclosed :
      ∫ t in J, |f t - A| ^ p ≤ ∫ t in J, |f' t| ^ p := by
    calc
      ∫ t in J, |f t - A| ^ p ≤ ∫ t in J, B ^ p := by
        refine MeasureTheory.setIntegral_mono_on hleft_int (integrableOn_const hvol_top)
          hJmeas fun t ht => hpoint_pow ht
      _ = B ^ p := by
        rw [MeasureTheory.setIntegral_const, smul_eq_mul, hvol]
        simp only [one_mul]
      _ ≤ ∫ t in J, |f' t| ^ p := hjensen
  have hmean_endpoints :
      ∫ s in J, f s = ∫ s in Set.Ioo (0 : ℝ) 1, f s := by
    simpa only [J] using
      (MeasureTheory.integral_Icc_eq_integral_Ioo (μ := volume) (f := f) (x := (0 : ℝ)) (y := 1))
  calc
    ∫ t in Set.Ioo (0 : ℝ) 1,
        |f t - ∫ s in Set.Ioo (0 : ℝ) 1, f s| ^ p =
        ∫ t in J, |f t - A| ^ p := by
      rw [← hmean_endpoints]
      simpa only [A] using
        (MeasureTheory.integral_Icc_eq_integral_Ioo (μ := volume)
          (f := fun t : ℝ => |f t - ∫ s in J, f s| ^ p) (x := (0 : ℝ)) (y := 1)).symm
    _ ≤ ∫ t in J, |f' t| ^ p := hclosed
    _ = ∫ t in Set.Ioo (0 : ℝ) 1, |f' t| ^ p := by
      simpa only [J] using
        (MeasureTheory.integral_Icc_eq_integral_Ioo (μ := volume)
          (f := fun t : ℝ => |f' t| ^ p) (x := (0 : ℝ)) (y := 1))

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory

private theorem continuous_parabolicMorreyUnitVelocityAverage
    {d : Nat} {u : TimeVelocity d -> Real}
    (hu : ContDiff Real 2 u) :
    Continuous (parabolicMorreyUnitVelocityAverage u) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (hasDerivAt_parabolicMorreyUnitVelocityAverage hu t).continuousAt

private theorem continuous_parabolicMorreyUnitVelocityCoeffAt
    {d : Nat} {u : TimeVelocity d -> Real}
    (hu : ContDiff Real 2 u) (i : Fin d) :
    Continuous (fun t => parabolicMorreyUnitVelocityCoeffAt u t i) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (hasDerivAt_parabolicMorreyUnitVelocityCoeffAt hu i t).continuousAt

private theorem continuous_parabolicMorreyUnitSpatialAffineProjection
    {d : Nat} {u : TimeVelocity d -> Real}
    (hu : ContDiff Real 2 u) :
    Continuous (parabolicMorreyUnitSpatialAffineProjection u) := by
  unfold parabolicMorreyUnitSpatialAffineProjection
  apply Continuous.add
  · exact (continuous_parabolicMorreyUnitVelocityAverage hu).comp continuous_fst
  · apply continuous_finset_sum
    intro i _
    exact ((continuous_parabolicMorreyUnitVelocityCoeffAt hu i).comp continuous_fst).mul
      (continuous_apply i |>.comp continuous_snd)

private theorem continuous_parabolicMorreyUnitAffineProjection
    {d : Nat} (u : TimeVelocity d -> Real) :
    Continuous (parabolicMorreyUnitAffineProjection u) := by
  unfold parabolicMorreyUnitAffineProjection
  apply Continuous.add continuous_const
  apply continuous_finset_sum
  intro i _
  exact continuous_const.mul (continuous_apply i |>.comp continuous_snd)

private theorem continuous_integrable_parabolicMorreyUnitBox
    {d : Nat} {f : TimeVelocity d -> Real} (hf : Continuous f) :
    Integrable f (volume.restrict (parabolicMorreyUnitBox d)) := by
  let K : Set (TimeVelocity d) :=
    parabolicClosedBox 1 1 0 (0 : PDE.Vec d)
  have hKcompact : IsCompact K :=
    isCompact_parabolicClosedBox 1 1 0 (0 : PDE.Vec d)
  have hsubset : parabolicMorreyUnitBox d ⊆ K := by
    rintro ⟨t, v⟩ hz
    change (t, v) ∈ parabolicBox 1 1 0 0 at hz
    change (t, v) ∈ parabolicClosedBox 1 1 0 0
    rcases hz with ⟨⟨htLeft, htRight⟩, hv⟩
    exact ⟨⟨htLeft.le, htRight.le⟩, fun i => (hv i).le⟩
  exact (hf.continuousOn.integrableOn_compact hKcompact).mono_set hsubset

private theorem parabolicExponent_eq_ofReal (d : Nat) :
    parabolicExponent d = ENNReal.ofReal ((d : Real) + 1) := by
  rw [show ((d : Real) + 1) = ((d + 1 : Nat) : Real) by norm_num]
  simpa only [parabolicExponent, Nat.cast_add, Nat.cast_one] using
    (ENNReal.ofReal_natCast (d + 1)).symm

private theorem parabolicMorreyUnitBox_volume_toReal_eq_velocityCube (d : Nat) :
    (volume (parabolicMorreyUnitBox d)).toReal =
      (volume (velocityCube (0 : PDE.Vec d) 1)).toReal := by
  rw [volume_parabolicMorreyUnitBox_toReal,
    volume_velocityCube_toReal (v₀ := (0 : PDE.Vec d)) (by norm_num : (0 : Real) ≤ 1)]
  simp only [mul_one]

private theorem integrableOn_parabolicMorreyUnitBox_as_prod
    {d : Nat} {f : TimeVelocity d -> Real}
    (hf : Integrable f (volume.restrict (parabolicMorreyUnitBox d))) :
    IntegrableOn f
      (Set.Ioo (0 : Real) 1 ×ˢ velocityCube (0 : PDE.Vec d) 1)
      ((volume : Measure Real).prod (volume : Measure (PDE.Vec d))) := by
  change Integrable f (((volume : Measure Real).prod (volume : Measure (PDE.Vec d))).restrict
    (Set.Ioo (0 : Real) 1 ×ˢ velocityCube (0 : PDE.Vec d) 1))
  rw [← Measure.prod_restrict, ← parabolicMorreyUnitBox_restrict_volume_eq_prod]
  exact hf

private theorem parabolicMorreyUnitAverage_eq_integral_velocityAverage
    {d : Nat} {u : TimeVelocity d -> Real}
    (hu : Continuous u) :
    parabolicMorreyUnitAverage u =
      ∫ t in Set.Ioo (0 : Real) 1, parabolicMorreyUnitVelocityAverage u t := by
  let I : Set Real := Set.Ioo 0 1
  let V : Set (PDE.Vec d) := velocityCube (0 : PDE.Vec d) 1
  have huInt : Integrable u (volume.restrict (parabolicMorreyUnitBox d)) :=
    continuous_integrable_parabolicMorreyUnitBox hu
  have huProd : IntegrableOn u (I ×ˢ V)
      ((volume : Measure Real).prod (volume : Measure (PDE.Vec d))) := by
    simpa only [I, V] using integrableOn_parabolicMorreyUnitBox_as_prod huInt
  have hFubini : ∫ z in parabolicMorreyUnitBox d, u z =
      ∫ t in I, ∫ v in V, u (t, v) := by
    change ∫ z, u z ∂volume.restrict (parabolicMorreyUnitBox d) =
      ∫ t, ∫ v, u (t, v) ∂volume.restrict V ∂volume.restrict I
    rw [parabolicMorreyUnitBox_restrict_volume_eq_prod]
    have huProd' : Integrable u
        ((volume.restrict I).prod (volume.restrict V)) := by
      rw [Measure.prod_restrict]
      exact huProd
    simpa only [I, V] using MeasureTheory.integral_prod u huProd'
  unfold parabolicMorreyUnitAverage parabolicMorreyUnitVelocityAverage
  rw [hFubini, parabolicMorreyUnitBox_volume_toReal_eq_velocityCube]
  rw [← MeasureTheory.integral_const_mul]

private theorem parabolicMorreyUnitVelocityCoeff_eq_integral_coeffAt
    {d : Nat} {u : TimeVelocity d -> Real}
    (hu : ContDiff Real 2 u) (i : Fin d) :
    parabolicMorreyUnitVelocityCoeff u i =
      ∫ t in Set.Ioo (0 : Real) 1, parabolicMorreyUnitVelocityCoeffAt u t i := by
  unfold parabolicMorreyUnitVelocityCoeff parabolicMorreyUnitVelocityCoeffAt
  have hcont : Continuous (fun z : TimeVelocity d => u z * z.2 i) :=
    hu.continuous.mul (continuous_apply i |>.comp continuous_snd)
  have haverage := parabolicMorreyUnitAverage_eq_integral_velocityAverage hcont
  change 3 * parabolicMorreyUnitAverage (fun z => u z * z.2 i) = _
  rw [haverage]
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
  intro t _
  unfold parabolicMorreyUnitVelocityAverage
  ring

private theorem parabolicMorreyUnitAffineProjection_eq_time_mean_spatialProjection
    {d : Nat} {u : TimeVelocity d -> Real}
    (hu : ContDiff Real 2 u) (v : PDE.Vec d) :
    parabolicMorreyUnitAffineProjection u (0, v) =
      ∫ t in Set.Ioo (0 : Real) 1,
        parabolicMorreyUnitSpatialAffineProjection u (t, v) := by
  let I : Set Real := Set.Ioo 0 1
  have hAvgCont : Continuous (parabolicMorreyUnitVelocityAverage u) :=
    continuous_parabolicMorreyUnitVelocityAverage hu
  have hAvgInt : IntegrableOn (parabolicMorreyUnitVelocityAverage u) I volume := by
    exact (hAvgCont.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
  have hCoeffCont : ∀ i : Fin d,
      Continuous (fun t => parabolicMorreyUnitVelocityCoeffAt u t i) :=
    fun i => continuous_parabolicMorreyUnitVelocityCoeffAt hu i
  have hCoeffInt : ∀ i : Fin d, IntegrableOn
      (fun t => parabolicMorreyUnitVelocityCoeffAt u t i * v i) I volume := by
    intro i
    exact ((hCoeffCont i).mul continuous_const).integrableOn_Icc.mono_set
      Set.Ioo_subset_Icc_self
  have hSumInt : IntegrableOn (fun t => ∑ i : Fin d,
      parabolicMorreyUnitVelocityCoeffAt u t i * v i) I volume := by
    exact integrable_finset_sum Finset.univ fun i _ => hCoeffInt i
  unfold parabolicMorreyUnitAffineProjection parabolicMorreyUnitSpatialAffineProjection
  rw [parabolicMorreyUnitAverage_eq_integral_velocityAverage hu.continuous]
  simp_rw [parabolicMorreyUnitVelocityCoeff_eq_integral_coeffAt hu]
  rw [MeasureTheory.integral_add hAvgInt hSumInt,
    MeasureTheory.integral_finset_sum Finset.univ (fun i _ => hCoeffInt i)]
  simp_rw [MeasureTheory.integral_mul_const]
  ring

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory

private theorem continuous_integral_velocity_weighted_of_continuous
    {d : Nat} {g : TimeVelocity d -> Real} (hg : Continuous g)
    (w : PDE.Vec d -> Real) (hw : Continuous w) :
    Continuous (fun t : Real =>
      ∫ v in velocityCube (0 : PDE.Vec d) 1, g (t, v) * w v) := by
  rw [continuous_iff_continuousAt]
  intro t
  let J : Set Real := Set.Icc (t - 1) (t + 1)
  let V : Set (PDE.Vec d) := velocityCube (0 : PDE.Vec d) 1
  let W : Set (PDE.Vec d) := velocityClosedCube (0 : PDE.Vec d) 1
  let F : Real -> PDE.Vec d -> Real := fun s v => g (s, v) * w v
  have hVW : V ⊆ W := by
    intro v hv i
    exact (hv i).le
  have hFcont : Continuous (Function.uncurry F) := by
    exact hg.mul (hw.comp continuous_snd)
  have hKcompact : IsCompact (J ×ˢ W) :=
    isCompact_Icc.prod (isCompact_velocityClosedCube (0 : PDE.Vec d) 1)
  obtain ⟨C, hC⟩ := hKcompact.exists_bound_of_continuousOn hFcont.continuousOn
  have hFmeas : ∀ s ∈ J, AEStronglyMeasurable (F s) (volume.restrict V) := by
    intro s _
    exact (hFcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hbound : ∀ s ∈ J, ∀ᵐ v ∂volume.restrict V, ‖F s v‖ ≤ C := by
    intro s hs
    filter_upwards [ae_restrict_mem (measurableSet_velocityCube (0 : PDE.Vec d) 1)]
      with v hv
    exact hC (s, v) ⟨hs, hVW hv⟩
  have hCint : Integrable (fun _ : PDE.Vec d => C) (volume.restrict V) := by
    have hclosed : IntegrableOn (fun _ : PDE.Vec d => C) W volume :=
      continuousOn_const.integrableOn_compact
        (isCompact_velocityClosedCube (0 : PDE.Vec d) 1)
    simpa only [IntegrableOn] using hclosed.mono_set hVW
  have hcont : ∀ᵐ v ∂volume.restrict V, ContinuousOn (fun s => F s v) J := by
    filter_upwards [ae_restrict_mem (measurableSet_velocityCube (0 : PDE.Vec d) 1)]
      with v _
    exact (hFcont.comp (continuous_id.prodMk continuous_const)).continuousOn
  have hJ : J ∈ nhds t := by
    simpa only [J] using
      (Icc_mem_nhds (show t - 1 < t by linarith) (show t < t + 1 by linarith))
  exact (continuousOn_of_dominated hFmeas hbound hCint hcont).continuousAt hJ

private theorem continuous_parabolicMorreyUnitSpatialAffineProjection_of_continuous
    {d : Nat} {g : TimeVelocity d -> Real} (hg : Continuous g) :
    Continuous (parabolicMorreyUnitSpatialAffineProjection g) := by
  unfold parabolicMorreyUnitSpatialAffineProjection
  apply Continuous.add
  · have hInt : Continuous (fun t : Real =>
        ∫ v in velocityCube (0 : PDE.Vec d) 1, g (t, v) * 1) :=
      continuous_integral_velocity_weighted_of_continuous hg
        (fun _ : PDE.Vec d => 1)
        (continuous_const : Continuous (fun _ : PDE.Vec d => (1 : Real)))
    simpa only [Function.comp_def, Pi.mul_def, parabolicMorreyUnitVelocityAverage, mul_one] using
      ((continuous_const : Continuous (fun _ : Real =>
      ((volume (velocityCube (0 : PDE.Vec d) 1)).toReal)⁻¹)).mul hInt).comp
        (continuous_fst : Continuous (fun z : TimeVelocity d => z.1))
  · apply continuous_finset_sum
    intro i _
    have hInt : Continuous (fun t : Real =>
        ∫ v in velocityCube (0 : PDE.Vec d) 1, g (t, v) * v i) :=
      continuous_integral_velocity_weighted_of_continuous hg
        (fun v : PDE.Vec d => v i) (continuous_apply i)
    simpa only [Function.comp_def, Pi.mul_def, parabolicMorreyUnitVelocityCoeffAt] using
      (((continuous_const : Continuous (fun _ : Real =>
        3 * ((volume (velocityCube (0 : PDE.Vec d) 1)).toReal)⁻¹)).mul hInt).comp
          continuous_fst).mul (continuous_apply i |>.comp continuous_snd)

private theorem parabolicELpNormOn_spatialAffineProjection_timeDerivative_le
    (d : Nat) (u : TimeVelocity d -> Real) (hu : ContDiff Real 2 u) :
    parabolicELpNormOn d (parabolicMorreyUnitSpatialAffineProjection (timeDerivative u))
        (parabolicMorreyUnitBox d) ≤
      ENNReal.ofReal (1 + 3 * (d : Real)) *
        parabolicELpNormOn d (timeDerivative u) (parabolicMorreyUnitBox d) := by
  let I : Set Real := Set.Ioo 0 1
  let V : Set (PDE.Vec d) := velocityCube (0 : PDE.Vec d) 1
  let p : ENNReal := parabolicExponent d
  let q : Real -> ENNReal := fun t =>
    PDE.eLpNormOn V p (fun v =>
      parabolicMorreyUnitSpatialAffineProjection (timeDerivative u) (t, v))
  let r : Real -> ENNReal := fun t =>
    PDE.eLpNormOn V p (fun v => timeDerivative u (t, v))
  have htime : Continuous (timeDerivative u) := continuous_timeDerivative hu
  have hTae : AEMeasurable (timeDerivative u)
      (volume.restrict (parabolicMorreyUnitBox d)) := htime.aemeasurable
  have hrAE : AEMeasurable r (volume.restrict I) := by
    simpa only [r, I, V, p] using
      aemeasurable_parabolicMorreyUnitVelocitySlice_eLpNorm (timeDerivative u) hTae
  have hslicebound (t : Real) : q t ≤ ENNReal.ofReal (1 + 3 * (d : Real)) * r t := by
    simpa only [q, r, p, V,
      parabolicMorreyUnitSpatialAffineProjection_eq_velocityAffineProjection] using
      eLpNormOn_parabolicMorreyUnitVelocityAffineProjection_le
        (fun v => timeDerivative u (t, v))
        (htime.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hScont : Continuous (parabolicMorreyUnitSpatialAffineProjection (timeDerivative u)) :=
    continuous_parabolicMorreyUnitSpatialAffineProjection_of_continuous htime
  have hsliceNorm : eLpNorm q p (volume.restrict I) ≤
      ENNReal.ofReal (1 + 3 * (d : Real)) * eLpNorm r p (volume.restrict I) := by
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' p
      (by simpa only [q, I, V, p] using
        (aemeasurable_parabolicMorreyUnitVelocitySlice_eLpNorm _
          hScont.aemeasurable).aestronglyMeasurable) ?_
    filter_upwards with t
    simpa only [enorm_eq_self] using hslicebound t

  calc
    parabolicELpNormOn d (parabolicMorreyUnitSpatialAffineProjection (timeDerivative u))
        (parabolicMorreyUnitBox d) = eLpNorm q p (volume.restrict I) := by
      simpa only [q, p, V, I] using
        parabolicELpNormOn_parabolicMorreyUnitBox_eq_time_eLpNorm_velocitySlice
          (parabolicMorreyUnitSpatialAffineProjection (timeDerivative u)) hScont.aemeasurable
    _ ≤ ENNReal.ofReal (1 + 3 * (d : Real)) * eLpNorm r p (volume.restrict I) := hsliceNorm
    _ = ENNReal.ofReal (1 + 3 * (d : Real)) *
        parabolicELpNormOn d (timeDerivative u) (parabolicMorreyUnitBox d) := by
      rw [parabolicELpNormOn_parabolicMorreyUnitBox_eq_time_eLpNorm_velocitySlice
        (timeDerivative u) hTae]

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped BigOperators

private theorem temporalResidual_setIntegral_rpow_le_spatialProjection
    (d : Nat) (u : TimeVelocity d -> Real) (hu : ContDiff Real 2 u) :
    ∫ z in parabolicMorreyUnitBox d,
        |parabolicMorreyUnitSpatialAffineProjection u z -
          parabolicMorreyUnitAffineProjection u z| ^ ((d : Real) + 1) <=
      ∫ z in parabolicMorreyUnitBox d,
        |parabolicMorreyUnitSpatialAffineProjection (timeDerivative u) z| ^
          ((d : Real) + 1) := by
  let I : Set Real := Set.Ioo 0 1
  let V : Set (PDE.Vec d) := velocityCube 0 1
  let B : Set (TimeVelocity d) := parabolicMorreyUnitBox d
  let p : Real := (d : Real) + 1
  let R : TimeVelocity d -> Real := fun z =>
    parabolicMorreyUnitSpatialAffineProjection u z -
      parabolicMorreyUnitAffineProjection u z
  let S : TimeVelocity d -> Real :=
    parabolicMorreyUnitSpatialAffineProjection (timeDerivative u)
  let μ : Measure Real := volume.restrict I
  let ν : Measure (PDE.Vec d) := volume.restrict V

  have hp : 0 < p := by
    dsimp only [p]
    positivity
  have hp1 : 1 <= p := by
    dsimp only [p]
    have hd : (0 : Real) <= (d : Real) := Nat.cast_nonneg d
    linarith
  have hRcont : Continuous R :=
    (continuous_parabolicMorreyUnitSpatialAffineProjection hu).sub
      (continuous_parabolicMorreyUnitAffineProjection u)
  have hScont : Continuous S :=
    continuous_parabolicMorreyUnitSpatialAffineProjection_of_continuous
      (continuous_timeDerivative hu)
  have hRpow : Integrable (fun z => |R z| ^ p) (volume.restrict B) := by
    have hRmem : MemLp R (parabolicExponent d) (volume.restrict B) := by
      simpa only [B] using Continuous.memLp_parabolicMorreyUnitBox hRcont
    simpa [parabolicExponent_eq_ofReal, p, ENNReal.toReal_ofReal hp.le,
      Real.norm_eq_abs] using hRmem.integrable_norm_rpow
        (by simp [parabolicExponent]) (by simp [parabolicExponent])
  have hSpow : Integrable (fun z => |S z| ^ p) (volume.restrict B) := by
    have hSmem : MemLp S (parabolicExponent d) (volume.restrict B) := by
      simpa only [B] using Continuous.memLp_parabolicMorreyUnitBox hScont
    simpa [parabolicExponent_eq_ofReal, p, ENNReal.toReal_ofReal hp.le,
      Real.norm_eq_abs] using hSmem.integrable_norm_rpow
        (by simp [parabolicExponent]) (by simp [parabolicExponent])
  have hRprod : Integrable (Function.uncurry fun t : Real => fun v : PDE.Vec d =>
      |R (t, v)| ^ p) (μ.prod ν) := by
    change Integrable (Function.uncurry fun t : Real => fun v : PDE.Vec d =>
      |R (t, v)| ^ p) ((volume.restrict I).prod (volume.restrict V))
    rw [Measure.prod_restrict]
    change IntegrableOn (fun z => |R z| ^ p) (I ×ˢ V)
      ((volume : Measure Real).prod (volume : Measure (PDE.Vec d)))
    exact integrableOn_parabolicMorreyUnitBox_as_prod hRpow
  have hSprod : Integrable (Function.uncurry fun t : Real => fun v : PDE.Vec d =>
      |S (t, v)| ^ p) (μ.prod ν) := by
    change Integrable (Function.uncurry fun t : Real => fun v : PDE.Vec d =>
      |S (t, v)| ^ p) ((volume.restrict I).prod (volume.restrict V))
    rw [Measure.prod_restrict]
    change IntegrableOn (fun z => |S z| ^ p) (I ×ˢ V)
      ((volume : Measure Real).prod (volume : Measure (PDE.Vec d)))
    exact integrableOn_parabolicMorreyUnitBox_as_prod hSpow
  have hpoint (v : PDE.Vec d) :
      ∫ t, |R (t, v)| ^ p ∂μ <= ∫ t, |S (t, v)| ^ p ∂μ := by
    have hmean := parabolicMorreyUnitAffineProjection_eq_time_mean_spatialProjection
      hu v
    have hscalar := unitTime_meanPoincare_rpow (p := p) hp1
      ((continuous_parabolicMorreyUnitSpatialAffineProjection_of_continuous
        (continuous_timeDerivative hu)).comp (continuous_id.prodMk continuous_const))
      (hasDerivAt_parabolicMorreyUnitSpatialAffineProjection hu v)
    have haffine (t : Real) :
        parabolicMorreyUnitAffineProjection u (t, v) =
          parabolicMorreyUnitAffineProjection u (0, v) := by
      simp only [parabolicMorreyUnitAffineProjection]
    change ∫ t in I,
        |parabolicMorreyUnitSpatialAffineProjection u (t, v) -
          parabolicMorreyUnitAffineProjection u (t, v)| ^ p <=
      ∫ t in I, |S (t, v)| ^ p
    simp_rw [haffine, hmean]
    simpa only [I, S, p, Function.comp_def, id_eq] using hscalar
  have hiter :
      ∫ t, ∫ v, |R (t, v)| ^ p ∂ν ∂μ <=
        ∫ t, ∫ v, |S (t, v)| ^ p ∂ν ∂μ := by
    rw [MeasureTheory.integral_integral_swap hRprod,
      MeasureTheory.integral_integral_swap hSprod]
    exact MeasureTheory.integral_mono_ae hRprod.integral_prod_right
      hSprod.integral_prod_right (Filter.Eventually.of_forall hpoint)
  calc
    ∫ z in parabolicMorreyUnitBox d,
        |parabolicMorreyUnitSpatialAffineProjection u z -
          parabolicMorreyUnitAffineProjection u z| ^ ((d : Real) + 1) =
        ∫ t, ∫ v, |R (t, v)| ^ p ∂ν ∂μ := by
      change ∫ z, |R z| ^ p ∂volume.restrict B = _
      rw [show volume.restrict B = μ.prod ν by
        simpa only [B, μ, ν, I, V] using parabolicMorreyUnitBox_restrict_volume_eq_prod d]
      exact MeasureTheory.integral_prod _ hRprod
    _ <= ∫ t, ∫ v, |S (t, v)| ^ p ∂ν ∂μ := hiter
    _ = ∫ z in parabolicMorreyUnitBox d,
        |parabolicMorreyUnitSpatialAffineProjection (timeDerivative u) z| ^
          ((d : Real) + 1) := by
      change _ = ∫ z, |S z| ^ p ∂volume.restrict B
      rw [show volume.restrict B = μ.prod ν by
        simpa only [B, μ, ν, I, V] using parabolicMorreyUnitBox_restrict_volume_eq_prod d]
      exact (MeasureTheory.integral_prod _ hSprod).symm

end HypoellipticAleksandrov.Parabolic

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory

private theorem parabolicELpNormOn_temporalResidual_le_spatialProjection
    (d : Nat) (u : TimeVelocity d -> Real) (hu : ContDiff Real 2 u) :
    parabolicELpNormOn d (fun z => parabolicMorreyUnitSpatialAffineProjection u z -
      parabolicMorreyUnitAffineProjection u z) (parabolicMorreyUnitBox d) <=
      parabolicELpNormOn d (parabolicMorreyUnitSpatialAffineProjection (timeDerivative u))
        (parabolicMorreyUnitBox d) := by
  let p : Real := (d : Real) + 1
  let R : TimeVelocity d -> Real := fun z => parabolicMorreyUnitSpatialAffineProjection u z -
    parabolicMorreyUnitAffineProjection u z
  let S : TimeVelocity d -> Real := parabolicMorreyUnitSpatialAffineProjection (timeDerivative u)
  have hp : 0 < p := by dsimp [p]; positivity
  have hR : MemLp R (ENNReal.ofReal p) (volume.restrict (parabolicMorreyUnitBox d)) := by
    simpa [R, S, Pi.sub_def, p, parabolicExponent_eq_ofReal] using
      Continuous.memLp_parabolicMorreyUnitBox
        ((continuous_parabolicMorreyUnitSpatialAffineProjection hu).sub
          (continuous_parabolicMorreyUnitAffineProjection u))
  have hS : MemLp S (ENNReal.ofReal p) (volume.restrict (parabolicMorreyUnitBox d)) := by
    simpa [R, S, Pi.sub_def, p, parabolicExponent_eq_ofReal] using
      Continuous.memLp_parabolicMorreyUnitBox
        (continuous_parabolicMorreyUnitSpatialAffineProjection_of_continuous
          (continuous_timeDerivative hu))
  have hpower := temporalResidual_setIntegral_rpow_le_spatialProjection d u hu
  have hpow :
      (eLpNorm R (ENNReal.ofReal p) (volume.restrict (parabolicMorreyUnitBox d))).toReal ^ p <=
        (eLpNorm S (ENNReal.ofReal p) (volume.restrict (parabolicMorreyUnitBox d))).toReal ^ p := by
    rw [PDE.toReal_eLpNorm_ofReal_rpow_eq_integral_rpow_norm hp hR,
      PDE.toReal_eLpNorm_ofReal_rpow_eq_integral_rpow_norm hp hS]
    simpa [R, S, p] using hpower
  have hroot : (eLpNorm R (ENNReal.ofReal p) (volume.restrict (parabolicMorreyUnitBox d))).toReal <=
      (eLpNorm S (ENNReal.ofReal p) (volume.restrict (parabolicMorreyUnitBox d))).toReal := by
    calc
      (eLpNorm R (ENNReal.ofReal p) (volume.restrict (parabolicMorreyUnitBox d))).toReal =
          ((eLpNorm R (ENNReal.ofReal p)
            (volume.restrict (parabolicMorreyUnitBox d))).toReal ^ p) ^ p⁻¹ :=
        (Real.rpow_rpow_inv ENNReal.toReal_nonneg hp.ne').symm
      _ <= ((eLpNorm S (ENNReal.ofReal p)
        (volume.restrict (parabolicMorreyUnitBox d))).toReal ^ p) ^ p⁻¹ :=
        Real.rpow_le_rpow (by positivity) hpow (by positivity)
      _ = (eLpNorm S (ENNReal.ofReal p) (volume.restrict (parabolicMorreyUnitBox d))).toReal :=
        Real.rpow_rpow_inv ENNReal.toReal_nonneg hp.ne'
  have hENN : eLpNorm R (ENNReal.ofReal p) (volume.restrict (parabolicMorreyUnitBox d)) <=
      eLpNorm S (ENNReal.ofReal p) (volume.restrict (parabolicMorreyUnitBox d)) :=
    (ENNReal.toReal_le_toReal hR.eLpNorm_ne_top hS.eLpNorm_ne_top).mp hroot
  simpa [parabolicELpNormOn, R, S, p, parabolicExponent_eq_ofReal] using hENN

/-- Temporal Poincare control of the time-dependent moment-affine projection
by the time derivative on the literal unit box. -/
theorem parabolicMorreyUnitTemporalAffinePoincareELpNorm_le
    (d : Nat) (u : TimeVelocity d -> Real) (hu : ContDiff Real 2 u) :
    parabolicELpNormOn d (fun z => parabolicMorreyUnitSpatialAffineProjection u z -
      parabolicMorreyUnitAffineProjection u z) (parabolicMorreyUnitBox d) <=
      ENNReal.ofReal (1 + 3 * (d : Real)) * parabolicELpNormOn d (timeDerivative u)
        (parabolicMorreyUnitBox d) :=
  (parabolicELpNormOn_temporalResidual_le_spatialProjection d u hu).trans
    (parabolicELpNormOn_spatialAffineProjection_timeDerivative_le d u hu)

/-- Real-valued corollary of the temporal moment-affine Poincare estimate. -/
theorem parabolicMorreyUnitTemporalAffinePoincareLpNorm_le
    (d : Nat) (u : TimeVelocity d -> Real) (hu : ContDiff Real 2 u) :
    parabolicLpNormOn d (fun z => parabolicMorreyUnitSpatialAffineProjection u z -
      parabolicMorreyUnitAffineProjection u z) (parabolicMorreyUnitBox d) <=
      (1 + 3 * (d : Real)) * parabolicLpNormOn d (timeDerivative u)
        (parabolicMorreyUnitBox d) := by
  have hT : MemLp (timeDerivative u) (parabolicExponent d)
      (volume.restrict (parabolicMorreyUnitBox d)) :=
    Continuous.memLp_parabolicMorreyUnitBox (continuous_timeDerivative hu)
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hT.eLpNorm_ne_top)
    (parabolicMorreyUnitTemporalAffinePoincareELpNorm_le d u hu)
  unfold parabolicLpNormOn
  rw [ENNReal.toReal_ofReal_mul (1 + 3 * (d : Real)) _ (by positivity)] at h
  exact h

end HypoellipticAleksandrov.Parabolic

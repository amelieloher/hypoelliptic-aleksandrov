module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeHilbertTraces
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeGelfandAffine
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Topology.ContinuousMap.Interval

/-!
# Canonical reverse-time Hilbert boundary pairing

This module pairs the canonical continuous spatial-`L²` representative of a
reverse-time Gelfand curve with the affine terminal-zero cutoff.  It never
evaluates the raw Bochner representative at a time endpoint.
-/

@[expose] public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

private theorem intervalPrimitive_boundary_pairing
    {T : ℝ} (_hT : 0 < T) {f eta etaDeriv : ℝ → ℝ}
    (hf : IntegrableOn f (Set.Icc 0 T) volume)
    (hEta : ∀ tau ∈ Set.Icc 0 T,
      HasDerivWithinAt eta (etaDeriv tau) (Set.Icc 0 T) tau)
    (hEtaDerivCont : ContinuousOn etaDeriv (Set.Icc 0 T))
    (hEtaT : eta T = 0) :
    (∫ tau, PDE.intervalPrimitive 0 f tau * etaDeriv tau
      ∂reverseTimeVolume T) =
      -(∫ tau, f tau * eta tau ∂reverseTimeVolume T) := by
  have hEtaCont : ContinuousOn eta (Icc 0 T) := HasDerivWithinAt.continuousOn hEta
  have hleft :
      (∫ tau, PDE.intervalPrimitive 0 f tau * etaDeriv tau
        ∂reverseTimeVolume T) =
        ∫ tau in Icc 0 T, PDE.intervalPrimitive 0 f tau * etaDeriv tau := by
    simp only [reverseTimeVolume, reverseTimeOpenInterval,
      restrict_Ioo_eq_restrict_Icc]
  have hright :
      (∫ tau, f tau * eta tau ∂reverseTimeVolume T) =
        ∫ tau in Icc 0 T, f tau * eta tau := by
    simp only [reverseTimeVolume, reverseTimeOpenInterval,
      restrict_Ioo_eq_restrict_Icc]
  rw [hleft, hright]
  calc
    (∫ tau in Icc 0 T, PDE.intervalPrimitive 0 f tau * etaDeriv tau) =
        ∫ tau in Icc 0 T, ∫ s in Icc 0 tau, f s * etaDeriv tau := by
          apply setIntegral_congr_fun measurableSet_Icc
          intro tau htau
          change PDE.intervalPrimitive 0 f tau * etaDeriv tau = _
          rw [PDE.intervalPrimitive_eq_setIntegral_Icc htau.1, ← integral_mul_const]
    _ = ∫ s in Icc 0 T, ∫ tau in Icc s T, f s * etaDeriv tau :=
      PDE.setIntegral_setIntegral_Icc_swap hf hEtaDerivCont
    _ = ∫ s in Icc 0 T, -(f s * eta s) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro s hs
      change (∫ tau in Icc s T, f s * etaDeriv tau) = -(f s * eta s)
      rw [integral_const_mul]
      have hFTC : ∫ tau in s..T, etaDeriv tau = eta T - eta s := by
        exact intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hs.2
          (hEtaCont.mono (Icc_subset_Icc hs.1 le_rfl)) (fun tau ht =>
            (hEta tau ⟨le_trans hs.1 ht.1.le, ht.2.le⟩).hasDerivAt
              (Icc_mem_nhds (lt_of_le_of_lt hs.1 ht.1) ht.2)
              |>.hasDerivWithinAt)
          ((hEtaDerivCont.mono (Icc_subset_Icc hs.1 le_rfl)).intervalIntegrable_of_Icc hs.2)
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs.2,
        hFTC, hEtaT]
      ring
    _ = -(∫ s in Icc 0 T, f s * eta s) := by rw [integral_neg]

private theorem reverseTimeVStarPrimitive_apply_eq_intervalPrimitive_on_Ioo
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (g : ReverseTimeL2VStar hΩ T)
    (v : H10HilbertGraph hΩ) {tau : ℝ} (ht : tau ∈ Ioo 0 T) :
    reverseTimeVStarPrimitive hΩ T g tau v =
      PDE.intervalPrimitive 0 (fun s => (g s) v) tau := by
  rw [reverseTimeVStarPrimitive_apply hΩ T g v tau]
  change (∫ s in Ioc 0 tau, (g s) v ∂reverseTimeVolume T) = _
  rw [show (∫ s in Ioc 0 tau, (g s) v ∂reverseTimeVolume T) =
      ∫ s in Ioc 0 tau, (g s) v ∂volume by
        simp only [reverseTimeVolume, reverseTimeOpenInterval,
          Measure.restrict_restrict measurableSet_Ioc]
        rw [inter_eq_left.mpr]
        intro s hs
        exact ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩]
  exact (intervalIntegral.integral_of_le (le_of_lt ht.1)).symm

private theorem reverseTimeVolume_affine_constant_integral
    {T a : ℝ} (hT : 0 < T) :
    (∫ _ : ℝ, a * (-(T⁻¹)) ∂reverseTimeVolume T) = -a := by
  have hMeasure : (reverseTimeVolume T).real univ = T := by
    change (volume.restrict (Ioo (0 : ℝ) T)).real univ = T
    rw [MeasureTheory.measureReal_restrict_apply_univ,
      Real.volume_real_Ioo_of_le hT.le]
    norm_num
  calc
    (∫ _ : ℝ, a * (-(T⁻¹)) ∂reverseTimeVolume T) =
        ∫ _ : ℝ, a * (-(T⁻¹)) ∂reverseTimeVolume T := rfl
    _ = (reverseTimeVolume T).real univ * (a * (-(T⁻¹))) :=
      MeasureTheory.integral_const (a * (-(T⁻¹)))
    _ = -a := by
      rw [hMeasure]
      field_simp [hT.ne']

private theorem reverseTimeHilbertRepresentative_affine_pairing_eqOn
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
    (v : H10HilbertGraph hΩ) :
    EqOn
      (fun tau => inner ℝ (valueCLM hΩ v)
        (Set.IccExtend hT.le
          (reverseTimeHilbertRepresentative hΩ T hT u g hderiv) tau))
      (fun tau => reverseTimeVStarPrimitive hΩ T g tau v +
        reverseTimeGelfandAffineConstant hΩ T hT u g v)
      (Icc 0 T) := by
  let Ubar := reverseTimeHilbertRepresentative hΩ T hT u g hderiv
  let Uext : ℝ → PDE.ScalarLp Ω (2 : ℝ≥0∞) := Set.IccExtend hT.le Ubar
  let P := reverseTimeVStarPrimitive hΩ T g
  let c := reverseTimeGelfandAffineConstant hΩ T hT u g
  have hUAE : ∀ᵐ tau ∂volume.restrict (Icc 0 T),
      ∀ ht : tau ∈ Ioo 0 T,
        Ubar ⟨tau, ⟨le_of_lt ht.1, le_of_lt ht.2⟩⟩ = valueCLM hΩ (u tau) := by
    simpa only [Ubar, ReverseTimeHilbertRepresentativeAgrees, reverseTimeVolume,
      reverseTimeOpenInterval, restrict_Ioo_eq_restrict_Icc] using
      (reverseTimeHilbertRepresentative_spec hΩ T hT u g hderiv).1
  have hGelfandAE : ∀ᵐ tau ∂volume.restrict (Icc 0 T),
      reverseTimeGelfandCLM hΩ T u tau =
        scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ (u tau)) := by
    have h := coeFn_reverseTimeGelfandCLM hΩ T u
    simp only [reverseTimeVolume, reverseTimeOpenInterval,
      restrict_Ioo_eq_restrict_Icc] at h
    filter_upwards [h] with tau ht
    exact ht
  have hAffineAE : ∀ᵐ tau ∂volume.restrict (Icc 0 T),
      reverseTimeGelfandCLM hΩ T u tau = P tau + c := by
    have h := reverseTimeGelfandCLM_ae_eq_reverseTimeVStarPrimitive_add_affineConstant
      hΩ T hT u g hderiv
    simp only [reverseTimeVolume, reverseTimeOpenInterval,
      restrict_Ioo_eq_restrict_Icc] at h
    filter_upwards [h] with tau ht
    exact ht
  have hIoo : ∀ᵐ tau ∂volume.restrict (Icc 0 T), tau ∈ Ioo 0 T := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  have hPairAE : (fun tau => inner ℝ (valueCLM hΩ v) (Uext tau)) =ᵐ[
      volume.restrict (Icc 0 T)] fun tau => P tau v + c v := by
    filter_upwards [hIoo, hUAE, hGelfandAE, hAffineAE]
      with tau ht hU hG hA
    have htIcc : tau ∈ Icc 0 T := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    calc
      inner ℝ (valueCLM hΩ v) (Uext tau) =
          inner ℝ (valueCLM hΩ v) (Ubar ⟨tau, htIcc⟩) := by
            change inner ℝ (valueCLM hΩ v) (Set.IccExtend hT.le Ubar tau) = _
            rw [Set.IccExtend_of_mem hT.le Ubar htIcc]
      _ = inner ℝ (valueCLM hΩ v) (valueCLM hΩ (u tau)) := by rw [hU ht]
      _ = scalarLpToH10HilbertGraphDual hΩ (valueCLM hΩ (u tau)) v := by
            rw [scalarLpToH10HilbertGraphDual_apply]
      _ = reverseTimeGelfandCLM hΩ T u tau v := by
            exact congrArg (fun ell : H10HilbertGraphDual hΩ => ell v) hG.symm
      _ = (P tau + c) v := congrArg (fun ell : H10HilbertGraphDual hΩ => ell v) hA
      _ = P tau v + c v := by rw [ContinuousLinearMap.add_apply]
  have hUCont : ContinuousOn (fun tau => inner ℝ (valueCLM hΩ v) (Uext tau)) (Icc 0 T) := by
    exact (innerSL ℝ (valueCLM hΩ v)).continuous.comp_continuousOn
      Ubar.continuous.Icc_extend'.continuousOn
  have hPCont : ContinuousOn (fun tau => P tau v + c v) (Icc 0 T) := by
    exact ((ContinuousLinearMap.apply ℝ ℝ v).continuous.comp_continuousOn
      (continuousOn_reverseTimeVStarPrimitive hΩ T g)).add continuousOn_const
  have hPairEqOn : EqOn (fun tau => inner ℝ (valueCLM hΩ v) (Uext tau))
      (fun tau => P tau v + c v) (Icc 0 T) :=
    Measure.eqOn_Icc_of_ae_eq volume hT.ne hPairAE hUCont hPCont
  exact hPairEqOn

private theorem reverseTimeHilbertRepresentative_affine_pairing_integral
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
    (v : H10HilbertGraph hΩ) :
    (∫ tau, inner ℝ (valueCLM hΩ v)
      (Set.IccExtend hT.le
        (reverseTimeHilbertRepresentative hΩ T hT u g hderiv) tau) * (-(T⁻¹))
      ∂reverseTimeVolume T) =
      ∫ tau, (reverseTimeVStarPrimitive hΩ T g tau v +
        reverseTimeGelfandAffineConstant hΩ T hT u g v) * (-(T⁻¹))
        ∂reverseTimeVolume T := by
  have hPairEqOn := reverseTimeHilbertRepresentative_affine_pairing_eqOn
    hΩ T hT u g hderiv v
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with tau ht
  exact congrArg (fun z => z * (-(T⁻¹)))
    (hPairEqOn ⟨le_of_lt ht.1, le_of_lt ht.2⟩)

private theorem reverseTimeVStarPrimitive_affine_initial_source_pairing
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (g : ReverseTimeL2VStar hΩ T) (v : H10HilbertGraph hΩ) :
    (∫ tau, reverseTimeVStarPrimitive hΩ T g tau v * (-(T⁻¹))
      ∂reverseTimeVolume T) =
      -(∫ tau, (g tau) v * (1 - tau / T) ∂reverseTimeVolume T) := by
  have hgIcc : IntegrableOn (fun tau => (g tau) v) (Icc 0 T) volume := by
    letI : IsFiniteMeasure (reverseTimeVolume T) := by
      change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) T))
      infer_instance
    change Integrable (fun tau => (g tau) v) (volume.restrict (Icc 0 T))
    simpa only [reverseTimeVolume, reverseTimeOpenInterval,
      restrict_Ioo_eq_restrict_Icc, ContinuousLinearMap.apply_apply] using
      ((MeasureTheory.Lp.memLp g).continuousLinearMap_comp
        (ContinuousLinearMap.apply ℝ ℝ v)).integrable (by norm_num)
  have hAffineDeriv : ∀ tau ∈ Icc 0 T,
      HasDerivWithinAt (fun tau : ℝ => 1 - tau / T) (-(T⁻¹)) (Icc 0 T) tau := by
    intro tau _
    simpa only [div_eq_mul_inv, zero_sub, one_mul, Pi.sub_def, id_eq] using
      (hasDerivAt_const (x := tau) (1 : ℝ)).sub
        ((hasDerivAt_id (x := tau)).mul_const T⁻¹) |>.hasDerivWithinAt
  have hAffineTerminal : 1 - T / T = 0 := by
    rw [div_self hT.ne']
    ring
  have hboundary := intervalPrimitive_boundary_pairing hT hgIcc hAffineDeriv
    continuousOn_const hAffineTerminal
  have hPrimitiveAE :
      (fun tau => reverseTimeVStarPrimitive hΩ T g tau v * (-(T⁻¹))) =ᵐ[
        reverseTimeVolume T] fun tau =>
          PDE.intervalPrimitive 0 (fun s => (g s) v) tau * (-(T⁻¹)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with tau ht
    exact congrArg (fun z => z * (-(T⁻¹)))
      (reverseTimeVStarPrimitive_apply_eq_intervalPrimitive_on_Ioo hΩ T g v ht)
  calc
    (∫ tau, reverseTimeVStarPrimitive hΩ T g tau v * (-(T⁻¹))
      ∂reverseTimeVolume T) =
        ∫ tau, PDE.intervalPrimitive 0 (fun s => (g s) v) tau * (-(T⁻¹))
          ∂reverseTimeVolume T := integral_congr_ae hPrimitiveAE
    _ = -(∫ tau, (g tau) v * (1 - tau / T) ∂reverseTimeVolume T) := hboundary

private theorem reverseTimeGelfandAffineConstant_apply_eq_initial_trace
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
    (v : H10HilbertGraph hΩ) :
    reverseTimeGelfandAffineConstant hΩ T hT u g v = inner ℝ (valueCLM hΩ v)
      (reverseTimeInitialTrace hΩ T hT u g hderiv) := by
  have hPairEqOn := reverseTimeHilbertRepresentative_affine_pairing_eqOn
    hΩ T hT u g hderiv v
  have hzero := hPairEqOn (left_mem_Icc.mpr hT.le)
  change inner ℝ (valueCLM hΩ v)
    (Set.IccExtend hT.le (reverseTimeHilbertRepresentative hΩ T hT u g hderiv) 0) =
      reverseTimeVStarPrimitive hΩ T g 0 v +
        reverseTimeGelfandAffineConstant hΩ T hT u g v at hzero
  rw [Set.IccExtend_left, reverseTimeVStarPrimitive_zero, ContinuousLinearMap.zero_apply,
    zero_add] at hzero
  change reverseTimeGelfandAffineConstant hΩ T hT u g v =
    inner ℝ (valueCLM hΩ v)
      (reverseTimeHilbertRepresentative hΩ T hT u g hderiv
        ⟨(0 : ℝ), ⟨le_rfl, hT.le⟩⟩)
  exact hzero.symm

/-- Pairing the canonical continuous Hilbert representative with the affine
terminal-zero cutoff recovers the reverse-time source pairing and the canonical
initial trace. -/
theorem reverseTimeHilbertRepresentative_affine_initial_pairing
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
    (v : H10HilbertGraph hΩ) :
    (∫ tau,
      inner ℝ (valueCLM hΩ v)
        (Set.IccExtend hT.le
          (reverseTimeHilbertRepresentative hΩ T hT u g hderiv) tau) *
          (-(T⁻¹))
        ∂reverseTimeVolume T) =
      -(∫ tau, (g tau) v * (1 - tau / T) ∂reverseTimeVolume T) -
        inner ℝ (valueCLM hΩ v)
          (reverseTimeInitialTrace hΩ T hT u g hderiv) := by
  have hPairIntegral := reverseTimeHilbertRepresentative_affine_pairing_integral
    hΩ T hT u g hderiv v
  have hPrimitive := reverseTimeVStarPrimitive_affine_initial_source_pairing
    hΩ T hT g v
  have hConstant :
      (∫ tau, reverseTimeGelfandAffineConstant hΩ T hT u g v * (-(T⁻¹))
        ∂reverseTimeVolume T) =
        -(reverseTimeGelfandAffineConstant hΩ T hT u g v) := by
    exact reverseTimeVolume_affine_constant_integral (T := T)
      (a := reverseTimeGelfandAffineConstant hΩ T hT u g v) hT
  have hTrace := reverseTimeGelfandAffineConstant_apply_eq_initial_trace
    hΩ T hT u g hderiv v
  rw [hPairIntegral]
  calc
    (∫ tau, (reverseTimeVStarPrimitive hΩ T g tau v +
      reverseTimeGelfandAffineConstant hΩ T hT u g v) * (-(T⁻¹))
      ∂reverseTimeVolume T) =
        (∫ tau, reverseTimeVStarPrimitive hΩ T g tau v * (-(T⁻¹))
          ∂reverseTimeVolume T) +
          ∫ tau, reverseTimeGelfandAffineConstant hΩ T hT u g v * (-(T⁻¹))
            ∂reverseTimeVolume T := by
              rw [← integral_add]
              · apply integral_congr_ae
                filter_upwards with tau
                ring
              · exact (integrable_reverseTimeVStarPrimitive_apply hΩ T g v).mul_const _
              · letI : IsFiniteMeasure (reverseTimeVolume T) := by
                  change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) T))
                  infer_instance
                exact integrable_const _
    _ = -(∫ tau, (g tau) v * (1 - tau / T) ∂reverseTimeVolume T) -
        reverseTimeGelfandAffineConstant hΩ T hT u g v := by
          rw [hPrimitive, hConstant]
          ring
    _ = -(∫ tau, (g tau) v * (1 - tau / T) ∂reverseTimeVolume T) -
        inner ℝ (valueCLM hΩ v)
          (reverseTimeInitialTrace hΩ T hT u g hderiv) := by rw [hTrace]

end HypoellipticAleksandrov.Parabolic.Dirichlet

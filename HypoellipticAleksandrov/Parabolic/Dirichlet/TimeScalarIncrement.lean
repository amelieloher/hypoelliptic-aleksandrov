module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeDerivativeKernel

/-!
# Reverse-time scalar increment testing

This module converts a continuous scalar increment identity on the literal
reverse-time interval into its compactly supported distributional identity.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open Filter Function MeasureTheory Set Topology
open scoped ENNReal

private theorem exists_strict_reverseTimeScalarTest_collar
    (T : ℝ) (hT : 0 < T) (eta : ReverseTimeScalarTest T) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < T ∧
      tsupport (eta : ℝ → ℝ) ⊆ Ioo a b ∧ tsupport eta.deriv ⊆ Ioo a b := by
  by_cases hsupport : (tsupport (eta : ℝ → ℝ)).Nonempty
  · obtain ⟨lo, hlo, hloMin⟩ :=
      eta.hasCompactSupport.exists_isMinOn hsupport continuousOn_id
    obtain ⟨hi, hhi, hhiMax⟩ :=
      eta.hasCompactSupport.exists_isMaxOn hsupport continuousOn_id
    have hloIoo : lo ∈ Ioo (0 : ℝ) T := eta.tsupport_subset hlo
    have hhiIoo : hi ∈ Ioo (0 : ℝ) T := eta.tsupport_subset hhi
    obtain ⟨a, ha0, halo⟩ := exists_between hloIoo.1
    obtain ⟨b, hhib, hbT⟩ := exists_between hhiIoo.2
    have hlohi : lo ≤ hi := hloMin hhi
    refine ⟨a, b, ha0, ?_, hbT, ?_, ?_⟩
    · exact lt_of_lt_of_le halo (hlohi.trans_lt hhib).le
    · intro t ht
      exact ⟨lt_of_lt_of_le halo (hloMin ht),
        lt_of_le_of_lt (hhiMax ht) hhib⟩
    · have hderivSupport : tsupport eta.deriv ⊆ tsupport (eta : ℝ → ℝ) := by
        rw [ReverseTimeScalarTest.deriv, tsupport]
        exact closure_minimal support_deriv_subset (isClosed_tsupport _)
      exact hderivSupport.trans (by
        intro t ht
        exact ⟨lt_of_lt_of_le halo (hloMin ht),
          lt_of_le_of_lt (hhiMax ht) hhib⟩)
  · have heta : (eta : ℝ → ℝ) = 0 := by
      funext t
      apply image_eq_zero_of_notMem_tsupport
      exact fun ht => hsupport ⟨t, ht⟩
    have hderiv : eta.deriv = 0 := by
      funext t
      rw [eta.deriv_apply, heta]
      simp
    refine ⟨T / 3, 2 * T / 3, by linarith, by linarith, by linarith, ?_, ?_⟩
    · rw [heta]
      simp
    · rw [hderiv]
      simp

private theorem integral_reverseTime_eq_integral_Icc_of_tsupport_subset
    {T a b : ℝ} {F phi : ℝ → ℝ}
    (hK : Icc a b ⊆ Ioo (0 : ℝ) T) (hphi : tsupport phi ⊆ Ioo a b) :
    (∫ t, F t * phi t ∂reverseTimeVolume T) = ∫ t in Icc a b, F t * phi t := by
  change (∫ t in Ioo (0 : ℝ) T, F t * phi t) = ∫ t in Icc a b, F t * phi t
  apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioo hK
  intro t ht
  rw [image_eq_zero_of_notMem_tsupport (fun hts => ht.2
    ⟨le_of_lt (hphi hts).1, le_of_lt (hphi hts).2⟩)]
  ring

private theorem reverseTime_Ioc_integral_eq_volume_Icc_integral
    {T a b s t : ℝ} {q : ℝ → ℝ}
    (hK : Icc a b ⊆ Ioo (0 : ℝ) T)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    (∫ r in Ioc s t, q r ∂reverseTimeVolume T) = ∫ r in Icc s t, q r := by
  have hIoc : Ioc s t ⊆ Ioo (0 : ℝ) T := by
    intro r hr
    exact ⟨lt_of_lt_of_le (hK hs).1 (mem_Ioc.mp hr).1.le,
      lt_of_le_of_lt (mem_Ioc.mp hr).2 (hK ht).2⟩
  change (∫ r, q r ∂(volume.restrict (Ioo (0 : ℝ) T)).restrict (Ioc s t)) = _
  rw [Measure.restrict_restrict_of_subset hIoc, ← integral_Icc_eq_integral_Ioc]

private def intervalPrimitive (a : ℝ) (q : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ r in a..t, q r

private theorem intervalPrimitive_eq_setIntegral_Icc
    {a t : ℝ} (hat : a ≤ t) (q : ℝ → ℝ) :
    intervalPrimitive a q t = ∫ r in Icc a t, q r := by
  rw [intervalPrimitive, intervalIntegral.integral_of_le hat,
    ← integral_Icc_eq_integral_Ioc]

private theorem continuousOn_intervalPrimitive
    {a b : ℝ} {q : ℝ → ℝ} (hab : a ≤ b)
    (hq : IntegrableOn q (Icc a b) volume) :
    ContinuousOn (intervalPrimitive a q) (Icc a b) := by
  have hq' : IntegrableOn q (uIcc a b) volume := by
    simpa only [uIcc_of_le hab] using hq
  change ContinuousOn (fun t => ∫ r in a..t, q r) (Icc a b)
  rw [← uIcc_of_le hab]
  exact intervalIntegral.continuousOn_primitive_interval hq'

private theorem setIntegral_setIntegral_Icc_swap
    {a b : ℝ} {q psi : ℝ → ℝ}
    (hq : IntegrableOn q (Icc a b) volume)
    (hpsi : ContinuousOn psi (Icc a b)) :
    ∫ t in Icc a b, (∫ r in Icc a t, q r * psi t) =
      ∫ r in Icc a b, (∫ t in Icc r b, q r * psi t) := by
  let I : Set ℝ := Icc a b
  let μ : Measure ℝ := volume.restrict I
  let triangle : Set (ℝ × ℝ) := {z | z.1 ≤ z.2}
  have htriangle : MeasurableSet triangle :=
    (isClosed_le continuous_fst continuous_snd).measurableSet
  have hqμ : Integrable q μ := by
    simpa only [μ, I, IntegrableOn] using hq
  have hpsiμ : Integrable psi μ := by
    simpa only [μ, I, IntegrableOn] using hpsi.integrableOn_Icc
  have hprod : Integrable (fun z : ℝ × ℝ => q z.1 * psi z.2) (μ.prod μ) :=
    hqμ.mul_prod hpsiμ
  have htriangleInt : Integrable
      (triangle.indicator (fun z : ℝ × ℝ => q z.1 * psi z.2)) (μ.prod μ) :=
    hprod.indicator htriangle
  have hleft :
      (∫ t, ∫ r, triangle.indicator (fun z : ℝ × ℝ => q z.1 * psi z.2) (r, t) ∂μ ∂μ) =
        ∫ t in Icc a b, (∫ r in Icc a t, q r * psi t) := by
    rw [show (∫ t, ∫ r,
        triangle.indicator (fun z : ℝ × ℝ => q z.1 * psi z.2) (r, t) ∂μ ∂μ) =
        ∫ t in I, ∫ r,
          triangle.indicator (fun z : ℝ × ℝ => q z.1 * psi z.2) (r, t) ∂μ ∂volume by
      rfl]
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    change (∫ r, triangle.indicator (fun z : ℝ × ℝ => q z.1 * psi z.2) (r, t) ∂μ) = _
    have hsection :
        (fun r => triangle.indicator (fun z : ℝ × ℝ => q z.1 * psi z.2) (r, t)) =
          (Iic t).indicator (fun r => q r * psi t) := by
      funext r
      by_cases hrt : r ≤ t
      · rw [Set.indicator_of_mem (show (r, t) ∈ triangle by exact hrt),
          Set.indicator_of_mem (show r ∈ Iic t by exact hrt)]
      · rw [Set.indicator_of_notMem (show (r, t) ∉ triangle by exact hrt),
          Set.indicator_of_notMem (show r ∉ Iic t by exact hrt)]
    rw [hsection, integral_indicator measurableSet_Iic]
    change (∫ r, q r * psi t ∂(volume.restrict I).restrict (Iic t)) = _
    rw [Measure.restrict_restrict measurableSet_Iic]
    have hIt : Iic t ∩ I = Icc a t := by
      ext r
      simp only [I, mem_inter_iff, mem_Icc, mem_Iic]
      constructor
      · intro hr
        exact ⟨hr.2.1, hr.1⟩
      · intro hr
        exact ⟨hr.2, ⟨hr.1, hr.2.trans ht.2⟩⟩
    rw [hIt]
  have hright :
      (∫ r, ∫ t, triangle.indicator (fun z : ℝ × ℝ => q z.1 * psi z.2) (r, t) ∂μ ∂μ) =
        ∫ r in Icc a b, (∫ t in Icc r b, q r * psi t) := by
    rw [show (∫ r, ∫ t,
        triangle.indicator (fun z : ℝ × ℝ => q z.1 * psi z.2) (r, t) ∂μ ∂μ) =
        ∫ r in I, ∫ t,
          triangle.indicator (fun z : ℝ × ℝ => q z.1 * psi z.2) (r, t) ∂μ ∂volume by
      rfl]
    apply setIntegral_congr_fun measurableSet_Icc
    intro r hr
    change (∫ t, triangle.indicator (fun z : ℝ × ℝ => q z.1 * psi z.2) (r, t) ∂μ) = _
    have hsection :
        (fun t => triangle.indicator (fun z : ℝ × ℝ => q z.1 * psi z.2) (r, t)) =
          (Ici r).indicator (fun t => q r * psi t) := by
      funext t
      by_cases hrt : r ≤ t
      · rw [Set.indicator_of_mem (show (r, t) ∈ triangle by exact hrt),
          Set.indicator_of_mem (show t ∈ Ici r by exact hrt)]
      · rw [Set.indicator_of_notMem (show (r, t) ∉ triangle by exact hrt),
          Set.indicator_of_notMem (show t ∉ Ici r by exact hrt)]
    rw [hsection, integral_indicator measurableSet_Ici]
    change (∫ t, q r * psi t ∂(volume.restrict I).restrict (Ici r)) = _
    rw [Measure.restrict_restrict measurableSet_Ici]
    have hIr : Ici r ∩ I = Icc r b := by
      ext t
      simp only [I, mem_inter_iff, mem_Icc, mem_Ici]
      constructor
      · intro ht
        exact ⟨ht.1, ht.2.2⟩
      · intro ht
        exact ⟨ht.1, ⟨hr.1.trans ht.1, ht.2⟩⟩
    rw [hIr]
  calc
    ∫ t in Icc a b, (∫ r in Icc a t, q r * psi t) =
        ∫ t, ∫ r, triangle.indicator (fun z : ℝ × ℝ => q z.1 * psi z.2) (r, t) ∂μ ∂μ :=
      hleft.symm
    _ = ∫ r, ∫ t, triangle.indicator (fun z : ℝ × ℝ => q z.1 * psi z.2) (r, t) ∂μ ∂μ :=
      integral_integral_swap htriangleInt.swap
    _ = ∫ r in Icc a b, (∫ t in Icc r b, q r * psi t) := hright

private theorem setIntegral_deriv_tail_eq_neg
    {a b t : ℝ} (ht : t ∈ Icc a b) {psi : ℝ → ℝ}
    (hpsi : ContDiff ℝ 1 psi) (hsupp : tsupport psi ⊆ Ioo a b) :
    ∫ r in Icc t b, deriv psi r = -psi t := by
  have hbzero : psi b = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hb
    exact (not_lt_of_ge le_rfl) (hsupp hb).2
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le ht.2,
    intervalIntegral.integral_deriv_eq_sub' psi rfl
      (fun r _ => hpsi.differentiable (by norm_num) r)
      (hpsi.continuous_deriv (by norm_num)).continuousOn,
    hbzero]
  ring

private theorem intervalPrimitive_scalar_weak_identity_Icc
    {a b : ℝ} {q : ℝ → ℝ}
    (hq : IntegrableOn q (Icc a b) volume) {psi : ℝ → ℝ}
    (hpsi : ContDiff ℝ 1 psi) (hsupp : tsupport psi ⊆ Ioo a b) :
    ∫ t in Icc a b, intervalPrimitive a q t * deriv psi t =
      -∫ t in Icc a b, q t * psi t := by
  rw [show (∫ t in Icc a b, intervalPrimitive a q t * deriv psi t) =
      ∫ t in Icc a b, ∫ r in Icc a t, q r * deriv psi t by
        apply setIntegral_congr_fun measurableSet_Icc
        intro t ht
        change intervalPrimitive a q t * deriv psi t =
          ∫ r in Icc a t, q r * deriv psi t
        rw [intervalPrimitive_eq_setIntegral_Icc ht.1]
        rw [integral_mul_const]
    , setIntegral_setIntegral_Icc_swap hq
      (hpsi.continuous_deriv (by norm_num)).continuousOn]
  have htail : ∀ r ∈ Icc a b, ∫ t in Icc r b, q r * deriv psi t = -(q r * psi r) := by
    intro r hr
    rw [integral_const_mul, setIntegral_deriv_tail_eq_neg hr hpsi hsupp]
    ring
  rw [show (∫ r in Icc a b, ∫ t in Icc r b, q r * deriv psi t) =
      ∫ r in Icc a b, -(q r * psi r) by
        apply setIntegral_congr_fun measurableSet_Icc
        exact htail]
  rw [integral_neg]

private theorem integral_mul_deriv_eq_neg_integral_of_increment
    {a b : ℝ} {e q : ℝ → ℝ}
    (hab : a ≤ b) (hq : IntegrableOn q (Icc a b) volume)
    (he : ContinuousOn e (Icc a b))
    (hinc : ∀ s t : ℝ, s ∈ Icc a b → t ∈ Icc a b → s ≤ t →
      e t - e s = ∫ r in Icc s t, q r)
    {eta : ℝ → ℝ} (heta : ContDiff ℝ 1 eta) (hsupp : tsupport eta ⊆ Ioo a b) :
    (∫ t in Icc a b, e t * deriv eta t) =
      -(∫ t in Icc a b, q t * eta t) := by
  have heIcc : IntegrableOn e (Icc a b) volume := he.integrableOn_Icc
  have hetaIcc : IntegrableOn eta (Icc a b) volume :=
    heta.continuous.integrableOn_Icc
  have hderivIcc : IntegrableOn (deriv eta) (Icc a b) volume :=
    (heta.continuous_deriv (by simp)).integrableOn_Icc
  have heFormula : ∀ t ∈ Icc a b, e t = intervalPrimitive a q t + e a := by
    intro t ht
    have h := hinc a t ⟨le_rfl, hab⟩ ht ht.1
    calc
      e t = (∫ r in Icc a t, q r) + e a := by linarith
      _ = intervalPrimitive a q t + e a := by
        rw [intervalPrimitive_eq_setIntegral_Icc ht.1]
  have hleft : (∫ t in Icc a b, e t * deriv eta t) =
      ∫ t in Icc a b, (intervalPrimitive a q t + e a) * deriv eta t := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    change e t * deriv eta t = _
    rw [heFormula t ht]
  rw [hleft]
  calc
    (∫ t in Icc a b, (intervalPrimitive a q t + e a) * deriv eta t) =
        ∫ t in Icc a b, intervalPrimitive a q t * deriv eta t + e a * deriv eta t := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro t _
      ring
    _ = (∫ t in Icc a b, intervalPrimitive a q t * deriv eta t) +
        ∫ t in Icc a b, e a * deriv eta t := by
      rw [integral_add]
      · exact ((continuousOn_intervalPrimitive hab hq).mul
          (heta.continuous_deriv (by simp)).continuousOn).integrableOn_Icc
      · simpa only [Pi.mul_apply] using hderivIcc.const_mul (e a)
    _ = -(∫ t in Icc a b, q t * eta t) := by
      rw [intervalPrimitive_scalar_weak_identity_Icc hq heta hsupp]
      have htail : ∫ t in Icc a b, deriv eta t = 0 := by
        rw [integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le hab,
          intervalIntegral.integral_deriv_eq_sub' eta rfl
            (fun t _ => heta.differentiable (by norm_num) t)
            (heta.continuous_deriv (by norm_num)).continuousOn]
        have ha : eta a = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          exact fun ht => (not_lt_of_ge le_rfl) (hsupp ht).1
        have hb : eta b = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          exact fun ht => (not_lt_of_ge le_rfl) (hsupp ht).2
        rw [ha, hb]
        ring
      rw [integral_const_mul, htail]
      ring

/-- A reverse-time scalar increment identity yields its compactly supported
distributional testing identity on the literal restricted time measure. -/
theorem integral_mul_reverseTimeScalarTest_deriv_eq_neg_integral_of_increment
    (T : ℝ) (hT : 0 < T)
    (q e : ℝ → ℝ)
    (hq : MeasureTheory.Integrable q (reverseTimeVolume T))
    (he : ContinuousOn e (Set.Icc 0 T))
    (hinc : ∀ s t : ℝ, s ∈ Set.Icc 0 T → t ∈ Set.Icc 0 T → s ≤ t →
      e t - e s = ∫ r in Set.Ioc s t, q r ∂reverseTimeVolume T)
    (eta : ReverseTimeScalarTest T) :
    (∫ t, e t * eta.deriv t ∂reverseTimeVolume T) =
      -(∫ t, q t * eta t ∂reverseTimeVolume T) := by
  obtain ⟨a, b, ha, hab, hb, heta, hetaDeriv⟩ :=
    exists_strict_reverseTimeScalarTest_collar T hT eta
  have hK : Icc a b ⊆ Ioo (0 : ℝ) T := by
    intro t ht
    exact ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
  have hqIcc : IntegrableOn q (Icc a b) volume := by
    change Integrable q (volume.restrict (Ioo (0 : ℝ) T)) at hq
    simpa only [Measure.restrict_restrict_of_subset hK, IntegrableOn] using
      hq.restrict (s := Icc a b)
  have heIcc : ContinuousOn e (Icc a b) := he.mono (by
    intro t ht
    exact ⟨(hK ht).1.le, (hK ht).2.le⟩)
  have hincIcc : ∀ s t : ℝ, s ∈ Icc a b → t ∈ Icc a b → s ≤ t →
      e t - e s = ∫ r in Icc s t, q r := by
    intro s t hs ht hst
    rw [hinc s t
      ⟨(hK hs).1.le, (hK hs).2.le⟩
      ⟨(hK ht).1.le, (hK ht).2.le⟩ hst]
    exact reverseTime_Ioc_integral_eq_volume_Icc_integral hK hs ht
  rw [integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK hetaDeriv,
    integral_reverseTime_eq_integral_Icc_of_tsupport_subset hK heta]
  exact integral_mul_deriv_eq_neg_integral_of_increment hab.le hqIcc heIcc hincIcc
    (eta.contDiff.of_le (by norm_num)) heta

end HypoellipticAleksandrov.Parabolic.Dirichlet

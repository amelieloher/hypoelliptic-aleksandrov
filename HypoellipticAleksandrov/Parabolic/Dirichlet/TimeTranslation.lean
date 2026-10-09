module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeBochner
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Local translation continuity for reverse-time Bochner spaces

This module obtains local literal-representative `L²` translation continuity
from the continuous domain-add action on ambient `Lp`.  The local statements
use a zero extension only as an `Lp` representative; they make no derivative
claim for that extension.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

private theorem sqNorm_integral_eq_norm_sq_toLp
    {E : Type*} [NormedAddCommGroup E]
    {μ : Measure ℝ} (F : ℝ → E) (hF : MemLp F (2 : ℝ≥0∞) μ) :
    ∫ t, ‖F t‖ ^ 2 ∂μ = ‖hF.toLp F‖ ^ 2 := by
  rw [Lp.norm_def, eLpNorm_congr_ae hF.coeFn_toLp,
    hF.eLpNorm_eq_integral_rpow_norm]
  · simp
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun _ => sq_nonneg _) _)]
    exact (Real.rpow_inv_natCast_pow
      (integral_nonneg fun _ => sq_nonneg _) (by norm_num)).symm
  · norm_num
  · simp

private theorem tendsto_sqNorm_integral_translate_add_on_of_memLp_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ℝ → E) (hF : MemLp F (2 : ℝ≥0∞) volume) (s : Set ℝ) :
    Tendsto (fun h : ℝ => ∫ t in s, ‖F (t + h) - F t‖ ^ 2) (𝓝 0) (𝓝 0) := by
  let f : Lp (α := ℝ) E (2 : ℝ≥0∞) volume := hF.toLp F
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have hcont : Continuous (fun h : ℝ => DomAddAct.mk h +ᵥ f) :=
    continuous_vadd.comp (DomAddAct.continuous_mk.prodMk continuous_const)
  have hzero : DomAddAct.mk (0 : ℝ) +ᵥ f = f := by
    simp
  have hcontsub : Continuous (fun h : ℝ => (DomAddAct.mk h +ᵥ f) - f) :=
    hcont.sub continuous_const
  have hvalue : (DomAddAct.mk (0 : ℝ) +ᵥ f) - f = 0 := by
    rw [hzero, sub_self]
  have hsub : Tendsto (fun h : ℝ => (DomAddAct.mk h +ᵥ f) - f) (𝓝 0) (𝓝 0) := by
    have hat : Tendsto (fun h : ℝ => (DomAddAct.mk h +ᵥ f) - f) (𝓝 0)
        (𝓝 ((DomAddAct.mk (0 : ℝ) +ᵥ f) - f)) :=
      hcontsub.continuousAt
    rw [hvalue] at hat
    exact hat
  have hnorm : Tendsto (fun h : ℝ => ‖(DomAddAct.mk h +ᵥ f) - f‖ ^ 2)
      (𝓝 0) (𝓝 0) := by
    simpa using hsub.norm.pow 2
  refine squeeze_zero (g := fun h : ℝ => ‖(DomAddAct.mk h +ᵥ f) - f‖ ^ 2)
    (fun _ => integral_nonneg fun _ => sq_nonneg _) (fun h => ?_) hnorm
  let htrans : MemLp (fun t : ℝ => F (h + t)) (2 : ℝ≥0∞) volume :=
    hF.comp_measurePreserving (measurePreserving_add_left volume h)
  let hdiff : MemLp (fun t : ℝ => F (h + t) - F t) (2 : ℝ≥0∞) volume :=
    htrans.sub hF
  let q : Lp (α := ℝ) E (2 : ℝ≥0∞) volume := hdiff.toLp _
  let qS : Lp (α := ℝ) E (2 : ℝ≥0∞) (volume.restrict s) :=
    ((Lp.memLp q).restrict s).toLp q
  have hq : q =ᵐ[volume] fun t : ℝ => F (h + t) - F t := by
    simpa [q] using hdiff.coeFn_toLp
  have hqS : qS =ᵐ[volume.restrict s] q := by
    simpa [qS] using MemLp.coeFn_toLp ((Lp.memLp q).restrict s)
  have hsq : (∫ t in s, ‖F (t + h) - F t‖ ^ 2) = ‖qS‖ ^ 2 := by
    change (∫ t, ‖F (t + h) - F t‖ ^ 2 ∂volume.restrict s) = _
    have hqSsq := sqNorm_integral_eq_norm_sq_toLp (qS : ℝ → E) (Lp.memLp qS)
    rw [Lp.toLp_coeFn qS (Lp.memLp qS)] at hqSsq
    rw [← hqSsq]
    apply integral_congr_ae
    filter_upwards [hqS, ae_restrict_of_ae hq] with t htS ht
    rw [htS, ht, add_comm]
  rw [hsq]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_Lp_toLp_restrict_le s q) 2

/-- Ambient Bochner `L²` translation continuity for an arbitrary representative. -/
theorem tendsto_sqNorm_integral_translate_add_of_memLp_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ℝ → E) (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) volume) :
    Filter.Tendsto
      (fun h : ℝ => ∫ t, ‖F (t + h) - F t‖ ^ 2)
      (𝓝 0) (𝓝 0) := by
  simpa only [Measure.restrict_univ] using
    tendsto_sqNorm_integral_translate_add_on_of_memLp_two F hF univ

/-- Forward local translation continuity on a compact interval inside reverse time. -/
theorem tendsto_sqNorm_integral_forward_translate_on_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ)
    (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < T) :
    Filter.Tendsto
      (fun h : ℝ => ∫ t in Set.Icc a b, ‖f (t + h) - f t‖ ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  let S : Set ℝ := Ioo 0 T
  let F : ℝ → E := S.indicator f
  have hS : MeasurableSet S := by
    simp only [S]
    exact measurableSet_Ioo
  have hF : MemLp F (2 : ℝ≥0∞) volume := by
    simpa only [F, S, reverseTimeVolume, reverseTimeOpenInterval] using
      (memLp_indicator_iff_restrict hS).mpr (Lp.memLp f)
  have hmax : max a b < T := by
    rw [max_eq_right hab]
    exact hb
  have hglobal := tendsto_sqNorm_integral_translate_add_on_of_memLp_two F hF (Icc a b)
  have hlocal : Tendsto
      (fun h : ℝ => ∫ t in Icc a b, ‖F (t + h) - F t‖ ^ 2)
      (𝓝[Ioi 0] 0) (𝓝 0) :=
    hglobal.mono_left (by
      exact nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Ioi (0 : ℝ)))
  apply Filter.Tendsto.congr' ?_ hlocal
  have hpos : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h := self_mem_nhdsWithin
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h < T - b :=
    (eventually_lt_nhds (sub_pos.mpr hb)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpos, hsmall] with h hh hsmall
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  have htS : t ∈ S := by
    change 0 < t ∧ t < T
    constructor
    · exact lt_of_lt_of_le ha ht.1
    · calc
        t ≤ b := ht.2
        _ ≤ max a b := le_max_right _ _
        _ < T := hmax
  have hthS : t + h ∈ S := by
    change 0 < t + h ∧ t + h < T
    constructor
    · exact add_pos (lt_of_lt_of_le ha ht.1) hh
    · have hbh : b + h < T := by
        rw [add_comm]
        exact lt_sub_iff_add_lt.mp hsmall
      calc
        t + h = h + t := add_comm _ _
        _ ≤ h + b := add_le_add_right ht.2 _
        _ = b + h := add_comm _ _
        _ < T := hbh
  simp only [F, Set.indicator_of_mem hthS, Set.indicator_of_mem htS]

/-- Backward local translation continuity on a compact interval inside reverse time. -/
theorem tendsto_sqNorm_integral_backward_translate_on_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ)
    (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < T) :
    Filter.Tendsto
      (fun h : ℝ => ∫ t in Set.Icc a b, ‖f (t - h) - f t‖ ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  let S : Set ℝ := Ioo 0 T
  let F : ℝ → E := S.indicator f
  have hS : MeasurableSet S := by
    simp only [S]
    exact measurableSet_Ioo
  have hF : MemLp F (2 : ℝ≥0∞) volume := by
    simpa only [F, S, reverseTimeVolume, reverseTimeOpenInterval] using
      (memLp_indicator_iff_restrict hS).mpr (Lp.memLp f)
  have hmax : max a b < T := by
    rw [max_eq_right hab]
    exact hb
  have hplus := tendsto_sqNorm_integral_translate_add_on_of_memLp_two F hF (Icc a b)
  have hneg : Tendsto (fun h : ℝ => -h) (𝓝 0) (𝓝 0) := by
    simpa using tendsto_neg (0 : ℝ)
  have hglobal : Tendsto (fun h : ℝ => ∫ t in Icc a b, ‖F (t - h) - F t‖ ^ 2)
      (𝓝 0) (𝓝 0) := by
    simpa only [sub_eq_add_neg, Function.comp_def] using hplus.comp hneg
  have hlocal : Tendsto
      (fun h : ℝ => ∫ t in Icc a b, ‖F (t - h) - F t‖ ^ 2)
      (𝓝[Ioi 0] 0) (𝓝 0) :=
    hglobal.mono_left (by
      exact nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Ioi (0 : ℝ)))
  apply Filter.Tendsto.congr' ?_ hlocal
  have hpos : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h := self_mem_nhdsWithin
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h < a :=
    (eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpos, hsmall] with h hh hsmall
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  have htS : t ∈ S := by
    change 0 < t ∧ t < T
    constructor
    · exact lt_of_lt_of_le ha ht.1
    · calc
        t ≤ b := ht.2
        _ ≤ max a b := le_max_right _ _
        _ < T := hmax
  have hthS : t - h ∈ S := by
    change 0 < t - h ∧ t - h < T
    constructor
    · rw [sub_pos]
      exact lt_of_lt_of_le hsmall ht.1
    · calc
        t - h < t := sub_lt_self _ hh
        _ ≤ b := ht.2
        _ < T := hb
  simp only [F, Set.indicator_of_mem hthS, Set.indicator_of_mem htS]

end HypoellipticAleksandrov.Parabolic.Dirichlet

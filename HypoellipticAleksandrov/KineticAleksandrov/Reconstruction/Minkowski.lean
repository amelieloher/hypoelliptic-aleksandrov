module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Minkowski's integral inequality

For σ-finite measures `m` on `α` and `ν` on `β`, a jointly measurable `F : α → β → ℝ≥0∞` and
`1 < p`,
`(∫⁻ y, (∫⁻ ξ, F y ξ ∂ν)^p ∂m)^(1/p) ≤ ∫⁻ ξ, (∫⁻ y, F y ξ^p ∂m)^(1/p) ∂ν`
(`minkowski_integral`).  The proof is the standard duality argument (`minkowski_aux`), valid when
the left-hand side is finite, together with a truncation to finite-measure boxes and bounded
values (`trunc`) and monotone convergence.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal

namespace HypoellipticAleksandrov.KineticAleksandrov.Reconstruction

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {m : Measure α} {ν : Measure β}

/-- Minkowski's inequality when the left-hand side is finite (duality argument). -/
lemma minkowski_aux [SFinite m] [SFinite ν] {p : ℝ} (hp : 1 < p) {F : α → β → ℝ≥0∞}
    (hF : Measurable (Function.uncurry F))
    (hA : ∫⁻ y, (∫⁻ ξ, F y ξ ∂ν) ^ p ∂m ≠ ∞) :
    (∫⁻ y, (∫⁻ ξ, F y ξ ∂ν) ^ p ∂m) ^ (1 / p) ≤
      ∫⁻ ξ, (∫⁻ y, F y ξ ^ p ∂m) ^ (1 / p) ∂ν := by
  set I : α → ℝ≥0∞ := fun y => ∫⁻ ξ, F y ξ ∂ν with hI
  have hIm : Measurable I := hF.lintegral_prod_right'
  set A := ∫⁻ y, I y ^ p ∂m with hAdef
  set B := ∫⁻ ξ, (∫⁻ y, F y ξ ^ p ∂m) ^ (1 / p) ∂ν with hBdef
  have hq := Real.HolderConjugate.conjExponent hp
  set q := p.conjExponent with hqdef
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := hq.symm.pos
  have hpq : 1 / p + 1 / q = 1 := by simpa using hq.inv_add_inv_eq_one
  have hq1 : p - 1 = p / q := by
    have := hq.inv_add_inv_eq_one
    field_simp at this ⊢
    linarith
  have hIpow : Measurable fun y => I y ^ (p - 1) := hIm.pow_const _
  have hpq' : (p - 1) * q = p := by rw [hq1]; field_simp
  have hFy : ∀ y, Measurable (F y) := fun y => hF.comp measurable_prodMk_left
  have hFξ : ∀ ξ, Measurable fun y => F y ξ := fun ξ => hF.comp measurable_prodMk_right
  have hNm : Measurable fun ξ => (∫⁻ y, F y ξ ^ p ∂m) ^ (1 / p) := by
    have : Measurable fun z : β × α => F z.2 z.1 ^ p := (hF.comp measurable_swap).pow_const p
    exact (this.lintegral_prod_right').pow_const _
  have key : A ≤ A ^ (1 / q) * B := by
    calc A = ∫⁻ y, I y ^ (p - 1) * I y ∂m := by
          refine lintegral_congr fun y => ?_
          conv_lhs => rw [show p = (p - 1) + 1 by ring]
          rw [ENNReal.rpow_add_of_nonneg _ _ (by linarith) (by linarith), ENNReal.rpow_one]
      _ = ∫⁻ y, ∫⁻ ξ, I y ^ (p - 1) * F y ξ ∂ν ∂m := by
          refine lintegral_congr fun y => ?_
          rw [lintegral_const_mul _ (hFy y)]
      _ = ∫⁻ ξ, ∫⁻ y, I y ^ (p - 1) * F y ξ ∂m ∂ν := by
          refine lintegral_lintegral_swap ?_
          exact ((hIpow.comp measurable_fst).mul hF).aemeasurable
      _ ≤ ∫⁻ ξ, (∫⁻ y, F y ξ ^ p ∂m) ^ (1 / p) * (A ^ (1 / q)) ∂ν := by
          refine lintegral_mono fun ξ => ?_
          have h := ENNReal.lintegral_mul_le_Lp_mul_Lq m hq (hFξ ξ).aemeasurable
            hIpow.aemeasurable
          have h2 : ∫⁻ y, (I y ^ (p - 1)) ^ q ∂m = A := by
            refine lintegral_congr fun y => ?_
            rw [← ENNReal.rpow_mul, hpq']
          simp only [Pi.mul_apply, h2] at h
          calc ∫⁻ y, I y ^ (p - 1) * F y ξ ∂m
              = ∫⁻ y, F y ξ * I y ^ (p - 1) ∂m := lintegral_congr fun y => mul_comm _ _
            _ ≤ _ := h
      _ = A ^ (1 / q) * B := by
          rw [lintegral_mul_const _ hNm, mul_comm]
  by_cases hA0 : A = 0
  · rw [hA0, ENNReal.zero_rpow_of_pos (by positivity)]
    exact zero_le
  · have hq' : 0 < 1 / q := by positivity
    have hsplit : A = A ^ (1 / q) * A ^ (1 / p) := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ hq'.le (by positivity), add_comm, hpq,
        ENNReal.rpow_one]
    have hne0 : A ^ (1 / q) ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hA0) hA).ne'
    have hneT : A ^ (1 / q) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hq'.le hA
    rw [← ENNReal.mul_le_mul_iff_right hne0 hneT]
    calc A ^ (1 / q) * A ^ (1 / p) = A := hsplit.symm
      _ ≤ _ := key


/-- Truncation of a jointly measurable function to finite-measure boxes and bounded values. -/
noncomputable def trunc (m : Measure α) (ν : Measure β) [SigmaFinite m] [SigmaFinite ν]
    (F : α → β → ℝ≥0∞) (n : ℕ) (y : α) (ξ : β) : ℝ≥0∞ :=
  (spanningSets m n ×ˢ spanningSets ν n).indicator (fun q => min (F q.1 q.2) n) (y, ξ)

section Trunc

variable [SigmaFinite m] [SigmaFinite ν] {F : α → β → ℝ≥0∞}

/-- The truncation is jointly measurable. -/
lemma measurable_trunc (hF : Measurable (Function.uncurry F)) (n : ℕ) :
    Measurable (Function.uncurry (trunc m ν F n)) := by
  unfold trunc
  exact (hF.min measurable_const).indicator
    ((measurableSet_spanningSets m n).prod (measurableSet_spanningSets ν n))

/-- The truncation is dominated by `F`. -/
lemma trunc_le (n : ℕ) (y : α) (ξ : β) : trunc m ν F n y ξ ≤ F y ξ := by
  unfold trunc
  by_cases h : (y, ξ) ∈ spanningSets m n ×ˢ spanningSets ν n
  · rw [Set.indicator_of_mem h]; exact min_le_left _ _
  · rw [Set.indicator_of_notMem h]; exact zero_le

/-- The truncation is monotone in `n`. -/
lemma trunc_mono (y : α) (ξ : β) : Monotone fun n => trunc m ν F n y ξ := by
  intro a b hab
  show trunc m ν F a y ξ ≤ trunc m ν F b y ξ
  unfold trunc
  by_cases h : (y, ξ) ∈ spanningSets m a ×ˢ spanningSets ν a
  · have h2 : (y, ξ) ∈ spanningSets m b ×ˢ spanningSets ν b :=
      ⟨spanningSets_mono hab h.1, spanningSets_mono hab h.2⟩
    rw [Set.indicator_of_mem h, Set.indicator_of_mem h2]
    exact min_le_min le_rfl (by exact_mod_cast hab)
  · rw [Set.indicator_of_notMem h]; exact zero_le

/-- The truncations increase to `F`. -/
lemma iSup_trunc (y : α) (ξ : β) : ⨆ n, trunc m ν F n y ξ = F y ξ := by
  refine le_antisymm (iSup_le fun n => trunc_le n y ξ) ?_
  refine le_of_forall_lt fun c hc => ?_
  obtain ⟨N, hN⟩ := mem_iUnion.1 (by rw [iUnion_spanningSets]; trivial : y ∈ ⋃ n, spanningSets m n)
  obtain ⟨N', hN'⟩ := mem_iUnion.1 (by rw [iUnion_spanningSets]; trivial :
    ξ ∈ ⋃ n, spanningSets ν n)
  obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt (hc.trans_le le_top).ne
  have hmem : (y, ξ) ∈ spanningSets m (max (max N N') k) ×ˢ spanningSets ν (max (max N N') k) :=
    ⟨spanningSets_mono (le_trans (le_max_left _ _) (le_max_left _ _)) hN,
      spanningSets_mono (le_trans (le_max_right _ _) (le_max_left _ _)) hN'⟩
  refine lt_of_lt_of_le ?_ (le_iSup _ (max (max N N') k))
  unfold trunc
  rw [Set.indicator_of_mem hmem]
  exact lt_min hc (hk.trans_le (by exact_mod_cast le_max_right _ _))

/-- The truncated Minkowski left-hand side is finite. -/
lemma lintegral_trunc_ne_top {p : ℝ} (hp : 0 < p) (n : ℕ) :
    ∫⁻ y, (∫⁻ ξ, trunc m ν F n y ξ ∂ν) ^ p ∂m ≠ ∞ := by
  set c : ℝ≥0∞ := n * ν (spanningSets ν n) with hc
  have hcT : c ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) (measure_spanningSets_lt_top ν n).ne
  have hI : ∀ y, ∫⁻ ξ, trunc m ν F n y ξ ∂ν ≤ (spanningSets m n).indicator (fun _ => c) y := by
    intro y
    by_cases hy : y ∈ spanningSets m n
    · rw [Set.indicator_of_mem hy]
      calc ∫⁻ ξ, trunc m ν F n y ξ ∂ν
          ≤ ∫⁻ ξ, (spanningSets ν n).indicator (fun _ => (n : ℝ≥0∞)) ξ ∂ν := by
            refine lintegral_mono fun ξ => ?_
            unfold trunc
            by_cases hξ : ξ ∈ spanningSets ν n
            · rw [Set.indicator_of_mem (show (y, ξ) ∈ spanningSets m n ×ˢ spanningSets ν n from
                ⟨hy, hξ⟩), Set.indicator_of_mem hξ]
              exact min_le_right _ _
            · rw [Set.indicator_of_notMem (fun h => hξ h.2)]; exact zero_le
        _ = c := by
            rw [lintegral_indicator_const (measurableSet_spanningSets ν n), hc]
    · rw [Set.indicator_of_notMem hy]
      have : ∀ ξ, trunc m ν F n y ξ = 0 := fun ξ => by
        unfold trunc
        exact Set.indicator_of_notMem (fun h => hy h.1) _
      simp [this]
  refine ne_top_of_le_ne_top (b := ∫⁻ y, (spanningSets m n).indicator (fun _ => c ^ p) y ∂m) ?_ ?_
  · rw [lintegral_indicator_const (measurableSet_spanningSets m n)]
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp.le hcT)
      (measure_spanningSets_lt_top m n).ne
  · refine lintegral_mono fun y => ?_
    refine (ENNReal.rpow_le_rpow (hI y) hp.le).trans ?_
    by_cases hy : y ∈ spanningSets m n
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, ENNReal.zero_rpow_of_pos hp]

end Trunc


/-- Minkowski's integral inequality for nonnegative jointly measurable functions. -/
theorem minkowski_integral [SigmaFinite m] [SigmaFinite ν] {p : ℝ} (hp : 1 < p)
    {F : α → β → ℝ≥0∞} (hF : Measurable (Function.uncurry F)) :
    (∫⁻ y, (∫⁻ ξ, F y ξ ∂ν) ^ p ∂m) ^ (1 / p) ≤
      ∫⁻ ξ, (∫⁻ y, F y ξ ^ p ∂m) ^ (1 / p) ∂ν := by
  have hp0 : 0 < p := by linarith
  set B := ∫⁻ ξ, (∫⁻ y, F y ξ ^ p ∂m) ^ (1 / p) ∂ν with hB
  have hGm := measurable_trunc (m := m) (ν := ν) hF
  have hn : ∀ n, ∫⁻ y, (∫⁻ ξ, trunc m ν F n y ξ ∂ν) ^ p ∂m ≤ B ^ p := by
    intro n
    have h1 := minkowski_aux (m := m) (ν := ν) hp (hGm n) (lintegral_trunc_ne_top hp0 n)
    have h2 : ∫⁻ ξ, (∫⁻ y, trunc m ν F n y ξ ^ p ∂m) ^ (1 / p) ∂ν ≤ B := by
      refine lintegral_mono fun ξ => ?_
      refine ENNReal.rpow_le_rpow (lintegral_mono fun y => ?_) (by positivity)
      exact ENNReal.rpow_le_rpow (trunc_le n y ξ) hp0.le
    have h3 := ENNReal.rpow_le_rpow (h1.trans h2) hp0.le
    rwa [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one] at h3
  have hI : ∀ y, ⨆ n, ∫⁻ ξ, trunc m ν F n y ξ ∂ν = ∫⁻ ξ, F y ξ ∂ν := by
    intro y
    have hmeas : ∀ n, Measurable fun ξ => trunc m ν F n y ξ :=
      fun n => (hGm n).comp measurable_prodMk_left
    have := lintegral_iSup (μ := ν) hmeas (fun a b hab ξ => trunc_mono y ξ hab)
    rw [← this]
    exact lintegral_congr fun ξ => iSup_trunc y ξ
  have hA : ∫⁻ y, (∫⁻ ξ, F y ξ ∂ν) ^ p ∂m =
      ⨆ n, ∫⁻ y, (∫⁻ ξ, trunc m ν F n y ξ ∂ν) ^ p ∂m := by
    have hmono : ∀ y, Monotone fun n => ∫⁻ ξ, trunc m ν F n y ξ ∂ν :=
      fun y a b hab => lintegral_mono fun ξ => trunc_mono y ξ hab
    rw [← lintegral_iSup]
    · refine lintegral_congr fun y => ?_
      rw [← hI y]
      exact (ENNReal.monotone_rpow_of_nonneg hp0.le).map_iSup_of_continuousAt
        (ENNReal.continuous_rpow_const.continuousAt) (ENNReal.zero_rpow_of_pos hp0)
    · intro n
      exact ((hGm n).lintegral_prod_right').pow_const _
    · intro a b hab y
      exact ENNReal.rpow_le_rpow (lintegral_mono fun ξ => trunc_mono y ξ hab) hp0.le
  have hAB : ∫⁻ y, (∫⁻ ξ, F y ξ ∂ν) ^ p ∂m ≤ B ^ p := by
    rw [hA]; exact iSup_le hn
  have := ENNReal.rpow_le_rpow hAB (show 0 ≤ 1 / p by positivity)
  rwa [← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one] at this

end HypoellipticAleksandrov.KineticAleksandrov.Reconstruction

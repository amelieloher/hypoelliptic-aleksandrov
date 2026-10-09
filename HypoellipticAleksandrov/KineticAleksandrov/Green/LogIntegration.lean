module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Logarithmic integration over dyadic slabs

The averaging step of the proof of the companion paper, Theorem 2.4: for a non-negative
function `F`, `∫_0^S F ≤ (1/log 2) ∫_0^S (dT/T) ∫_T^{2T} F`, because each `τ ∈ (0,S)` is counted
for `τ/2 < T < τ`, a set of logarithmic length `log 2`.  Here this is proved for a measure `ν`
and a measurable positive height `h` (`τ = h`): `log 2 · ν{h < S} ≤ ∫_0^S ν{T < h < 2T} dT/T`.
We also record the power integral `∫_0^S T^{δ-1} dT = S^δ/δ`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Green

open MeasureTheory Set
open scoped ENNReal

/-- `∫_{a/2}^{a} dT/T = log 2`. -/
lemma lintegral_inv_Ioo_half {a : ℝ} (ha : 0 < a) :
    ∫⁻ T in Ioo (a / 2) a, ENNReal.ofReal T⁻¹ = ENNReal.ofReal (Real.log 2) := by
  have ha2 : 0 < a / 2 := by positivity
  have hle : a / 2 ≤ a := by linarith
  have hint : IntervalIntegrable (fun x : ℝ => x⁻¹) volume (a / 2) a :=
    intervalIntegral.intervalIntegrable_inv (fun x hx => by
      rw [Set.uIcc_of_le hle] at hx
      exact (lt_of_lt_of_le ha2 hx.1).ne') continuousOn_id
  have h1 : ∫⁻ T in Ioo (a / 2) a, ENNReal.ofReal T⁻¹ =
      ∫⁻ T in Ioc (a / 2) a, ENNReal.ofReal T⁻¹ :=
    setLIntegral_congr Ioo_ae_eq_Ioc
  rw [h1, ← ofReal_integral_eq_lintegral_ofReal
    (by simpa [IntegrableOn, Set.uIoc_of_le hle] using hint.1)
    ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun T hT =>
      inv_nonneg.2 (by linarith [hT.1])))]
  congr 1
  rw [← intervalIntegral.integral_of_le hle, integral_inv_of_pos ha2 ha]
  congr 1
  field_simp

/-- The inner logarithmic integral of the indicator of `T < h < 2T` over `(0,S]`. -/
lemma lintegral_inv_indicator {h S : ℝ} (hh : 0 < h) (hhS : h < S) :
    ∫⁻ T in Ioc 0 S, ENNReal.ofReal T⁻¹ *
        ({p : ℝ | p < h ∧ h < 2 * p}.indicator (fun _ => (1 : ℝ≥0∞)) T) =
      ENNReal.ofReal (Real.log 2) := by
  rw [← lintegral_inv_Ioo_half hh]
  have hset : {p : ℝ | p < h ∧ h < 2 * p} = Ioo (h / 2) h := by
    ext p; simp only [mem_ofPred_eq, mem_Ioo]; constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;>
      linarith
  rw [hset]
  have hB : MeasurableSet (Ioo (h / 2) h) := measurableSet_Ioo
  have hfun : ∀ T : ℝ, ENNReal.ofReal T⁻¹ *
      (Ioo (h / 2) h).indicator (fun _ => (1 : ℝ≥0∞)) T =
      (Ioo (h / 2) h).indicator (fun T => ENNReal.ofReal T⁻¹) T := by
    intro T
    by_cases hT : T ∈ Ioo (h / 2) h <;> simp [hT]
  simp_rw [hfun]
  rw [lintegral_indicator hB, Measure.restrict_restrict hB]
  congr 2
  ext p
  simp only [mem_inter_iff, mem_Ioo, mem_Ioc]
  constructor
  · exact fun hp => hp.1
  · intro hp
    exact ⟨hp, by linarith [hp.1], by linarith [hp.2]⟩

/-- Logarithmic averaging: `log 2 · ν{h < S} ≤ ∫_0^S ν{T < h < 2T} dT/T`. -/
lemma log_mul_measure_le {X : Type*} [MeasurableSpace X] (ν : Measure X) [SFinite ν]
    {h : X → ℝ} (hh : Measurable h) (hpos : ∀ x, 0 < h x) (S : ℝ) :
    ENNReal.ofReal (Real.log 2) * ν {x | h x < S} ≤
      ∫⁻ T in Ioc 0 S, ENNReal.ofReal T⁻¹ * ν {x | T < h x ∧ h x < 2 * T} := by
  set f : X → ℝ → ℝ≥0∞ := fun x T => ENNReal.ofReal T⁻¹ *
    ({p : ℝ | p < h x ∧ h x < 2 * p}.indicator (fun _ => (1 : ℝ≥0∞)) T) with hf
  have hSet : MeasurableSet {q : X × ℝ | q.2 < h q.1 ∧ h q.1 < 2 * q.2} :=
    (measurableSet_lt measurable_snd (hh.comp measurable_fst)).inter
      (measurableSet_lt (hh.comp measurable_fst) (measurable_const.mul measurable_snd))
  have hfm : Measurable (Function.uncurry f) := by
    have : Function.uncurry f = fun q : X × ℝ => ENNReal.ofReal q.2⁻¹ *
        ({q : X × ℝ | q.2 < h q.1 ∧ h q.1 < 2 * q.2}.indicator (fun _ => (1 : ℝ≥0∞)) q) := by
      ext q; rfl
    rw [this]
    exact (ENNReal.measurable_ofReal.comp measurable_snd.inv).mul
      (measurable_const.indicator hSet)
  calc ENNReal.ofReal (Real.log 2) * ν {x | h x < S}
      = ∫⁻ x, {x | h x < S}.indicator (fun _ => ENNReal.ofReal (Real.log 2)) x ∂ν := by
        rw [lintegral_indicator_const (measurableSet_lt hh measurable_const), mul_comm]
    _ ≤ ∫⁻ x, (∫⁻ T in Ioc 0 S, f x T) ∂ν := by
        refine lintegral_mono fun x => ?_
        by_cases hx : h x < S
        · rw [Set.indicator_of_mem (show x ∈ {x | h x < S} from hx)]
          exact (lintegral_inv_indicator (hpos x) hx).ge
        · rw [Set.indicator_of_notMem (show x ∉ {x | h x < S} from hx)]
          exact zero_le
    _ = ∫⁻ T in Ioc 0 S, (∫⁻ x, f x T ∂ν) :=
        lintegral_lintegral_swap hfm.aemeasurable
    _ = _ := by
        refine lintegral_congr fun T => ?_
        have : ∀ x, f x T = ENNReal.ofReal T⁻¹ *
            {x | T < h x ∧ h x < 2 * T}.indicator (fun _ => (1 : ℝ≥0∞)) x := by
          intro x; rfl
        simp_rw [this]
        have hs : MeasurableSet {x | T < h x ∧ h x < 2 * T} :=
          (measurableSet_lt measurable_const hh).inter (measurableSet_lt hh measurable_const)
        rw [lintegral_const_mul _ (measurable_const.indicator hs)]
        congr 1
        exact lintegral_indicator_one hs

/-- `∫_0^S T^{-1} (K T^δ) dT = K S^δ / δ`. -/
lemma lintegral_inv_mul_rpow {S δ : ℝ} (hS : 0 < S) (hδ : 0 < δ) (K : ℝ≥0∞) :
    ∫⁻ T in Ioc 0 S, ENNReal.ofReal T⁻¹ * (K * ENNReal.ofReal (T ^ δ)) =
      K * ENNReal.ofReal (S ^ δ / δ) := by
  have h1 : ∀ T ∈ Ioc 0 S, ENNReal.ofReal T⁻¹ * (K * ENNReal.ofReal (T ^ δ)) =
      K * ENNReal.ofReal (T ^ (δ - 1)) := by
    intro T hT
    have hT0 : 0 < T := hT.1
    have : T ^ (δ - 1) = T⁻¹ * T ^ δ := by
      rw [Real.rpow_sub hT0, Real.rpow_one]; field_simp
    rw [this, ENNReal.ofReal_mul (inv_nonneg.2 hT0.le), mul_left_comm]
  have hmeas : Measurable fun x : ℝ => ENNReal.ofReal (x ^ (δ - 1)) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)
  rw [setLIntegral_congr_fun measurableSet_Ioc h1, lintegral_const_mul K hmeas]
  congr 1
  have hint : IntegrableOn (fun T : ℝ => T ^ (δ - 1)) (Ioc 0 S) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := S)
      (by linarith : -1 < δ - 1)).1
    simpa [Set.uIoc_of_le hS.le] using this
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun T hT =>
      (Real.rpow_pos_of_pos hT.1 _).le))]
  congr 1
  rw [← intervalIntegral.integral_of_le hS.le, integral_rpow (Or.inl (by linarith))]
  have : δ - 1 + 1 = δ := by ring
  rw [this, Real.zero_rpow hδ.ne']
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Green

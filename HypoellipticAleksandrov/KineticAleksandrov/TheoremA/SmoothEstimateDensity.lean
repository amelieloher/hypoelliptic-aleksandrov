module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! # Real representatives of finite-power Green densities -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.TheoremA
open MeasureTheory Filter
open scoped ENNReal

/-- A finite positive-power density norm gives a measurable nonnegative real representative. -/
theorem real_density_of_eLpNorm_bound {α : Type*} [MeasurableSpace α]
    (μ Γ : Measure α) (G : α → ℝ≥0∞) (hG : Measurable G)
    (hΓ : Γ = μ.withDensity G) (q C : ℝ) (hq : 0 < q) (hC : 0 ≤ C)
    (hnorm : eLpNorm G (ENNReal.ofReal q) μ ≤ ENNReal.ofReal C) :
    ∃ F : α → ℝ, Measurable F ∧ (∀ x, 0 ≤ F x) ∧
      Γ = μ.withDensity (fun x => ENNReal.ofReal (F x)) ∧
      (eLpNorm F (ENNReal.ofReal q) μ).toReal ≤ C ∧
      MemLp F (ENNReal.ofReal q) μ := by
  have hfin : eLpNorm G (ENNReal.ofReal q) μ < ⊤ :=
    hnorm.trans_lt ENNReal.ofReal_lt_top
  have hl := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
    (ENNReal.ofReal_pos.mpr hq).ne' ENNReal.ofReal_ne_top hfin
  have hpow : ∫⁻ x, G x ^ q ∂μ < ⊤ := by
    simpa only [enorm_eq_self, ENNReal.toReal_ofReal hq.le] using hl
  have hae : ∀ᵐ x ∂μ, G x ≠ ⊤ := by
    filter_upwards [ae_lt_top (hG.pow_const q) hpow.ne] with x hx
    exact fun h => hx.ne ((ENNReal.rpow_eq_top_iff_of_pos hq).mpr h)
  have hFm : Measurable (fun x => (G x).toReal) := hG.ennreal_toReal
  have heq : (fun x => ENNReal.ofReal ((G x).toReal)) =ᵐ[μ] G := by
    filter_upwards [hae] with x hx
    exact ENNReal.ofReal_toReal hx
  have hN : eLpNorm (fun x => (G x).toReal) (ENNReal.ofReal q) μ =
      eLpNorm G (ENNReal.ofReal q) μ := by
    apply eLpNorm_congr_enorm_ae hFm.aestronglyMeasurable hG.aestronglyMeasurable
    filter_upwards [heq] with x hx
    simpa only [Real.enorm_of_nonneg ENNReal.toReal_nonneg, enorm_eq_self] using hx
  refine ⟨_, hFm, fun x => ENNReal.toReal_nonneg, ?_, ?_, ?_⟩
  · rw [hΓ, withDensity_congr_ae heq]
  · rw [hN]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hnorm).trans_eq
      (ENNReal.toReal_ofReal hC)
  · change eLpNorm _ _ _ < ⊤
    rw [hN]
    exact hfin

end HypoellipticAleksandrov.KineticAleksandrov.TheoremA

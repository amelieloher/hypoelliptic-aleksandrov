module

public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabSetting
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Lemma 5.1: the scaling `ζ = T^{3/2} ξ`

`∫_{ℝ^d} exp(-c T |ξ|^{2/3}) dξ = T^{-3d/2} ∫_{ℝ^d} exp(-c |ζ|^{2/3}) dζ` and the last integral is
finite for `c > 0`, `d ≥ 1` (Euclidean norm `≥` sup norm, polar integration in the sup norm).
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Green

open MeasureTheory Set
open scoped ENNReal NNReal

/-- The decay profile `exp(-c |ζ|^{2/3})` (Euclidean norm), as an `ℝ≥0∞`-valued function. -/
def decayProfile (d : ℕ) (c : ℝ) (ζ : PDE.Vec d) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(c * PDE.vecEuclideanNorm ζ ^ ((2 : ℝ) / 3))))

/-- The decay profile is Lebesgue integrable: `∫ exp(-c |ζ|^{2/3}) dζ < ∞`. -/
theorem lintegral_decayProfile_lt_top {d : ℕ} (hd : 0 < d) {c : ℝ} (hc : 0 < c) :
    ∫⁻ ζ, decayProfile d c ζ < ⊤ := by
  have : Nontrivial (PDE.Vec d) := by
    unfold PDE.Vec
    exact ⟨⟨0, 1, fun h => by simpa using congrFun h ⟨0, hd⟩⟩⟩
  have hint : Integrable (fun ζ : PDE.Vec d => Real.exp (-(c * ‖ζ‖ ^ ((2 : ℝ) / 3)))) := by
    refine (integrable_fun_norm_addHaar (volume : Measure (PDE.Vec d))
      (f := fun y : ℝ => Real.exp (-(c * y ^ ((2 : ℝ) / 3))))).2 ?_
    have h1 := integrableOn_rpow_mul_exp_neg_mul_rpow (p := (2 : ℝ) / 3) (s := (d : ℝ) - 1)
      (b := c) (by have : (1 : ℝ) ≤ d := by exact_mod_cast hd
                   linarith) (by norm_num) hc
    refine h1.congr_fun (fun y hy => ?_) measurableSet_Ioi
    simp only [Module.finrank_fin_fun, smul_eq_mul]
    rw [neg_mul, ← Real.rpow_natCast, Nat.cast_sub hd]
    simp
  have hle : ∀ ζ : PDE.Vec d, decayProfile d c ζ ≤
      ENNReal.ofReal (Real.exp (-(c * ‖ζ‖ ^ ((2 : ℝ) / 3)))) := by
    intro ζ
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have h1 := PDE.norm_le_vecEuclideanNorm ζ
    have h2 : ‖ζ‖ ^ ((2 : ℝ) / 3) ≤ PDE.vecEuclideanNorm ζ ^ ((2 : ℝ) / 3) :=
      Real.rpow_le_rpow (norm_nonneg _) h1 (by norm_num)
    nlinarith
  exact (lintegral_mono hle).trans_lt hint.lintegral_lt_top


lemma measurable_decayProfile (d : ℕ) (c : ℝ) : Measurable (decayProfile d c) := by
  have h : Measurable (fun ζ : PDE.Vec d => PDE.vecEuclideanNorm ζ) := by
    unfold PDE.vecEuclideanNorm PDE.vecNormSq PDE.vecDot
    fun_prop
  unfold decayProfile
  exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (((measurable_const.mul (h.pow_const _))).neg))

/-- **Scaling `ζ = T^{3/2} ξ`.** -/
theorem lintegral_decayProfile_scaling (d : ℕ) (c T : ℝ) (hT : 0 < T) :
    ∫⁻ ξ : PDE.Vec d,
        ENNReal.ofReal (Real.exp (-(c * T * PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3)))) =
      ENNReal.ofReal (T ^ (-(3 * (d : ℝ) / 2))) * ∫⁻ ζ, decayProfile d c ζ := by
  set a : ℝ := T ^ ((3 : ℝ) / 2) with ha
  have ha0 : 0 < a := Real.rpow_pos_of_pos hT _
  have hfun : ∀ ξ : PDE.Vec d,
      ENNReal.ofReal (Real.exp (-(c * T * PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3)))) =
        decayProfile d c (a • ξ) := by
    intro ξ
    unfold decayProfile
    rw [PDE.vecEuclideanNorm_smul, abs_of_pos ha0, Real.mul_rpow ha0.le
      (PDE.vecEuclideanNorm_nonneg ξ), ha, ← Real.rpow_mul hT.le]
    norm_num
    ring_nf
  simp_rw [hfun]
  have hmap := Measure.map_addHaar_smul (volume : Measure (PDE.Vec d)) ha0.ne'
  have hm : Measurable (fun ξ : PDE.Vec d => a • ξ) := measurable_const_smul a
  rw [← lintegral_map (measurable_decayProfile d c) hm, hmap, lintegral_smul_measure]
  congr 1
  simp only [Module.finrank_fin_fun, abs_inv, abs_pow, abs_of_pos ha0]
  congr 1
  rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul hT.le, ← Real.rpow_neg hT.le]
  congr 1
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Green

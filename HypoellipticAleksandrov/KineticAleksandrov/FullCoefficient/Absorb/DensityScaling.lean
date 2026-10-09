module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.FlowInstance
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Absorb.DensityLimit
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The Gaussian flow kernel is an approximate identity

The Gaussian flow: the kernel has the parabolic scaling
`Φ_{s²}(s v, s³ z) = s^{-4d} Φ_1(v, z)`, so `∫ ψ(y + w) Φ_ε(w) dw = ∫ ψ(y + T_{√ε} w) Φ_1(w) dw`
with `T_s(v, z) = (s v, s³ z)`, which tends to `ψ(y)` by dominated convergence.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open MeasureTheory Filter Topology
open scoped ENNReal

variable {d : ℕ}

/-- The parabolic dilation `T_s (v, z) = (s v, s³ z)`. -/
def parabolicScale (s : ℝ) (w : EvolutionAmbientState d) : EvolutionAmbientState d :=
  (s • w.1, s ^ 3 • w.2)

/-- The pair density has the parabolic scaling in `h = s²`. -/
theorem flowPairDensity_scale {lam s : ℝ} (hl : 0 < lam) (hs : 0 < s) (u w : ℝ) :
    flowPairDensity lam (s ^ 2) (s ^ 3 * u) (s * w) =
      ((s ^ 2) ^ 2)⁻¹ * flowPairDensity lam 1 u w := by
  unfold flowPairDensity
  have hpre : √(5 * lam ^ 2 * (s ^ 2) ^ 4 / 12) = (s ^ 2) ^ 2 * √(5 * lam ^ 2 * 1 ^ 4 / 12) := by
    have : (5 * lam ^ 2 * (s ^ 2) ^ 4 / 12 : ℝ) =
        ((s ^ 2) ^ 2) ^ 2 * (5 * lam ^ 2 * 1 ^ 4 / 12) := by ring
    rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have hpos : 0 < √(5 * lam ^ 2 * 1 ^ 4 / 12) := Real.sqrt_pos.2 (by positivity)
  rw [hpre, show (1 : ℝ) / (2 * Real.pi * ((s ^ 2) ^ 2 * √(5 * lam ^ 2 * 1 ^ 4 / 12))) =
    ((s ^ 2) ^ 2)⁻¹ * (1 / (2 * Real.pi * √(5 * lam ^ 2 * 1 ^ 4 / 12))) by
      field_simp, mul_assoc]
  congr 2
  field_simp

/-- The flow kernel has the parabolic scaling. -/
theorem flowKernel_parabolicScale {lam s : ℝ} (hl : 0 < lam) (hs : 0 < s)
    (w : EvolutionAmbientState d) :
    flowKernel lam (s ^ 2) (parabolicScale s w) =
      (((s ^ 2) ^ 2)⁻¹) ^ d * flowKernel lam 1 w := by
  unfold flowKernel parabolicScale
  have h : ∀ i : Fin d, flowPairDensity lam (s ^ 2) ((s ^ 3 • w.2) i) ((s • w.1) i) =
      ((s ^ 2) ^ 2)⁻¹ * flowPairDensity lam 1 (w.2 i) (w.1 i) := fun i => by
    simpa using flowPairDensity_scale hl hs (w.2 i) (w.1 i)
  rw [Finset.prod_congr rfl fun i _ => h i, Finset.prod_mul_distrib]
  simp

/-- Local instance: Lebesgue measure on phase space is an additive Haar measure. -/
local instance absorbVolumeIsAddHaar'' (d : ℕ) :
    (volume : Measure (EvolutionAmbientState d)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure volume volume

/-- The dilation `T_s` as a linear equivalence, for `s ≠ 0`. -/
def parabolicScaleEquiv (s : ℝ) (hs : s ≠ 0) :
    EvolutionAmbientState d ≃ₗ[ℝ] EvolutionAmbientState d :=
  (LinearEquiv.smulOfNeZero ℝ (PDE.Vec d) s hs).prodCongr
    (LinearEquiv.smulOfNeZero ℝ (PDE.Vec d) (s ^ 3) (pow_ne_zero 3 hs))

theorem parabolicScaleEquiv_apply (s : ℝ) (hs : s ≠ 0) (w : EvolutionAmbientState d) :
    parabolicScaleEquiv s hs w = parabolicScale s w := rfl

/-- Change of variables under the dilation: a constant multiple of the integral. -/
theorem exists_integral_comp_parabolicScale {s : ℝ} (hs : s ≠ 0) :
    ∃ c : ℝ, ∀ g : EvolutionAmbientState d → ℝ, Measurable g →
      ∫ w, g (parabolicScale s w) = c * ∫ w, g w := by
  let f : EvolutionAmbientState d →ₗ[ℝ] EvolutionAmbientState d :=
    (parabolicScaleEquiv (d := d) s hs).toLinearMap
  have hdet : LinearMap.det f ≠ 0 := (LinearEquiv.isUnit_det' _).ne_zero
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure (EvolutionAmbientState d)) hdet
  refine ⟨(ENNReal.ofReal |(LinearMap.det f)⁻¹|).toReal, fun g hg => ?_⟩
  have hf : Measurable f :=
    (parabolicScaleEquiv (d := d) s hs).toContinuousLinearEquiv.continuous.measurable
  have h1 := integral_map (μ := (volume : Measure (EvolutionAmbientState d))) hf.aemeasurable
    (f := g) (hg.aestronglyMeasurable)
  have h2 : ∫ w, g (f w) = ∫ w, g (parabolicScale s w) := rfl
  rw [← h2, ← h1, hmap, integral_smul_measure, smul_eq_mul]

theorem continuous_parabolicScale (s : ℝ) :
    Continuous (parabolicScale (d := d) s) := by
  unfold parabolicScale
  fun_prop

/-- Translated integrals of the flow kernel reduce to the unit kernel along the dilation. -/
theorem integral_translate_flowKernel {lam s : ℝ} (hl : 0 < lam) (hs : 0 < s)
    {ψ : EvolutionAmbientState d → ℝ} (hψ : Continuous ψ) (y : EvolutionAmbientState d) :
    ∫ w, ψ (y + w) * flowKernel lam (s ^ 2) w =
      ∫ w, ψ (y + parabolicScale s w) * flowKernel lam 1 w := by
  obtain ⟨c, hc⟩ := exists_integral_comp_parabolicScale (d := d) hs.ne'
  have hΦc : Continuous (flowKernel (d := d) lam 1) := (flowKernel_contDiff hl one_pos).continuous
  have hΦc' : Continuous (flowKernel (d := d) lam (s ^ 2)) :=
    (flowKernel_contDiff hl (by positivity)).continuous
  set a : ℝ := (((s ^ 2) ^ 2)⁻¹) ^ d with ha
  have ha0 : a ≠ 0 := by positivity
  have hscale : ∀ w, flowKernel lam (s ^ 2) (parabolicScale s w) = a * flowKernel lam 1 w :=
    flowKernel_parabolicScale hl hs
  have hca : c = a := by
    have h1 := hc (flowKernel lam (s ^ 2)) hΦc'.measurable
    simp_rw [hscale] at h1
    rw [integral_const_mul, integral_flowKernel hl one_pos, integral_flowKernel hl (by positivity)]
      at h1
    linarith
  have h2 : ∫ w, a * (ψ (y + parabolicScale s w) * flowKernel lam 1 w) =
      c * ∫ w, ψ (y + w) * flowKernel lam (s ^ 2) w := by
    rw [← hc (fun w => ψ (y + w) * flowKernel lam (s ^ 2) w)
      ((hψ.comp (continuous_const.add continuous_id)).mul hΦc').measurable]
    congr 1
    funext w
    rw [hscale]
    ring
  rw [integral_const_mul, hca] at h2
  exact (mul_left_cancel₀ ha0 h2).symm

/-- **The Gaussian flow family is an approximate identity**: `∫ ψ(y + w) Φ_ε(w) dw → ψ(y)` as
`ε ↓ 0`, for bounded continuous `ψ`. -/
theorem flowKernelFamily_isApproxIdentity {lam : ℝ} (hl : 0 < lam) :
    IsApproxIdentity (flowKernelFamily (d := d) hl) := by
  intro ψ B hψ hB y
  have hΦc : Continuous (flowKernel (d := d) lam 1) := (flowKernel_contDiff hl one_pos).continuous
  have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∫ w, ψ (y + parabolicScale (√ε) w) * flowKernel lam 1 w =
      ∫ w, ψ (y + w) * (flowKernelFamily (d := d) hl).kernel ε w := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : (0 : ℝ) < ε := hε
    have := integral_translate_flowKernel (d := d) hl (Real.sqrt_pos.2 hε') hψ y
    rw [Real.sq_sqrt hε'.le] at this
    exact this.symm
  refine Tendsto.congr' hev ?_
  have hψy : ψ y = ∫ w, ψ y * flowKernel (d := d) lam 1 w := by
    rw [integral_const_mul, integral_flowKernel hl one_pos, mul_one]
  rw [hψy]
  refine tendsto_integral_filter_of_dominated_convergence (fun w => B * flowKernel lam 1 w)
    ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun ε => ?_
    exact ((hψ.comp (continuous_const.add (continuous_parabolicScale _))).mul hΦc)
      |>.aestronglyMeasurable
  · refine Eventually.of_forall fun ε => Eventually.of_forall fun w => ?_
    have hp : 0 < flowKernel (d := d) lam 1 w := flowKernel_pos hl one_pos w
    rw [norm_mul, Real.norm_of_nonneg hp.le]
    exact mul_le_mul_of_nonneg_right (by simpa using hB _) hp.le
  · exact ((flowKernelFamily (d := d) hl).integrable_kernel one_pos).const_mul B
  · refine Eventually.of_forall fun w => ?_
    have hg : Continuous fun ε : ℝ => y + parabolicScale (√ε) w := by
      unfold parabolicScale
      fun_prop
    have h0 : Tendsto (fun ε : ℝ => y + parabolicScale (√ε) w) (𝓝[>] 0) (𝓝 y) := by
      have := (hg.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa [parabolicScale, Prod.mk_zero_zero] using this
    exact ((hψ.tendsto y).comp h0).mul_const _

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

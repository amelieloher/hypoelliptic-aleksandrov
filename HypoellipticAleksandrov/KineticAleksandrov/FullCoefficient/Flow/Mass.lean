module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Flow.PhaseProduct

/-!
# Mass and supremum of the Gaussian flow kernel

The Gaussian flow estimates: positivity, total mass one and the
supremum bound for `Φ_h`, derived from the Gaussian integral of the exponential
`gaussExp a b c = exp (-(∑ᵢ a zᵢ² + b zᵢ vᵢ + c vᵢ²))`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open Real MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

/-- The quadratic form `∑ᵢ a zᵢ² + b zᵢ vᵢ + c vᵢ²` on phase space `y = (v, z)`. -/
def quadForm (a b c : ℝ) (y : EvolutionAmbientState d) : ℝ :=
  ∑ i, (a * y.2 i ^ 2 + b * y.2 i * y.1 i + c * y.1 i ^ 2)

/-- The Gaussian exponential `exp (-quadForm a b c)`. -/
def gaussExp (a b c : ℝ) (y : EvolutionAmbientState d) : ℝ :=
  Real.exp (-quadForm a b c y)

theorem gaussExp_eq_prod (a b c : ℝ) (y : EvolutionAmbientState d) :
    gaussExp a b c y = ∏ i, Real.exp (-pairQ a b c (y.1 i, y.2 i)) := by
  unfold gaussExp quadForm pairQ
  rw [← Real.exp_sum, ← Finset.sum_neg_distrib]

theorem flowKernel_eq {lam h : ℝ} (hl : 0 < lam) (hh : 0 < h) (y : EvolutionAmbientState d) :
    flowKernel lam h y =
      flowConst lam h ^ d * gaussExp (flowA lam h) (flowB lam h) (flowC lam h) y := by
  have hp : flowConst lam h ^ d = ∏ _i : Fin d, flowConst lam h := by simp
  rw [gaussExp_eq_prod, hp, ← Finset.prod_mul_distrib]
  unfold flowKernel
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [flowPairDensity_eq hl hh]
  simp [pairQ]

theorem flowConst_pos {lam h : ℝ} (hl : 0 < lam) (hh : 0 < h) : 0 < flowConst lam h := by
  unfold flowConst
  have : 0 < √(12 / 5 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  positivity

theorem flowA_pos {lam h : ℝ} (hl : 0 < lam) (hh : 0 < h) : 0 < flowA lam h := by
  unfold flowA; positivity

theorem flowRes_eq {lam h : ℝ} (hl : 0 < lam) (hh : 0 < h) :
    pairRes (flowA lam h) (flowB lam h) (flowC lam h) = 1 / (2 * lam * h) := by
  unfold pairRes flowA flowB flowC
  field_simp
  ring

theorem flowRes_pos {lam h : ℝ} (hl : 0 < lam) (hh : 0 < h) :
    0 < pairRes (flowA lam h) (flowB lam h) (flowC lam h) := by
  rw [flowRes_eq hl hh]; positivity

theorem integrable_gaussExp {a b c : ℝ} (ha : 0 < a) (hr : 0 < pairRes a b c) :
    Integrable (gaussExp a b c : EvolutionAmbientState d → ℝ) := by
  have := integrable_phase_prod (d := d) (integrable_exp_neg_pairQ ha hr)
  convert this using 2 with y
  exact gaussExp_eq_prod a b c y

theorem integral_gaussExp {a b c : ℝ} (ha : 0 < a) (hr : 0 < pairRes a b c) :
    ∫ y : EvolutionAmbientState d, gaussExp a b c y =
      (√(π / a) * √(π / pairRes a b c)) ^ d := by
  have := integral_phase_prod (d := d) (fun p : ℝ × ℝ => Real.exp (-pairQ a b c p))
  simp_rw [← gaussExp_eq_prod] at this
  rw [this, integral_exp_neg_pairQ ha hr]

theorem pairQ_nonneg {a b c : ℝ} (ha : 0 < a) (hr : 0 ≤ pairRes a b c) (p : ℝ × ℝ) :
    0 ≤ pairQ a b c p := by
  rw [pairQ_eq ha]; positivity

theorem quadForm_nonneg {a b c : ℝ} (ha : 0 < a) (hr : 0 ≤ pairRes a b c)
    (y : EvolutionAmbientState d) : 0 ≤ quadForm a b c y :=
  Finset.sum_nonneg fun i _ => pairQ_nonneg ha hr (y.1 i, y.2 i)

/-- The Gaussian flow estimates, positivity. -/
theorem flowKernel_pos {lam h : ℝ} (hl : 0 < lam) (hh : 0 < h) (y : EvolutionAmbientState d) :
    0 < flowKernel lam h y := by
  rw [flowKernel_eq hl hh]
  have := flowConst_pos hl hh
  unfold gaussExp
  positivity

/-- The Gaussian flow estimates, total mass one. -/
theorem integral_flowKernel {lam h : ℝ} (hl : 0 < lam) (hh : 0 < h) :
    ∫ y : EvolutionAmbientState d, flowKernel lam h y = 1 := by
  simp_rw [flowKernel_eq hl hh]
  rw [integral_const_mul, integral_gaussExp (flowA_pos hl hh) (flowRes_pos hl hh),
    ← mul_pow, ← one_pow d]
  congr 1
  have h1 : flowConst lam h * (√(π / flowA lam h) * √(π / pairRes (flowA lam h) (flowB lam h)
      (flowC lam h))) = 1 := by
    rw [flowRes_eq hl hh, ← Real.sqrt_mul (by unfold flowA; positivity)]
    unfold flowConst flowA
    have e : π / (6 / (5 * lam * h ^ 3)) * (π / (1 / (2 * lam * h))) =
        (π * lam * h ^ 2) ^ 2 * (5 / 3 : ℝ) := by
      field_simp; ring
    rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    have e2 : √(5 / 3 : ℝ) * √(12 / 5 : ℝ) = 2 := by
      rw [← Real.sqrt_mul (by norm_num)]
      rw [show (5 / 3 * (12 / 5) : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have hπ := Real.pi_pos
    field_simp
    nlinarith [e2]
  rw [h1]

/-- The Gaussian flow estimates, the supremum bound `Φ_h ≤ c_{d,λ} h^{-2d}`. -/
theorem flowKernel_le {lam h : ℝ} (hl : 0 < lam) (hh : 0 < h) (y : EvolutionAmbientState d) :
    flowKernel lam h y ≤ flowSupConstant d lam * h ^ (-(2 * d : ℝ)) := by
  rw [flowKernel_eq hl hh]
  have hg : gaussExp (flowA lam h) (flowB lam h) (flowC lam h) y ≤ 1 := by
    unfold gaussExp
    rw [Real.exp_le_one_iff, neg_nonpos]
    exact quadForm_nonneg (flowA_pos hl hh) (flowRes_pos hl hh).le y
  have hc := flowConst_pos hl hh
  have hle : flowConst lam h ^ d * gaussExp (flowA lam h) (flowB lam h) (flowC lam h) y ≤
      flowConst lam h ^ d := by
    have : 0 ≤ gaussExp (flowA lam h) (flowB lam h) (flowC lam h) y := (Real.exp_pos _).le
    nlinarith [pow_pos hc d]
  refine hle.trans (le_of_eq ?_)
  unfold flowSupConstant flowConst
  have hs : (12 / 5 : ℝ) ^ ((d : ℝ) / 2) = (√(12 / 5 : ℝ)) ^ d := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1; ring
  have h2 : (2 * π) ^ (-(d : ℝ)) = ((2 * π) ^ d)⁻¹ := by
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  have h3 : lam ^ (-(d : ℝ)) = (lam ^ d)⁻¹ := by
    rw [Real.rpow_neg hl.le, Real.rpow_natCast]
  have h4 : h ^ (-(2 * d : ℝ)) = ((h ^ 2) ^ d)⁻¹ := by
    rw [Real.rpow_neg hh.le, ← pow_mul, show (2 * d : ℝ) = ((2 * d : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  rw [hs, h2, h3, h4]
  rw [div_pow, mul_pow, mul_pow]
  field_simp

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

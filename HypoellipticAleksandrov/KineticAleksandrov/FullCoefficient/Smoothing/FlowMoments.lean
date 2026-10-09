module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Flow.Main
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Flow.Coercive

/-!
# Uniform Gaussian moment bounds for the flow kernel

For `0 < a ≤ h ≤ b` the quadratic form of the flow kernel is bounded below by a fixed multiple of
`∑ᵢ (vᵢ² + zᵢ²)`, so the polynomially weighted kernel `(1 + |y|)^k Φ_h` is dominated by one fixed
Gaussian. This gives the local uniformity in `h` of the moment bounds of the Gaussian flow
estimates, which the
abstract kernel family of `Smoothing/Kernel` requires.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open Real MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

theorem flow_pairQ_uniform_coercive {lam a b : ℝ} (hl : 0 < lam) (ha : 0 < a) (hab : a ≤ b) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ, a ≤ h → h ≤ b → ∀ p : ℝ × ℝ,
      ε * (p.1 ^ 2 + p.2 ^ 2) ≤ pairQ (flowA lam h) (flowB lam h) (flowC lam h) p := by
  have hb : 0 < b := ha.trans_le hab
  set A0 : ℝ := 6 / (5 * lam * b ^ 3) with hA0
  set R0 : ℝ := 1 / (2 * lam * b) with hR0
  set T : ℝ := b / 2 with hT
  have hA0p : 0 < A0 := by positivity
  have hR0p : 0 < R0 := by positivity
  have h1 : 0 < 1 + 2 * T ^ 2 := by positivity
  refine ⟨min (A0 / 2) (R0 / (1 + 2 * T ^ 2)), lt_min (by positivity) (by positivity),
    fun h hah hhb p => ?_⟩
  have hh : 0 < h := ha.trans_le hah
  set ε := min (A0 / 2) (R0 / (1 + 2 * T ^ 2)) with hε
  have e1 : ε ≤ A0 / 2 := min_le_left _ _
  have e2 : ε * (1 + 2 * T ^ 2) ≤ R0 := by
    have := min_le_right (A0 / 2) (R0 / (1 + 2 * T ^ 2))
    rw [le_div_iff₀ h1] at this
    exact this
  have hε0 : 0 ≤ ε := (lt_min (by positivity) (by positivity)).le
  have hA : A0 ≤ flowA lam h := by
    unfold flowA
    rw [hA0]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have : h ^ 3 ≤ b ^ 3 := pow_le_pow_left₀ hh.le hhb 3
    nlinarith [mul_pos hl (by norm_num : (0:ℝ) < 5)]
  have hR : R0 ≤ pairRes (flowA lam h) (flowB lam h) (flowC lam h) := by
    rw [flowRes_eq hl hh, hR0]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith
  have ht : flowB lam h / (2 * flowA lam h) = h / 2 := by
    unfold flowA flowB; field_simp
  have hAp := flowA_pos hl hh
  rw [pairQ_eq hAp, ht]
  have ht2 : (h / 2) ^ 2 ≤ T ^ 2 := by
    rw [hT]; exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  set t : ℝ := h / 2 with htdef
  have key : p.2 ^ 2 ≤ 2 * (p.2 + t * p.1) ^ 2 + 2 * t ^ 2 * p.1 ^ 2 := by
    nlinarith [sq_nonneg (p.2 + 2 * t * p.1), sq_nonneg (p.2 + t * p.1), sq_nonneg (t * p.1)]
  have e3 : ε * (1 + 2 * t ^ 2) ≤ pairRes (flowA lam h) (flowB lam h) (flowC lam h) := by
    have : ε * (1 + 2 * t ^ 2) ≤ ε * (1 + 2 * T ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hε0; linarith
    linarith
  have e4 : ε ≤ flowA lam h / 2 := by linarith
  nlinarith [mul_le_mul_of_nonneg_left key hε0, sq_nonneg (p.2 + t * p.1), sq_nonneg p.1,
    mul_nonneg (sub_nonneg.2 e4) (sq_nonneg (p.2 + t * p.1)),
    mul_nonneg (sub_nonneg.2 e3) (sq_nonneg p.1)]

theorem flow_quadForm_uniform_coercive {lam a b : ℝ} (hl : 0 < lam) (ha : 0 < a) (hab : a ≤ b) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ h : ℝ, a ≤ h → h ≤ b → ∀ y : EvolutionAmbientState d,
      ε * ∑ i, (y.1 i ^ 2 + y.2 i ^ 2) ≤ quadForm (flowA lam h) (flowB lam h) (flowC lam h) y := by
  obtain ⟨ε, hε, h⟩ := flow_pairQ_uniform_coercive hl ha hab
  refine ⟨ε, hε, fun h' hah hhb y => ?_⟩
  calc ε * ∑ i, (y.1 i ^ 2 + y.2 i ^ 2) = ∑ i, ε * (y.1 i ^ 2 + y.2 i ^ 2) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ i, pairQ (flowA lam h') (flowB lam h') (flowC lam h') (y.1 i, y.2 i) :=
        Finset.sum_le_sum fun i _ => h h' hah hhb (y.1 i, y.2 i)
    _ = _ := rfl

/-- Uniform domination of the weighted flow kernel by a fixed Gaussian. -/
theorem flow_weighted_le_gaussian {lam a b : ℝ} (hl : 0 < lam) (ha : 0 < a) (hab : a ≤ b) (k : ℕ) :
    ∃ ε M : ℝ, 0 < ε ∧ 0 ≤ M ∧ ∀ h : ℝ, a ≤ h → h ≤ b → ∀ y : EvolutionAmbientState d,
      (1 + ‖y‖) ^ k * flowKernel lam h y ≤ M * gaussExp (ε / 2) 0 (ε / 2) y := by
  obtain ⟨ε, hε, hco⟩ := flow_quadForm_uniform_coercive (d := d) hl ha hab
  obtain ⟨M0, hM0⟩ := pow_mul_exp_neg_le k (t := ε / 2) (by positivity)
  set cmax : ℝ := flowConst lam a with hcm
  have hcmp : 0 < cmax := flowConst_pos hl ha
  have hM0n : 0 ≤ M0 := (by
    have := hM0 0 le_rfl
    simpa using (le_trans (by positivity) this))
  refine ⟨ε, cmax ^ d * M0, hε, by positivity, fun h hah hhb y => ?_⟩
  have hh : 0 < h := ha.trans_le hah
  have hc : flowConst lam h ≤ cmax := by
    unfold flowConst
    rw [hcm]
    unfold flowConst
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have : a ^ 2 ≤ h ^ 2 := pow_le_pow_left₀ ha.le hah 2
    nlinarith [mul_pos (by positivity : (0:ℝ) < 2 * π) hl]
  rw [flowKernel_eq hl hh]
  set S : ℝ := ∑ i, (y.1 i ^ 2 + y.2 i ^ 2) with hS
  have hS0 : ‖y‖ ^ 2 ≤ S := norm_sq_le_sum y
  have hq := hco h hah hhb y
  have hg : gaussExp (ε / 2) 0 (ε / 2) y = exp (-(ε / 2 * S)) := by
    unfold gaussExp quadForm
    congr 1
    rw [hS, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hg]
  have hexp1 : exp (-quadForm (flowA lam h) (flowB lam h) (flowC lam h) y) ≤
      exp (-(ε / 2 * S)) * exp (-(ε / 2 * ‖y‖ ^ 2)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith [hq, hS0, hε]
  have h3 := hM0 ‖y‖ (norm_nonneg y)
  have hK : 0 ≤ flowConst lam h := (flowConst_pos hl hh).le
  have hKd : flowConst lam h ^ d ≤ cmax ^ d := pow_le_pow_left₀ hK hc d
  have hpow : 0 ≤ (1 + ‖y‖) ^ k := by positivity
  calc (1 + ‖y‖) ^ k * (flowConst lam h ^ d * gaussExp (flowA lam h) (flowB lam h) (flowC lam h) y)
      = flowConst lam h ^ d * ((1 + ‖y‖) ^ k *
        exp (-quadForm (flowA lam h) (flowB lam h) (flowC lam h) y)) := by
        unfold gaussExp; ring
    _ ≤ flowConst lam h ^ d * ((1 + ‖y‖) ^ k *
        (exp (-(ε / 2 * S)) * exp (-(ε / 2 * ‖y‖ ^ 2)))) := by gcongr
    _ = flowConst lam h ^ d * (((1 + ‖y‖) ^ k * exp (-(ε / 2 * ‖y‖ ^ 2))) *
        exp (-(ε / 2 * S))) := by ring
    _ ≤ flowConst lam h ^ d * (M0 * exp (-(ε / 2 * S))) := by gcongr
    _ ≤ cmax ^ d * (M0 * exp (-(ε / 2 * S))) := by
        gcongr
    _ = _ := by ring

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

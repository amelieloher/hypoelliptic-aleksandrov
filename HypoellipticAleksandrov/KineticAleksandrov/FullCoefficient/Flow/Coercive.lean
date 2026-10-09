module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Flow.Mass
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Coercivity of the Gaussian quadratic form

For a positive definite pair form `a u² + b u w + c w²` (`a > 0`, `c - b²/(4a) > 0`) there is
`ε > 0` with `quadForm a b c y ≥ ε ‖y‖²`. Combined with the elementary bound
`(1 + r)^m exp (-t r²) ≤ M`, this dominates polynomially weighted Gaussians by a Gaussian with
halved coefficients (used for the integrability statements of the Gaussian flow estimates).
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open Real

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

theorem pairQ_coercive {a b c : ℝ} (ha : 0 < a) (hr : 0 < pairRes a b c) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p : ℝ × ℝ, ε * (p.1 ^ 2 + p.2 ^ 2) ≤ pairQ a b c p := by
  set t : ℝ := b / (2 * a) with ht
  have h1 : 0 < 1 + 2 * t ^ 2 := by positivity
  refine ⟨min (a / 2) (pairRes a b c / (1 + 2 * t ^ 2)), lt_min (by positivity)
    (by positivity), fun p => ?_⟩
  rw [pairQ_eq ha]
  set ε := min (a / 2) (pairRes a b c / (1 + 2 * t ^ 2)) with hε
  have e1 : ε ≤ a / 2 := min_le_left _ _
  have e2 : ε * (1 + 2 * t ^ 2) ≤ pairRes a b c := by
    have := min_le_right (a / 2) (pairRes a b c / (1 + 2 * t ^ 2))
    rw [le_div_iff₀ h1] at this
    exact this
  have key : p.2 ^ 2 ≤ 2 * (p.2 + t * p.1) ^ 2 + 2 * t ^ 2 * p.1 ^ 2 := by
    nlinarith [sq_nonneg (p.2 + 2 * t * p.1), sq_nonneg (p.2 + t * p.1), sq_nonneg (t * p.1)]
  have hε0 : 0 ≤ ε := (lt_min (by positivity) (by positivity)).le
  nlinarith [mul_le_mul_of_nonneg_left key hε0, sq_nonneg (p.2 + t * p.1), sq_nonneg p.1,
    mul_nonneg (sub_nonneg.2 e1) (sq_nonneg (p.2 + t * p.1)),
    mul_nonneg (sub_nonneg.2 e2) (sq_nonneg p.1)]

theorem norm_sq_le_sum (y : EvolutionAmbientState d) :
    ‖y‖ ^ 2 ≤ ∑ i, (y.1 i ^ 2 + y.2 i ^ 2) := by
  set s : ℝ := ∑ i, (y.1 i ^ 2 + y.2 i ^ 2) with hs
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun i _ => by positivity
  have hcoord : ∀ i, y.1 i ^ 2 ≤ s ∧ y.2 i ^ 2 ≤ s := by
    intro i
    have hi : y.1 i ^ 2 + y.2 i ^ 2 ≤ s :=
      Finset.single_le_sum (f := fun i => y.1 i ^ 2 + y.2 i ^ 2)
        (fun j _ => by positivity) (Finset.mem_univ i)
    constructor <;> nlinarith [sq_nonneg (y.1 i), sq_nonneg (y.2 i)]
  have hn : ‖y‖ ≤ √s := by
    rw [Prod.norm_def, max_le_iff]
    constructor
    · refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
      rw [Real.norm_eq_abs]
      exact Real.abs_le_sqrt (hcoord i).1
    · refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
      rw [Real.norm_eq_abs]
      exact Real.abs_le_sqrt (hcoord i).2
  calc ‖y‖ ^ 2 ≤ (√s) ^ 2 := by gcongr
    _ = s := Real.sq_sqrt hs0

theorem quadForm_coercive {a b c : ℝ} (ha : 0 < a) (hr : 0 < pairRes a b c) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y : EvolutionAmbientState d, ε * ‖y‖ ^ 2 ≤ quadForm a b c y := by
  obtain ⟨ε, hε, h⟩ := pairQ_coercive ha hr
  refine ⟨ε, hε, fun y => ?_⟩
  calc ε * ‖y‖ ^ 2 ≤ ε * ∑ i, (y.1 i ^ 2 + y.2 i ^ 2) :=
        mul_le_mul_of_nonneg_left (norm_sq_le_sum y) hε.le
    _ = ∑ i, ε * (y.1 i ^ 2 + y.2 i ^ 2) := by rw [Finset.mul_sum]
    _ ≤ ∑ i, pairQ a b c (y.1 i, y.2 i) := Finset.sum_le_sum fun i _ => h (y.1 i, y.2 i)
    _ = quadForm a b c y := rfl

theorem pow_mul_exp_neg_le (m : ℕ) {t : ℝ} (ht : 0 < t) :
    ∃ M : ℝ, ∀ r : ℝ, 0 ≤ r → (1 + r) ^ m * exp (-(t * r ^ 2)) ≤ M := by
  refine ⟨2 ^ m * (1 + m.factorial / t ^ m), fun r hr => ?_⟩
  have hexp : 0 < exp (-(t * r ^ 2)) := Real.exp_pos _
  have hexp1 : exp (-(t * r ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg r]
  have hpoly : (1 + r) ^ m ≤ 2 ^ m * (1 + (r ^ 2) ^ m) := by
    rcases le_or_gt r 1 with h | h
    · calc (1 + r) ^ m ≤ 2 ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
        _ ≤ 2 ^ m * (1 + (r ^ 2) ^ m) := by
          have : 0 ≤ (r ^ 2) ^ m := by positivity
          nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) m]
    · calc (1 + r) ^ m ≤ (2 * r) ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
        _ = 2 ^ m * r ^ m := mul_pow _ _ _
        _ ≤ 2 ^ m * (r ^ 2) ^ m := by
          gcongr
          nlinarith
        _ ≤ 2 ^ m * (1 + (r ^ 2) ^ m) := by
          gcongr; linarith
  have hfac := Real.pow_div_factorial_le_exp (t * r ^ 2) (by positivity) m
  have hr2 : (r ^ 2) ^ m ≤ m.factorial / t ^ m * exp (t * r ^ 2) := by
    have hfpos : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
    have htm : 0 < t ^ m := by positivity
    rw [mul_pow, div_le_iff₀ hfpos] at hfac
    rw [div_mul_eq_mul_div, le_div_iff₀ htm]
    nlinarith [hfac]
  calc (1 + r) ^ m * exp (-(t * r ^ 2))
      ≤ 2 ^ m * (1 + (r ^ 2) ^ m) * exp (-(t * r ^ 2)) :=
        mul_le_mul_of_nonneg_right hpoly hexp.le
    _ ≤ 2 ^ m * (1 + m.factorial / t ^ m * exp (t * r ^ 2)) * exp (-(t * r ^ 2)) := by
        gcongr
    _ = 2 ^ m * (exp (-(t * r ^ 2)) + m.factorial / t ^ m) := by
        have : exp (t * r ^ 2) * exp (-(t * r ^ 2)) = 1 := by
          rw [← Real.exp_add]; simp
        calc _ = 2 ^ m * (exp (-(t * r ^ 2)) +
              m.factorial / t ^ m * (exp (t * r ^ 2) * exp (-(t * r ^ 2)))) := by ring
          _ = _ := by rw [this]; ring
    _ ≤ 2 ^ m * (1 + m.factorial / t ^ m) := by
        gcongr

theorem pow_norm_mul_gaussExp_le {a b c : ℝ} (ha : 0 < a) (hr : 0 < pairRes a b c) (m : ℕ) :
    ∃ M : ℝ, ∀ y : EvolutionAmbientState d,
      (1 + ‖y‖) ^ m * gaussExp a b c y ≤ M * gaussExp (a / 2) (b / 2) (c / 2) y := by
  obtain ⟨ε, hε, hcoer⟩ := quadForm_coercive (d := d) ha hr
  obtain ⟨M, hM⟩ := pow_mul_exp_neg_le m (t := ε / 2) (by positivity)
  refine ⟨M, fun y => ?_⟩
  have hq : quadForm (a / 2) (b / 2) (c / 2) y = quadForm a b c y / 2 := by
    unfold quadForm
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  unfold gaussExp
  rw [hq]
  have h1 : exp (-quadForm a b c y) = exp (-(quadForm a b c y / 2)) *
      exp (-(quadForm a b c y / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : exp (-(quadForm a b c y / 2)) ≤ exp (-(ε / 2 * ‖y‖ ^ 2)) := by
    apply Real.exp_le_exp.2
    have := hcoer y
    linarith
  have h3 := hM ‖y‖ (norm_nonneg y)
  calc (1 + ‖y‖) ^ m * exp (-quadForm a b c y)
      = ((1 + ‖y‖) ^ m * exp (-(quadForm a b c y / 2))) * exp (-(quadForm a b c y / 2)) := by
        rw [h1]; ring
    _ ≤ ((1 + ‖y‖) ^ m * exp (-(ε / 2 * ‖y‖ ^ 2))) * exp (-(quadForm a b c y / 2)) := by
        gcongr
    _ ≤ M * exp (-(quadForm a b c y / 2)) := by
        gcongr

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

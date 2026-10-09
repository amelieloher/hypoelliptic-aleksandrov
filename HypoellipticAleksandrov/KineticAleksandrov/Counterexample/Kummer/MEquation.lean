module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.Series
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Differential identities for the Kummer series

Coefficient recurrences and differentiation of the convergent series.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

/-- Raising the denominator parameter by one. -/
def next (b : Pos) : Pos := ⟨b.1 + 1, by linarith [b.2]⟩

/-- Left recurrence for the rising factorial. -/
theorem poch_succ_left (a : ℝ) (n : ℕ) : poch a (n + 1) = a * poch (a + 1) n := by
  simp [poch, ascPochhammer_succ_left]

/-- Differentiation recurrence for the coefficients. -/
theorem coeff_deriv (a : ℝ) (b : Pos) (n : ℕ) :
    (n + 1 : ℝ) * coeff a b (n + 1) = (a / b.1) * coeff (a + 1) (next b) n := by
  have hb := ne_of_gt b.2
  have hp := ne_of_gt (poch_pos (next b) n)
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  simp only [coeff, poch_succ_left, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, next]
  field_simp

/-- The coefficient recurrence encoding Kummer's equation. -/
theorem coeff_recurrence (a : ℝ) (b : Pos) (n : ℕ) :
    (n + 1 : ℝ) * (b.1 + n) * coeff a b (n + 1) = (a + n) * coeff a b n := by
  have hp := ne_of_gt (poch_pos b n)
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have hb : b.1 + n ≠ 0 := ne_of_gt
    (add_pos_of_pos_of_nonneg b.2 (Nat.cast_nonneg n))
  simp only [coeff, poch_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one]
  field_simp

/-- The real formal power series has infinite convergence radius. -/
theorem radius_M (a : ℝ) (b : Pos) :
    (FormalMultilinearSeries.ofScalars ℝ (coeff a b)).radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro r
  have hs := (hasSum_M a b (r : ℝ)).summable.norm
  simpa only [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow,
    Real.norm_eq_abs, NNReal.abs_eq] using hs

private theorem series_sum (a : ℝ) (b : Pos) :
    (FormalMultilinearSeries.ofScalars ℝ (coeff a b)).sum = M a b := by
  funext z
  exact FormalMultilinearSeries.ofScalars_sum_eq (coeff a b) z

private theorem derivative_sum (a : ℝ) (b : Pos) (z : ℝ) :
    (FormalMultilinearSeries.ofScalars ℝ (coeff a b)).derivSeries.sum z 1 =
      ∑' n : ℕ, ((n + 1 : ℝ) * coeff a b (n + 1)) * z ^ n := by
  have hz : z ∈ Metric.eball (0 : ℝ)
      (FormalMultilinearSeries.ofScalars ℝ (coeff a b)).derivSeries.radius := by
    have hr := (FormalMultilinearSeries.ofScalars ℝ (coeff a b))
      |>.radius_le_radius_derivSeries
    rw [radius_M] at hr
    have ht := top_le_iff.mp hr
    rw [ht]
    simp
  have hs := ((FormalMultilinearSeries.ofScalars ℝ (coeff a b)).derivSeries.hasSum hz)
    |>.summable
  have hm := (ContinuousLinearMap.apply ℝ ℝ 1).map_tsum hs
  change ((FormalMultilinearSeries.ofScalars ℝ (coeff a b)).derivSeries.sum z) 1 = _
  refine hm.trans ?_
  apply tsum_congr
  intro n
  change ((FormalMultilinearSeries.ofScalars ℝ (coeff a b)).derivSeries n
    (fun _ => z)) 1 = _
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff]
  change z ^ n *
    ((FormalMultilinearSeries.ofScalars ℝ (coeff a b)).derivSeries.coeff n 1) = _
  rw [FormalMultilinearSeries.derivSeries_coeff_one,
    FormalMultilinearSeries.coeff_ofScalars]
  simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  ring

/-- Termwise differentiated series, with a genuine derivative. -/
theorem hasDerivAt_M (a : ℝ) (b : Pos) (z : ℝ) :
    HasDerivAt (M a b) ((a / b.1) * M (a + 1) (next b) z) z := by
  have hz : ‖z‖ₑ < (FormalMultilinearSeries.ofScalars ℝ (coeff a b)).radius := by
    rw [radius_M]
    exact enorm_lt_top
  have hd := ((FormalMultilinearSeries.ofScalars ℝ (coeff a b)).hasFDerivAt_sum hz)
    |>.hasDerivAt
  rw [series_sum, derivative_sum] at hd
  simpa only [coeff_deriv, mul_assoc, tsum_mul_left, M] using hd

/-- The first derivative shifts both Kummer parameters. -/
theorem deriv_M (a : ℝ) (b : Pos) (z : ℝ) :
    deriv (M a b) z = (a / b.1) * M (a + 1) ⟨b.1 + 1, by linarith [b.2]⟩ z :=
  (hasDerivAt_M a b z).deriv

/-- The linear coefficient is the derivative at zero. -/
theorem deriv_M_zero (a : ℝ) (b : Pos) : deriv (M a b) 0 = a / b.1 := by
  rw [deriv_M, M_zero, mul_one]

/-- The second derivative shifts both parameters twice. -/
theorem deriv2_M (a : ℝ) (b : Pos) (z : ℝ) :
    deriv (deriv (M a b)) z =
      (a / b.1) * ((a + 1) / (b.1 + 1)) * M (a + 2) (next (next b)) z := by
  have he : deriv (M a b) = fun x => (a / b.1) * M (a + 1) (next b) x :=
    funext (fun x => (hasDerivAt_M a b x).deriv)
  rw [he, deriv_const_mul_field, deriv_M]
  change a / b.1 * ((a + 1) / (b.1 + 1) * M (a + 1 + 1) (next (next b)) z) = _
  have he2 : a + 1 + 1 = a + 2 := by ring
  rw [he2, mul_assoc]

/-- The first differentiated series. -/
theorem hasSum_deriv_M (a : ℝ) (b : Pos) (z : ℝ) :
    HasSum (fun n : ℕ => (n + 1 : ℝ) * coeff a b (n + 1) * z ^ n)
      (deriv (M a b) z) := by
  rw [(hasDerivAt_M a b z).deriv]
  simpa only [coeff_deriv, mul_assoc] using (hasSum_M (a + 1) (next b) z)
    |>.mul_left (a / b.1)

/-- The twice differentiated series. -/
theorem hasSum_deriv2_M (a : ℝ) (b : Pos) (z : ℝ) :
    HasSum (fun n : ℕ =>
      (n + 1 : ℝ) * (n + 2 : ℝ) * coeff a b (n + 2) * z ^ n)
      (deriv (deriv (M a b)) z) := by
  have hc (n : ℕ) :
      (n + 1 : ℝ) * (n + 2 : ℝ) * coeff a b (n + 2) =
        (a / b.1 * ((a + 1) / (b.1 + 1))) * coeff (a + 2) (next (next b)) n := by
    have h1 := coeff_deriv a b (n + 1)
    have h2 := coeff_deriv (a + 1) (next b) n
    have he : a + 1 + 1 = a + 2 := by ring
    have hn : n + 1 + 1 = n + 2 := by omega
    simp only [Nat.cast_add, Nat.cast_one, hn] at h1
    rw [he] at h2
    calc
      _ = (n + 1 : ℝ) * ((n + 1 + 1 : ℝ) * coeff a b (n + 2)) := by ring
      _ = (n + 1 : ℝ) * ((a / b.1) * coeff (a + 1) (next b) (n + 1)) := by rw [h1]
      _ = (a / b.1) * ((n + 1 : ℝ) * coeff (a + 1) (next b) (n + 1)) := by ring
      _ = _ := by rw [h2, mul_assoc]; rfl

  rw [deriv2_M]
  simpa only [hc, mul_assoc] using (hasSum_M (a + 2) (next (next b)) z)
    |>.mul_left (a / b.1 * ((a + 1) / (b.1 + 1)))

private theorem hasSum_z_deriv (a : ℝ) (b : Pos) (z : ℝ) :
    HasSum (fun n : ℕ => (n : ℝ) * coeff a b n * z ^ n)
      (z * deriv (M a b) z) := by
  have hs := (hasSum_deriv_M a b z).mul_left z
  have he (n : ℕ) : z * ((n + 1 : ℝ) * coeff a b (n + 1) * z ^ n) =
      ((n + 1 : ℕ) : ℝ) * coeff a b (n + 1) * z ^ (n + 1) := by
    simp only [Nat.cast_add, Nat.cast_one, pow_succ]
    ring
  simp only [he] at hs
  simpa only [Nat.cast_zero, zero_mul, zero_add] using
    hs.zero_add (f := fun n : ℕ => (n : ℝ) * coeff a b n * z ^ n)

private theorem hasSum_z_deriv2 (a : ℝ) (b : Pos) (z : ℝ) :
    HasSum (fun n : ℕ => (n : ℝ) * (n + 1 : ℝ) * coeff a b (n + 1) * z ^ n)
      (z * deriv (deriv (M a b)) z) := by
  have hs := (hasSum_deriv2_M a b z).mul_left z
  have he (n : ℕ) : z * ((n + 1 : ℝ) * (n + 2 : ℝ) * coeff a b (n + 2) * z ^ n) =
      ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) + 1 : ℝ) *
        coeff a b ((n + 1) + 1) * z ^ (n + 1) := by
    simp only [Nat.cast_add, Nat.cast_one, pow_succ]
    ring
  simp only [he] at hs
  simpa only [Nat.cast_zero, zero_mul, zero_add] using
    hs.zero_add (f := fun n : ℕ =>
      (n : ℝ) * (n + 1 : ℝ) * coeff a b (n + 1) * z ^ n)

/-- The literal entire power series solves Kummer's differential equation. -/
theorem M_ode (a : ℝ) (b : Pos) (z : ℝ) :
    z * deriv (deriv (M a b)) z + (b.1 - z) * deriv (M a b) z - a * M a b z = 0 := by
  have hl := (hasSum_z_deriv2 a b z).add ((hasSum_deriv_M a b z).mul_left b.1)
  have hr := (hasSum_z_deriv a b z).add ((hasSum_M a b z).mul_left a)
  have he (n : ℕ) :
      (n : ℝ) * (n + 1 : ℝ) * coeff a b (n + 1) * z ^ n +
        b.1 * ((n + 1 : ℝ) * coeff a b (n + 1) * z ^ n) =
      (n : ℝ) * coeff a b n * z ^ n + a * (coeff a b n * z ^ n) := by
    calc
      _ = ((n + 1 : ℝ) * (b.1 + n) * coeff a b (n + 1)) * z ^ n := by ring
      _ = _ := by rw [coeff_recurrence]; ring
  simp only [he] at hl
  have h := hl.unique hr
  linarith only [h]

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

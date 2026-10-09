module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.OriginJetsIntegrability
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Whole-plane integration by parts from regular one-dimensional slices -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set MeasureTheory

/-- Fubini and one-dimensional integration by parts off the null position axis. -/
theorem bellman_integral_slices_second (f g test test' : (ℝ × ℝ) → ℝ)
    (h1 : Integrable (fun q => f q * test' q) volume)
    (h2 : Integrable (fun q => g q * test q) volume)
    (h0 : Integrable (fun q => f q * test q) volume)
    (hf : ∀ X : ℝ, X ≠ 0 → ∀ v : ℝ, HasDerivAt (fun w => f (X, w)) (g (X, v)) v)
    (ht : ∀ X v : ℝ, HasDerivAt (fun w => test (X, w)) (test' (X, v)) v) :
    (∫ q, f q * test' q) = -(∫ q, g q * test q) := by
  rw [Measure.volume_eq_prod] at h1 h2 h0 ⊢
  rw [integral_prod _ h1, integral_prod _ h2, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [volume.ae_ne (0 : ℝ), h1.prod_right_ae,
    h2.prod_right_ae, h0.prod_right_ae] with X hX h1X h2X h0X
  exact integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun v _ => hf X hX v) (fun v _ => ht X v) h1X h2X h0X

/-- Fubini and one-dimensional integration by parts off the null velocity axis. -/
theorem bellman_integral_slices_first (f g test test' : (ℝ × ℝ) → ℝ)
    (h1 : Integrable (fun q => f q * test' q) volume)
    (h2 : Integrable (fun q => g q * test q) volume)
    (h0 : Integrable (fun q => f q * test q) volume)
    (hf : ∀ v : ℝ, v ≠ 0 → ∀ X : ℝ, HasDerivAt (fun Y => f (Y, v)) (g (X, v)) X)
    (ht : ∀ X v : ℝ, HasDerivAt (fun Y => test (Y, v)) (test' (X, v)) X) :
    (∫ q, f q * test' q) = -(∫ q, g q * test q) := by
  rw [Measure.volume_eq_prod] at h1 h2 h0 ⊢
  rw [integral_prod_symm _ h1, integral_prod_symm _ h2, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [volume.ae_ne (0 : ℝ), h1.prod_left_ae,
    h2.prod_left_ae, h0.prod_left_ae] with v hv h1v h2v h0v
  exact integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun X _ => hf v hv X) (fun X _ => ht X v) h1v h2v h0v

/-- The position slice derivative is the literal position jet. -/
theorem bellman_hasDerivAt_first {f : (ℝ × ℝ) → ℝ} {X v : ℝ}
    (hf : DifferentiableAt ℝ f (X, v)) :
    HasDerivAt (fun Y => f (Y, v)) (bellmanDx f (X, v)) X := by
  have hh := hf.hasFDerivAt.comp_hasDerivAt X
    ((hasDerivAt_id X).prodMk (hasDerivAt_const X v))
  simpa only [bellmanDx, Function.comp_def, id_eq] using hh

/-- The velocity slice derivative is the literal velocity jet. -/
theorem bellman_hasDerivAt_second {f : (ℝ × ℝ) → ℝ} {X v : ℝ}
    (hf : DifferentiableAt ℝ f (X, v)) :
    HasDerivAt (fun w => f (X, w)) (bellmanDv f (X, v)) v := by
  have hh := hf.hasFDerivAt.comp_hasDerivAt v
    ((hasDerivAt_const v X).prodMk (hasDerivAt_id v))
  simpa only [bellmanDv, Function.comp_def, id_eq] using hh

end HypoellipticAleksandrov.KineticAleksandrov

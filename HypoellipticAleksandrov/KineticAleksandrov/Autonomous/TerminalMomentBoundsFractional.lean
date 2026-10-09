module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TerminalMomentBounds
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Tactic

/-! # Fractional endpoint moments from the actual terminal second moments -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov MeasureTheory Set Filter
open scoped ENNReal

/-- Subunit nonnegative powers are bounded by one plus their argument. -/
theorem subunit_rpow_le_one_add {p x : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hx : 0 ≤ x) :
    x ^ p ≤ 1+x := by
  by_cases hx1 : x ≤ 1
  · exact (Real.rpow_le_one hx hx1 hp0).trans (by linarith)
  · have h := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx1) hp1
    rw [Real.rpow_one] at h
    linarith

/-- Jensen's inequality for a fractional power, with integrability proved from the first moment. -/
theorem integral_subunit_rpow_le {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (f : Ω → ℝ)
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfi : Integrable f mu)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Integrable (fun x => (f x)^p) mu ∧
      (∫ x, (f x)^p ∂mu) ≤ (∫ x, f x ∂mu)^p := by
  have hpow : Integrable (fun x => (f x)^p) mu := by
    apply Integrable.mono' ((integrable_const (1 : ℝ)).add hfi)
      ((Real.continuous_rpow_const hp0).measurable.comp hf).aestronglyMeasurable
    filter_upwards with x
    change ‖(f x)^p‖ ≤ 1+f x
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (hf0 x) _)]
    exact subunit_rpow_le_one_add hp0 hp1 (hf0 x)
  refine ⟨hpow, ?_⟩
  exact (Real.concaveOn_rpow hp0 hp1).le_map_integral
    (Real.continuous_rpow_const hp0).continuousOn isClosed_Ici
    (Eventually.of_forall hf0) hfi hpow

/-- Fractional powers of displacement are controlled by their second moment. -/
theorem integral_abs_rpow_le_second {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (f : Ω → ℝ) (hf : Measurable f)
    (hfi : Integrable (fun x => (f x)^2) mu) {a : ℝ} (ha0 : 0 ≤ a) (ha2 : a ≤ 2) :
    Integrable (fun x => |f x|^a) mu ∧
      (∫ x, |f x|^a ∂mu) ≤ (∫ x, (f x)^2 ∂mu)^(a/2) := by
  have hp0 : 0 ≤ a/2 := by linarith
  have hp1 : a/2 ≤ 1 := by linarith
  have he (x : Ω) : ((f x)^2)^(a/2) = |f x|^a := by
    rw [← sq_abs, ← Real.rpow_natCast_mul (abs_nonneg _) 2]
    congr 1
    ring
  simpa only [he] using integral_subunit_rpow_le mu (fun x => (f x)^2)
    (hf.pow_const 2) (fun _ => sq_nonneg _) hfi hp0 hp1

/-- Actual canonical velocity fractional moments, with no moment hypothesis. -/
theorem terminal_velocity_fractional_moment
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (z : Z) (T : NNReal)
    {a : ℝ} (ha0 : 0 ≤ a) (ha2 : a ≤ 2) :
    let E := fullSpaceEvolution hH hLE hlam hLam A
    Integrable (fun w : Z => |w.2-z.2|^a) (kernelXV E T z) ∧
      (∫ w, |w.2-z.2|^a ∂kernelXV E T z) ≤ (2*Lam*(T : ℝ))^(a/2) := by
  let E := fullSpaceEvolution hH hLE hlam hLam A
  let : IsProbabilityMeasure (kernelXV E T z) :=
    ⟨kernelXV_mass_one hlam A E (fullSpaceEvolution_spec hH hLE hlam hLam A) T z⟩
  have hi := (terminal_second_moments_integrable hH hLE hlam hLam A z T).1
  obtain ⟨hfi, hle⟩ := integral_abs_rpow_le_second (kernelXV E T z)
    (fun w : Z => w.2-z.2) (by fun_prop) hi ha0 ha2
  refine ⟨hfi, hle.trans ?_⟩
  apply Real.rpow_le_rpow (integral_nonneg (fun _ => sq_nonneg _)) ?_ (by linarith)
  have h := (terminal_second_moments hH hLE hlam hLam A z T).1
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun w : Z => sq_nonneg (w.2-z.2)))] at h
  have hL : 0 ≤ Lam := hlam.le.trans hLam
  have hT := T.property
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

/-- Actual canonical position fractional moments, with no moment hypothesis. -/
theorem terminal_position_fractional_moment
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (z : Z) (T : NNReal)
    {a : ℝ} (ha0 : 0 ≤ a) (ha2 : a ≤ 2) :
    let E := fullSpaceEvolution hH hLE hlam hLam A
    Integrable (fun w : Z => |w.1-z.1|^a) (kernelXV E T z) ∧
      (∫ w, |w.1-z.1|^a ∂kernelXV E T z) ≤
        (2*z.2^2*(T : ℝ)^2+4/3*Lam*(T : ℝ)^3)^(a/2) := by
  let E := fullSpaceEvolution hH hLE hlam hLam A
  let : IsProbabilityMeasure (kernelXV E T z) :=
    ⟨kernelXV_mass_one hlam A E (fullSpaceEvolution_spec hH hLE hlam hLam A) T z⟩
  have hi := (terminal_second_moments_integrable hH hLE hlam hLam A z T).2
  obtain ⟨hfi, hle⟩ := integral_abs_rpow_le_second (kernelXV E T z)
    (fun w : Z => w.1-z.1) (by fun_prop) hi ha0 ha2
  refine ⟨hfi, hle.trans ?_⟩
  apply Real.rpow_le_rpow (integral_nonneg (fun _ => sq_nonneg _)) ?_ (by linarith)
  have h := (terminal_second_moments hH hLE hlam hLam A z T).2
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun w : Z => sq_nonneg (w.1-z.1)))] at h
  have hL : 0 ≤ Lam := hlam.le.trans hLam
  have hT := T.property
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

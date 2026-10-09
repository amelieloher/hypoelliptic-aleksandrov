module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Flow.Bounds
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Flow.Coercive

/-!
# Smoothness and integrability for the flow kernel

The Gaussian flow estimates, smoothness and integrability:
polynomially weighted derivatives of `Φ_h` are integrable.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

theorem contDiff_dirPartial {F : EvolutionAmbientState d → ℝ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (δ : Fin d ⊕ Fin d) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dirPartial δ F) := by
  have h := hF.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)
  exact h.clm_apply contDiff_const

theorem contDiff_iterPartial {F : EvolutionAmbientState d → ℝ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) :
    ∀ l : List (Fin d ⊕ Fin d), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (iterPartial l F)
  | [] => hF
  | δ :: l => contDiff_dirPartial (contDiff_iterPartial hF l) δ

/-- The Gaussian flow estimates: smoothness of the kernel in `y`. -/
theorem flowKernel_contDiff {lam h : ℝ} (hl : 0 < lam) (hh : 0 < h) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (flowKernel lam h : EvolutionAmbientState d → ℝ) := by
  rw [flowKernel_funext hl hh]
  exact contDiff_const.mul (contDiff_gaussExp (flowA lam h) (flowB lam h) (flowC lam h)
    ((⊤ : ℕ∞) : WithTop ℕ∞))

theorem flowKernel_continuous {lam h : ℝ} (hl : 0 < lam) (hh : 0 < h) :
    Continuous (flowKernel lam h : EvolutionAmbientState d → ℝ) :=
  (flowKernel_contDiff hl hh).continuous

theorem iterPartial_flowKernel_continuous {lam h : ℝ} (hl : 0 < lam) (hh : 0 < h)
    (l : List (Fin d ⊕ Fin d)) :
    Continuous (iterPartial l (flowKernel lam h)) :=
  (contDiff_iterPartial (flowKernel_contDiff hl hh) l).continuous

/-- Polynomially weighted integrability of the flow kernel. -/
theorem integrable_pow_mul_flowKernel {lam h : ℝ} (hl : 0 < lam) (hh : 0 < h) (m : ℕ) :
    Integrable (fun y : EvolutionAmbientState d => (1 + ‖y‖) ^ m * flowKernel lam h y) := by
  obtain ⟨M, hM⟩ := pow_norm_mul_gaussExp_le (d := d) (flowA_pos hl hh) (flowRes_pos hl hh) m
  have hres : 0 < pairRes (flowA lam h / 2) (flowB lam h / 2) (flowC lam h / 2) := by
    have hr0 := flowRes_pos hl hh
    unfold pairRes at hr0 ⊢
    have ha := flowA_pos hl hh
    have e : (flowC lam h / 2 - (flowB lam h / 2) ^ 2 / (4 * (flowA lam h / 2))) =
        (flowC lam h - flowB lam h ^ 2 / (4 * flowA lam h)) / 2 := by
      field_simp
    rw [e]; positivity
  have hA2 : 0 < flowA lam h / 2 := by have := flowA_pos hl hh; positivity
  have hint := (integrable_gaussExp (d := d) hA2 hres).const_mul (flowConst lam h ^ d * M)
  refine hint.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
  · exact ((by fun_prop : Continuous fun y : EvolutionAmbientState d => (1 + ‖y‖) ^ m).mul
      (flowKernel_continuous hl hh)).aestronglyMeasurable
  · rw [flowKernel_eq hl hh]
    have hK := pow_pos (flowConst_pos hl hh) d
    have hpos : 0 ≤ (1 + ‖y‖) ^ m * (flowConst lam h ^ d *
        gaussExp (flowA lam h) (flowB lam h) (flowC lam h) y) := by
      have : 0 ≤ gaussExp (flowA lam h) (flowB lam h) (flowC lam h) y := (Real.exp_pos _).le
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hpos]
    calc (1 + ‖y‖) ^ m * (flowConst lam h ^ d *
          gaussExp (flowA lam h) (flowB lam h) (flowC lam h) y)
        = flowConst lam h ^ d * ((1 + ‖y‖) ^ m *
          gaussExp (flowA lam h) (flowB lam h) (flowC lam h) y) := by ring
      _ ≤ flowConst lam h ^ d * (M * gaussExp (flowA lam h / 2) (flowB lam h / 2)
          (flowC lam h / 2) y) := mul_le_mul_of_nonneg_left (hM y) hK.le
      _ = _ := by ring

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

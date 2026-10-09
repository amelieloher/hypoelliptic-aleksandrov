module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Flow.IterBounds

/-!
# Pointwise derivative bounds for the flow kernel

The Gaussian flow estimates: for every word `l` of coordinate
directions there is a constant `C`, uniform in `h ∈ [a, ∞)`, with
`|∂^l Φ_h(y)| ≤ C (1 + ‖y‖)^{|l|} Φ_h(y)`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

theorem flowCoef_mem {lam a h : ℝ} (hl : 0 < lam) (ha : 0 < a) (hah : a ≤ h) :
    (flowA lam h, flowB lam h, flowC lam h) ∈
      Coef (flowA lam a + flowB lam a + flowC lam a) := by
  have hh : 0 < h := ha.trans_le hah
  have hA : flowA lam h ≤ flowA lam a := by unfold flowA; gcongr
  have hB : flowB lam h ≤ flowB lam a := by unfold flowB; gcongr
  have hC : flowC lam h ≤ flowC lam a := by unfold flowC; gcongr
  have pA := flowA_pos hl hh
  have pa := flowA_pos hl ha
  have pB : 0 < flowB lam h := by unfold flowB; positivity
  have pb : 0 < flowB lam a := by unfold flowB; positivity
  have pC : 0 < flowC lam h := by unfold flowC; positivity
  have pc : 0 < flowC lam a := by unfold flowC; positivity
  refine ⟨?_, ?_, ?_⟩ <;> simp only [abs_of_pos pA, abs_of_pos pB, abs_of_pos pC] <;> linarith

/-- The Gaussian flow estimates: derivative bounds, uniform for `h ≥ a`. -/
theorem flowKernel_iterPartial_bound {lam a : ℝ} (hl : 0 < lam) (ha : 0 < a)
    (l : List (Fin d ⊕ Fin d)) :
    ∃ C : ℝ, ∀ h : ℝ, a ≤ h → ∀ y : EvolutionAmbientState d,
      |iterPartial l (flowKernel lam h) y| ≤ C * (1 + ‖y‖) ^ l.length * flowKernel lam h y := by
  obtain ⟨P, hP, hE⟩ := iterPartial_gaussExp (d := d)
    (flowA lam a + flowB lam a + flowC lam a) l
  obtain ⟨C, hC⟩ := hP.bound
  refine ⟨C, fun h hah y => ?_⟩
  have hh : 0 < h := ha.trans_le hah
  have hθ := flowCoef_mem hl ha hah
  have e := congrFun (hE _ hθ (flowConst lam h ^ d)) y
  conv_lhs => rw [flowKernel_funext hl hh]
  have e2 : iterPartial l (fun y => flowConst lam h ^ d *
      gaussExp (flowA lam h) (flowB lam h) (flowC lam h) y) y =
      flowConst lam h ^ d * P (flowA lam h, flowB lam h, flowC lam h) y *
        gaussExp (flowA lam h) (flowB lam h) (flowC lam h) y := e
  rw [e2]
  rw [flowKernel_eq hl hh]
  have hK := pow_pos (flowConst_pos hl hh) d
  have hG : 0 < gaussExp (flowA lam h) (flowB lam h) (flowC lam h) y := Real.exp_pos _
  have hb := hC _ hθ y
  calc |flowConst lam h ^ d * P (flowA lam h, flowB lam h, flowC lam h) y *
        gaussExp (flowA lam h) (flowB lam h) (flowC lam h) y|
      = |P (flowA lam h, flowB lam h, flowC lam h) y| *
        (flowConst lam h ^ d * gaussExp (flowA lam h) (flowB lam h) (flowC lam h) y) := by
        rw [abs_mul, abs_mul, abs_of_pos hK, abs_of_pos hG]; ring
    _ ≤ C * (1 + ‖y‖) ^ l.length *
        (flowConst lam h ^ d * gaussExp (flowA lam h) (flowB lam h) (flowC lam h) y) :=
        mul_le_mul_of_nonneg_right hb (by positivity)

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

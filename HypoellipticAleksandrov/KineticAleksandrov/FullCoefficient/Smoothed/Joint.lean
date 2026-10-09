module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothed.Product

/-!
# Joint smoothness of the time-averaged smoothings

The smoothed equation: `ρ` and `J` are smooth in `(τ, y)`, and the `τ`-derivative of `ρ` may
be taken under the integral sign.  Here `timeSmoothed Φ η h f Γ'` is the function
`(τ, y) ↦ ∫ f(t, y') η_δ(τ - t) Φ_h(y - y') dΓ'(t, y')`; the density has `f = 1` and the flux
entries have `f = B_{ij}`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open MeasureTheory Set

variable {d : ℕ} {δ : ℝ} {η : ℝ → ℝ} {lam : ℝ}

/-- `(τ, y) ↦ ∫ f(a) η(τ - a₁) Φ_h(y - a₂) dΓ'(a)`. -/
def timeSmoothed (Φ : SmoothingKernelFamily d lam) (η : ℝ → ℝ) (h : ℝ)
    (f : ℝ × EvolutionAmbientState d → ℝ) (Γ' : Measure (ℝ × EvolutionAmbientState d))
    (p : ℝ × EvolutionAmbientState d) : ℝ :=
  ∫ a, f a * (η (p.1 - a.1) * Φ.kernel h (p.2 - a.2)) ∂Γ'

variable (Φ : SmoothingKernelFamily d lam) {h : ℝ} {Γ' : Measure (ℝ × EvolutionAmbientState d)}
  [IsFiniteMeasure Γ'] {f : ℝ × EvolutionAmbientState d → ℝ} {Cf : ℝ}

omit [IsFiniteMeasure Γ'] in
theorem timeSmoothed_eq_wconv :
    timeSmoothed Φ η h f Γ' =
      wconv (fun p : ℝ × EvolutionAmbientState d => η p.1 * Φ.kernel h p.2) f Γ' := by
  funext p
  simp [timeSmoothed, wconv]

/-- **Joint smoothness** of the time-averaged smoothings. -/
theorem contDiff_timeSmoothed (hη : IsMollifier δ η) (hh : 0 < h) (hf : Measurable f)
    (hfb : ∀ a, |f a| ≤ Cf) :
    ContDiff ℝ (⊤ : ℕ∞) (timeSmoothed Φ η h f Γ') := by
  rw [timeSmoothed_eq_wconv Φ]
  exact contDiff_wconv (isBoundedSmooth_timeKernel hη Φ hh) hf hfb Γ'

/-- The `τ`-derivative of the time-averaged smoothing, under the integral sign. -/
theorem hasDerivAt_timeSmoothed (hη : IsMollifier δ η) (hh : 0 < h) (hf : Measurable f)
    (hfb : ∀ a, |f a| ≤ Cf) (τ : ℝ) (y : EvolutionAmbientState d) :
    HasDerivAt (fun τ' => timeSmoothed Φ η h f Γ' (τ', y))
      (∫ a, f a * (deriv η (τ - a.1) * Φ.kernel h (y - a.2)) ∂Γ') τ := by
  obtain ⟨C1, hC1⟩ := hη.exists_bound
  obtain ⟨C2, hC2⟩ := hη.exists_bound_deriv
  obtain ⟨C3, -, hC3⟩ := Φ.exists_sup_bound (K := {h}) isCompact_singleton (by simpa using hh)
  have hΦc : Continuous fun a : ℝ × EvolutionAmbientState d => Φ.kernel h (y - a.2) :=
    (Φ.contDiff hh).continuous.comp (continuous_const.sub continuous_snd)
  have hηc : ∀ τ' : ℝ, Continuous fun a : ℝ × EvolutionAmbientState d => η (τ' - a.1) :=
    fun τ' => hη.continuous.comp (continuous_const.sub continuous_fst)
  have hη'c : ∀ τ' : ℝ, Continuous fun a : ℝ × EvolutionAmbientState d => deriv η (τ' - a.1) :=
    fun τ' => hη.contDiff_deriv.continuous.comp (continuous_const.sub continuous_fst)
  have hfm := hf.aestronglyMeasurable (μ := Γ')
  have hmeas : ∀ τ', AEStronglyMeasurable
      (fun a : ℝ × EvolutionAmbientState d => f a * (η (τ' - a.1) * Φ.kernel h (y - a.2))) Γ' :=
    fun τ' => hfm.mul (((hηc τ').mul hΦc).aestronglyMeasurable)
  have hmeas' : AEStronglyMeasurable
      (fun a : ℝ × EvolutionAmbientState d => f a * (deriv η (τ - a.1) * Φ.kernel h (y - a.2)))
      Γ' := hfm.mul (((hη'c τ).mul hΦc).aestronglyMeasurable)
  have hC3' : ∀ a : ℝ × EvolutionAmbientState d, |Φ.kernel h (y - a.2)| ≤ C3 := fun a => by
    rw [abs_of_pos (Φ.pos hh _)]; exact hC3 h rfl _
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := Γ')
    (F := fun (τ' : ℝ) (a : ℝ × EvolutionAmbientState d) =>
      f a * (η (τ' - a.1) * Φ.kernel h (y - a.2)))
    (F' := fun (τ' : ℝ) (a : ℝ × EvolutionAmbientState d) =>
      f a * (deriv η (τ' - a.1) * Φ.kernel h (y - a.2))) (x₀ := τ)
    (bound := fun _ => Cf * (C2 * C3)) (s := univ) Filter.univ_mem
    (Filter.Eventually.of_forall hmeas) ?_ hmeas' ?_ (integrable_const _) ?_
  · exact key.2
  · refine Integrable.of_bound (hmeas τ) (Cf * (C1 * C3)) (Filter.Eventually.of_forall fun a => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    exact mul_le_mul (hfb a) (mul_le_mul (hC1 _) (hC3' a) (abs_nonneg _)
      ((abs_nonneg _).trans (hC1 (τ - a.1)))) (by positivity) ((abs_nonneg _).trans (hfb a))
  · refine Filter.Eventually.of_forall fun a τ' _ => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    exact mul_le_mul (hfb a) (mul_le_mul (hC2 _) (hC3' a) (abs_nonneg _)
      ((abs_nonneg _).trans (hC2 (τ' - a.1)))) (by positivity) ((abs_nonneg _).trans (hfb a))
  · refine Filter.Eventually.of_forall fun a τ' _ => ?_
    have h1 : HasDerivAt (fun x : ℝ => η (x - a.1)) (deriv η (τ' - a.1)) τ' := by
      simpa using (hη.hasDerivAt (τ' - a.1)).comp_sub_const τ' a.1
    exact (h1.mul_const _).const_mul _

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

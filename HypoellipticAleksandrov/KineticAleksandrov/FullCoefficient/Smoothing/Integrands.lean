module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Targets

/-!
# The integrands of the smoothing estimates: integrability and uniform bounds

The smoothing estimates: with `r = m_h`, `β = (Fm)_h / m_h`,
`J = (Fm)_h` and `1 < q ≤ 2`, the ten functions
`r^q, r^q |β|², r^{q-1} |Dr|, r^{q-1} |D²r|, r^{q-2} |Dr|², r^q |Dβ|, r^{q-1} |DJ|, r^{q-1} |D²J|,
r^{q-2} |DJ|², r^{q-1} |Dr| |Dβ|` are integrable, with integrals bounded in terms of the mass of `m`
and a compact set of the parameter `h` only.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ} {lam : ℝ} (Φ : SmoothingKernelFamily d lam) (h : ℝ)
  (F : EvolutionAmbientState d → PDE.Mat d) (m : Measure (EvolutionAmbientState d)) (q : ℝ)

/-- `r^q`. -/
def integrandPow (y : EvolutionAmbientState d) : ℝ := smoothDensity Φ h m y ^ q

/-- `r^q |β|²`. -/
def integrandPowBeta (y : EvolutionAmbientState d) : ℝ :=
  smoothDensity Φ h m y ^ q * frobeniusSq (smoothCoefficient Φ h F m y)

/-- `r^{q-1} |Dr|`. -/
def integrandGrad (y : EvolutionAmbientState d) : ℝ :=
  smoothDensity Φ h m y ^ (q - 1) * gradNorm (smoothDensity Φ h m) y

/-- `r^{q-1} |D²r|`. -/
def integrandHess (y : EvolutionAmbientState d) : ℝ :=
  smoothDensity Φ h m y ^ (q - 1) * hessNorm (smoothDensity Φ h m) y

/-- `r^{q-2} |Dr|²`. -/
def integrandFisher (y : EvolutionAmbientState d) : ℝ :=
  smoothDensity Φ h m y ^ (q - 2) * gradNormSq (smoothDensity Φ h m) y

/-- `r^q |Dβ|`. -/
def integrandBetaGrad (y : EvolutionAmbientState d) : ℝ :=
  smoothDensity Φ h m y ^ q * coefficientGradNorm (smoothCoefficient Φ h F m) y

/-- `r^{q-1} |DJ|` with `J = (Fm)_h`. -/
def integrandFluxGrad (y : EvolutionAmbientState d) : ℝ :=
  smoothDensity Φ h m y ^ (q - 1) * coefficientGradNorm (smoothFlux Φ h F m) y

/-- `r^{q-1} |D²J|`. -/
def integrandFluxHess (y : EvolutionAmbientState d) : ℝ :=
  smoothDensity Φ h m y ^ (q - 1) * coefficientHessNorm (smoothFlux Φ h F m) y

/-- `r^{q-2} |DJ|²`. -/
def integrandFluxFisher (y : EvolutionAmbientState d) : ℝ :=
  smoothDensity Φ h m y ^ (q - 2) * coefficientGradNormSq (smoothFlux Φ h F m) y

/-- `r^{q-1} |Dr| |Dβ|`. -/
def integrandMixed (y : EvolutionAmbientState d) : ℝ :=
  smoothDensity Φ h m y ^ (q - 1) * gradNorm (smoothDensity Φ h m) y *
    coefficientGradNorm (smoothCoefficient Φ h F m) y

variable {Φ h F m q}

section Master

variable {T : EvolutionAmbientState d → ℝ} [IsFiniteMeasure m]

theorem integrable_of_le_smoothWeight2 (hh : 0 < h) (hT : Continuous T) (h0 : ∀ y, 0 ≤ T y)
    {A : ℝ} (hA : ∀ y, T y ≤ A * smoothWeight2 Φ h m y) :
    Integrable T ∧ ∫ y, T y ≤ A * (m.real Set.univ * ∫ z, weight2 Φ h z) := by
  have hint : Integrable T := by
    refine ((integrable_smoothWeight2 (Φ := Φ) m hh).const_mul A).mono' hT.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 y)]
    exact hA y
  refine ⟨hint, ?_⟩
  calc ∫ y, T y ≤ ∫ y, A * smoothWeight2 Φ h m y :=
        integral_mono hint ((integrable_smoothWeight2 (Φ := Φ) m hh).const_mul A) hA
    _ = _ := by rw [integral_const_mul, integral_smoothWeight2 (Φ := Φ) m hh]

end Master

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

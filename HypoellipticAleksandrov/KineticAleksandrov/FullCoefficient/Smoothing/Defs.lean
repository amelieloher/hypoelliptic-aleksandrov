module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Kernel
public import HypoellipticAleksandrov.Coefficients.Ellipticity

/-!
# Smoothing of finite measures: definitions

definition the smoothing operation. For a finite measure `m` on phase
space `y = (v, z)` and a bounded measurable matrix field `F`,
`m_h(y) = ∫ Φ_h(y - y') dm(y')` and `(Fm)_h(y) = ∫ Φ_h(y - y') F(y') dm(y')`, and
`β_h = (Fm)_h / m_h` (or `λ I` when `m = 0`). The flux is defined entrywise.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory
open scoped MatrixOrder

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ} {lam : ℝ}

/-- A measurable symmetric matrix field with two-sided Loewner bounds `lam I ≤ F ≤ Lam I`, the
hypothesis on `F` in the smoothing estimates. -/
structure IsAdmissibleCoefficient (lam Lam : ℝ) (F : EvolutionAmbientState d → PDE.Mat d) :
    Prop where
  measurable : ∀ i j, Measurable fun y => F y i j
  symm : ∀ y, (F y).IsSymm
  lower : ∀ y, lam • (1 : PDE.Mat d) ≤ F y
  upper : ∀ y, F y ≤ Lam • (1 : PDE.Mat d)

/-- The smoothed density `m_h(y) = ∫ Φ_h(y - y') dm(y')`. -/
def smoothDensity (Φ : SmoothingKernelFamily d lam) (h : ℝ)
    (m : Measure (EvolutionAmbientState d)) (y : EvolutionAmbientState d) : ℝ :=
  ∫ y', Φ.kernel h (y - y') ∂m

/-- The `(i, j)` entry of the smoothed flux `(Fm)_h(y) = ∫ Φ_h(y - y') F(y') dm(y')`. -/
def smoothFluxEntry (Φ : SmoothingKernelFamily d lam) (h : ℝ)
    (F : EvolutionAmbientState d → PDE.Mat d) (m : Measure (EvolutionAmbientState d))
    (i j : Fin d) (y : EvolutionAmbientState d) : ℝ :=
  ∫ y', Φ.kernel h (y - y') * F y' i j ∂m

/-- The smoothed flux `(Fm)_h`, defined entrywise. -/
def smoothFlux (Φ : SmoothingKernelFamily d lam) (h : ℝ)
    (F : EvolutionAmbientState d → PDE.Mat d) (m : Measure (EvolutionAmbientState d))
    (y : EvolutionAmbientState d) : PDE.Mat d :=
  Matrix.of fun i j => smoothFluxEntry Φ h F m i j y

open Classical in
/-- The smoothed coefficient `β_h = (Fm)_h / m_h`, equal to `lam I` when `m = 0`. -/
def smoothCoefficient (Φ : SmoothingKernelFamily d lam) (h : ℝ)
    (F : EvolutionAmbientState d → PDE.Mat d) (m : Measure (EvolutionAmbientState d))
    (y : EvolutionAmbientState d) : PDE.Mat d :=
  if m = 0 then lam • (1 : PDE.Mat d) else (smoothDensity Φ h m y)⁻¹ • smoothFlux Φ h F m y

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

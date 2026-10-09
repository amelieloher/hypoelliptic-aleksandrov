module

public import HypoellipticAleksandrov.KineticAleksandrov.MovingKernel
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Coordinate derivatives on phase space

Phase-space points are `y = (v, z) : EvolutionAmbientState d`, velocity first, as in the terminal
solution operator. This module fixes the coordinate partial derivatives and the second-order
operators used throughout the full-coefficient Aleksandrov estimate: velocity and position partials,
the velocity Hessian contraction
`B : D_v² F`, the transport derivative `v · ∇_z F`, the two Laplacians and the mixed operator
`∇_z · ∇_v`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

/-- The `i`-th velocity partial derivative of a function on phase space `(v, z)`. -/
def velocityPartial (i : Fin d) (F : EvolutionAmbientState d → ℝ)
    (y : EvolutionAmbientState d) : ℝ :=
  fderiv ℝ F y (Pi.single i 1, 0)

/-- The `i`-th position partial derivative of a function on phase space `(v, z)`. -/
def positionPartial (i : Fin d) (F : EvolutionAmbientState d → ℝ)
    (y : EvolutionAmbientState d) : ℝ :=
  fderiv ℝ F y (0, Pi.single i 1)

/-- The velocity Hessian contraction `B : D_v² F = ∑ᵢⱼ Bᵢⱼ ∂_{vᵢ} ∂_{vⱼ} F`. -/
def velocityHessianContraction (B : PDE.Mat d) (F : EvolutionAmbientState d → ℝ)
    (y : EvolutionAmbientState d) : ℝ :=
  ∑ i, ∑ j, B i j * velocityPartial i (velocityPartial j F) y

/-- The transport derivative `v · ∇_z F` at `y = (v, z)`. -/
def transportDerivative (F : EvolutionAmbientState d → ℝ)
    (y : EvolutionAmbientState d) : ℝ :=
  ∑ i, y.1 i * positionPartial i F y

/-- The velocity Laplacian `Δ_v F`. -/
def velocityLaplacian (F : EvolutionAmbientState d → ℝ) (y : EvolutionAmbientState d) : ℝ :=
  ∑ i, velocityPartial i (velocityPartial i F) y

/-- The position Laplacian `Δ_z F`. -/
def positionLaplacian (F : EvolutionAmbientState d → ℝ) (y : EvolutionAmbientState d) : ℝ :=
  ∑ i, positionPartial i (positionPartial i F) y

/-- The mixed operator `∇_z · ∇_v F = ∑ᵢ ∂_{zᵢ} ∂_{vᵢ} F`. -/
def mixedDivergence (F : EvolutionAmbientState d → ℝ) (y : EvolutionAmbientState d) : ℝ :=
  ∑ i, positionPartial i (velocityPartial i F) y

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

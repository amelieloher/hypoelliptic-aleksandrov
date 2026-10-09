module

public import HypoellipticAleksandrov.Parabolic.Geometry
public import HypoellipticAleksandrov.Parabolic.SpatialCoordinateDerivatives

/-!
# Localized spatial gradient divergence

This file records the transparent localized divergence expression used in the
weak gradient time-energy identity.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.WeakGradientTimeEnergy

/-- The localized negative spatial divergence built from selected weak
gradient and diagonal Hessian representatives. -/
def localizedGradientDivergence
    {d : ℕ}
    (η : PDE.Vec d → ℝ)
    (QG : TimeVelocity d → PDE.Vec d)
    (QH : TimeVelocity d → PDE.Mat d)
    (z : TimeVelocity d) : ℝ :=
  -∑ i : Fin d,
    (2 * η z.2 * spatialPartial i η z.2 * QG z i +
      η z.2 ^ 2 * QH z i i)

end HypoellipticAleksandrov.Parabolic.WeakGradientTimeEnergy

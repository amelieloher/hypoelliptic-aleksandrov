module

public import PDEFoundation.Ambient.EuclideanNorm

@[expose] public section

open scoped Matrix

/-!
# Ellipsoidal Dirichlet domains

This module records the literal open ellipsoid used as the smooth bounded
spatial base for the classical Dirichlet theorem.
-/

namespace HypoellipticAleksandrov.KineticAleksandrov

/-- The open ellipsoid associated with a real square matrix. -/
def openEllipsoid {N : ℕ} (Q : PDE.Mat N) : Set (PDE.Vec N) :=
  {x | PDE.vecDot x (Q *ᵥ x) < 1}

end HypoellipticAleksandrov.KineticAleksandrov

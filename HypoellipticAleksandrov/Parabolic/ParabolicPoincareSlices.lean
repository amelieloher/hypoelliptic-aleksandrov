module

public import HypoellipticAleksandrov.Parabolic.ParabolicPoincareFoundation

/-!
# Time-slice parabolic moment projections

This module fixes the canonical velocity-cube moment-affine projection at each
time separately. It contains only the shared definitions used by the spatial
and temporal parabolic Poincare estimates.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped BigOperators

/-- The normalized velocity-cube average at a fixed time. -/
noncomputable def parabolicMorreyUnitVelocityAverage {d : Nat}
    (u : TimeVelocity d -> Real) (t : Real) : Real :=
  ((volume (velocityCube (0 : PDE.Vec d) 1)).toReal)⁻¹ *
    ∫ v in velocityCube 0 1, u (t, v)

/-- The normalized `i`th velocity moment coefficient at a fixed time. -/
noncomputable def parabolicMorreyUnitVelocityCoeffAt {d : Nat}
    (u : TimeVelocity d -> Real) (t : Real) (i : Fin d) : Real :=
  3 * ((volume (velocityCube (0 : PDE.Vec d) 1)).toReal)⁻¹ *
    ∫ v in velocityCube 0 1, u (t, v) * v i

/-- The canonical moment-affine velocity projection, performed separately at
each time. -/
noncomputable def parabolicMorreyUnitSpatialAffineProjection {d : Nat}
    (u : TimeVelocity d -> Real) : TimeVelocity d -> Real :=
  fun z => parabolicMorreyUnitVelocityAverage u z.1 +
    ∑ i : Fin d, parabolicMorreyUnitVelocityCoeffAt u z.1 i * z.2 i

end HypoellipticAleksandrov.Parabolic

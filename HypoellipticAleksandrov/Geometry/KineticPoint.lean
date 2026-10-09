module

public import Mathlib.Topology.MetricSpace.Isometry
public import PDEFoundation.Ambient.Basic

/-!
# Kinetic spacetime points

This module gives an explicit carrier for kinetic spacetime. Its fields make
the time, position, and velocity coordinate order visible in every theorem
surface.

## Main definitions

* `KineticPoint d` is a kinetic spacetime point with time, position, and
  velocity coordinates.
* `KineticPoint.homeomorphProd d` identifies this explicit carrier with
  `ℝ × (PDE.Vec d × PDE.Vec d)` for standard topology infrastructure.

## Implementation note

The transported product metric supplies only the ordinary topology and
uniformity used by sets, continuity, and compactness. It is not the
manuscript's Euclidean kinetic geometry; Euclidean norms and balls must use
the explicit `PDEFoundation` API.
-/

@[expose] public section

namespace HypoellipticAleksandrov

/-- A point of kinetic spacetime in dimension `d`. -/
@[ext]
structure KineticPoint (d : ℕ) where
  /-- Time coordinate. -/
  time : ℝ
  /-- Position coordinate. -/
  position : PDE.Vec d
  /-- Velocity coordinate. -/
  velocity : PDE.Vec d

/-- The explicit coordinate equivalence with the standard nested product carrier. -/
def KineticPoint.equivProd (d : ℕ) :
    KineticPoint d ≃ ℝ × (PDE.Vec d × PDE.Vec d) where
  toFun z := (z.time, (z.position, z.velocity))
  invFun z := ⟨z.1, z.2.1, z.2.2⟩
  left_inv z := by
    ext <;> rfl
  right_inv z := by
    rcases z with ⟨t, x, v⟩
    rfl

/-- The standard product metric transported to the explicit coordinate carrier.

This is only topology and uniformity infrastructure, not manuscript round
Euclidean geometry. -/
instance (d : ℕ) : MetricSpace (KineticPoint d) :=
  MetricSpace.induced (KineticPoint.equivProd d)
    (KineticPoint.equivProd d).injective inferInstance

/-- The coordinate equivalence is an isometry for the transported standard product metric. -/
def KineticPoint.isometryEquivProd (d : ℕ) :
    KineticPoint d ≃ᵢ ℝ × (PDE.Vec d × PDE.Vec d) where
  toEquiv := KineticPoint.equivProd d
  isometry_toFun :=
    MetricSpace.isometry_induced (KineticPoint.equivProd d)
      (KineticPoint.equivProd d).injective

/-- The explicit coordinate homeomorphism with the standard nested product carrier. -/
def KineticPoint.homeomorphProd (d : ℕ) :
    KineticPoint d ≃ₜ ℝ × (PDE.Vec d × PDE.Vec d) :=
  (KineticPoint.isometryEquivProd d).toHomeomorph

/-- The time projection is continuous for the standard product topology. -/
theorem continuous_time {d : ℕ} : Continuous (@KineticPoint.time d) :=
  continuous_fst.comp (KineticPoint.homeomorphProd d).continuous

/-- The position projection is continuous for the standard product topology. -/
theorem continuous_position {d : ℕ} : Continuous (@KineticPoint.position d) :=
  continuous_snd.fst.comp (KineticPoint.homeomorphProd d).continuous

/-- The velocity projection is continuous for the standard product topology. -/
theorem continuous_velocity {d : ℕ} : Continuous (@KineticPoint.velocity d) :=
  continuous_snd.snd.comp (KineticPoint.homeomorphProd d).continuous

/-- Assemble a continuous kinetic point from continuous coordinate functions. -/
theorem KineticPoint.continuous_mk
    {α : Type*} [TopologicalSpace α] {d : ℕ}
    {t : α → ℝ} {x v : α → PDE.Vec d}
    (ht : Continuous t) (hx : Continuous x) (hv : Continuous v) :
    Continuous (fun a => KineticPoint.mk (t a) (x a) (v a)) :=
  (KineticPoint.homeomorphProd d).symm.continuous.comp (ht.prodMk (hx.prodMk hv))

/-- Assemble a continuous curve from its time, position, and velocity coordinate curves. -/
theorem continuous_kinetic_curve {d : ℕ} {t : ℝ → ℝ}
    {x v : ℝ → PDE.Vec d} (ht : Continuous t) (hx : Continuous x) (hv : Continuous v) :
    Continuous (fun r : ℝ => KineticPoint.mk (t r) (x r) (v r)) :=
  KineticPoint.continuous_mk ht hx hv

end HypoellipticAleksandrov

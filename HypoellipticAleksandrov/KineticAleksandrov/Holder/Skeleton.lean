module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Setting
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.ProjIcc

/-!
# Compatible kinetic skeletons

A skeleton has position derivative equal to velocity and an acceleration bound expressed
as a Euclidean Lipschitz bound. Endpoint-constant extension of velocity preserves that bound.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set

/-- Position and velocity compatibility with Euclidean acceleration bound on a closed interval. -/
def IsSkeleton {d : ℕ} (x v : ℝ → PDE.Vec d) (H a b : ℝ) : Prop :=
  ContinuousOn v (Icc a b) ∧
  (∀ s ∈ Icc a b, HasDerivWithinAt x (v s) (Icc a b) s) ∧
  (∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
    PDE.vecEuclideanNorm (v s - v t) ≤ H * |s - t|)

/-- A closed position–velocity corridor around a compatible path. -/
def corridor {d : ℕ} (tminus a b kx kv : ℝ) (x v : ℝ → PDE.Vec d) :
    Set (KineticPoint d) :=
  {P | P.time - tminus ∈ Icc a b ∧
    PDE.vecEuclideanNorm (P.position - x (P.time - tminus)) ≤ kx ∧
    PDE.vecEuclideanNorm (P.velocity - v (P.time - tminus)) ≤ kv}

/-- A skeleton's position is continuous on its defining interval. -/
theorem IsSkeleton.continuousOn_position {d : ℕ} {x v : ℝ → PDE.Vec d}
    {H a b : ℝ} (hx : IsSkeleton x v H a b) : ContinuousOn x (Icc a b) :=
  fun s hs => (hx.2.1 s hs).continuousWithinAt

/-- Endpoint-constant extension of the velocity of a skeleton. -/
noncomputable def extendVelocity {d : ℕ} (v : ℝ → PDE.Vec d) (a b : ℝ) (hab : a ≤ b) :
    ℝ → PDE.Vec d := fun s => v (projIcc a b hab s)

/-- The extension agrees with the original velocity on the closed interval. -/
theorem extendVelocity_eq {d : ℕ} (v : ℝ → PDE.Vec d) {a b : ℝ}
    (hab : a ≤ b) {s : ℝ} (hs : s ∈ Icc a b) :
    extendVelocity v a b hab s = v s := by
  simp only [extendVelocity, projIcc_of_mem hab hs]

/-- Extending velocity by endpoint constants preserves continuity. -/
theorem continuous_extendVelocity {d : ℕ} {v : ℝ → PDE.Vec d} {a b : ℝ}
    (hab : a ≤ b) (hv : ContinuousOn v (Icc a b)) :
    Continuous (extendVelocity v a b hab) :=
  hv.domRestrict.comp continuous_projIcc

/-- Extending velocity by endpoint constants preserves the Euclidean Lipschitz constant. -/
theorem extendVelocity_lipschitz {d : ℕ} {x v : ℝ → PDE.Vec d} {H a b : ℝ}
    (hab : a ≤ b) (hH : 0 ≤ H) (hx : IsSkeleton x v H a b) (s t : ℝ) :
    PDE.vecEuclideanNorm
      (extendVelocity v a b hab s - extendVelocity v a b hab t) ≤ H * |s - t| := by
  have hdist := (LipschitzWith.projIcc hab).dist_le_mul s t
  have hproj : |(projIcc a b hab s : ℝ) - (projIcc a b hab t : ℝ)| ≤ |s - t| := by
    simpa only [Subtype.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul] using hdist
  exact (hx.2.2 _ (projIcc a b hab s).property _ (projIcc a b hab t).property).trans
    (mul_le_mul_of_nonneg_left hproj hH)

end HypoellipticAleksandrov.KineticAleksandrov.Holder

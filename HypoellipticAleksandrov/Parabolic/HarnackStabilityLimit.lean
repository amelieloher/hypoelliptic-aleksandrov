module

public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Passing parabolic Harnack inequalities to uniform limits

This module records the elementary order-closedness argument that passes an
eventual additive-error Harnack inequality to a uniform limit.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open Filter Set
open scoped Topology

/-- An eventual Harnack inequality with a vanishing additive error passes to a
uniform limit on a carrier containing the source and target set. -/
theorem harnack_limit_of_tendstoUniformlyOn_of_eventually_le_add
    {α : Type*} {K T : Set α} {x₀ : α}
    {v : Nat → α → Real} {q : α → Real} {ε : Nat → Real} {h : Real}
    (hx₀ : x₀ ∈ K) (hTK : T ⊆ K)
    (hv : TendstoUniformlyOn v q atTop K)
    (hε : Tendsto ε atTop (nhds 0))
    (hinequality : ∀ᶠ n in atTop, ∀ x ∈ T,
      h * v n x₀ ≤ v n x + ε n) :
    ∀ x ∈ T, h * q x₀ ≤ q x := by
  intro x hx
  have hsource : Tendsto (fun n => v n x₀) atTop (nhds (q x₀)) :=
    hv.tendsto_at hx₀
  have htarget : Tendsto (fun n => v n x) atTop (nhds (q x)) :=
    hv.tendsto_at (hTK hx)
  have hleft : Tendsto (fun n => h * v n x₀) atTop (nhds (h * q x₀)) :=
    tendsto_const_nhds.mul hsource
  have hright : Tendsto (fun n => v n x + ε n) atTop (nhds (q x)) := by
    simpa using htarget.add hε
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [hinequality] with n hn
  exact hn x hx

end HypoellipticAleksandrov.Parabolic

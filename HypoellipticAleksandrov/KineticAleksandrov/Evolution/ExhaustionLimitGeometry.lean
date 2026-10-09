module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCauchyRegion
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCauchyRadius

/-!
# Eventual containment of fixed inner cylinders

Every bounded inner cylinder eventually lies strictly inside every finite
approximating ellipsoid. The radius and curve errors are the actual sequence data.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov Set Filter
open scoped Topology

/-- A bounded strict inner cylinder, using the manuscript Euclidean radius and cutoff. -/
def boundedInnerOpenCylinder {n : ℕ} (ρ : ℝ) (Γ : ℝ → PDE.Vec n)
    (α τ S : ℝ) : Set (KineticPoint n) :=
  {p | α < p.time ∧ p.time < τ ∧
    p.position ∈ movingDomain (PDE.euclideanBall 0 ρ) Γ p.time ∧ radialSq p < S ^ 2}

/-- Strict bounded inner cylinders are open for continuous centre curves. -/
theorem isOpen_boundedInnerOpenCylinder {n : ℕ} (ρ : ℝ) {Γ : ℝ → PDE.Vec n}
    (hΓ : Continuous Γ) (α τ S : ℝ) : IsOpen (boundedInnerOpenCylinder ρ Γ α τ S) :=
  (isOpen_lt continuous_const continuous_time).inter
    ((isOpen_lt continuous_time continuous_const).inter
      ((isOpen_setOf_mem_movingDomain (PDE.isOpen_euclideanBall 0 ρ) hΓ).inter
        (isOpen_lt continuous_radialSq continuous_const)))

/-- A strict inner cylinder lies in the corresponding compact closed cylinder. -/
theorem boundedInnerOpenCylinder_subset_closed {n : ℕ} (ρ : ℝ)
    (Γ : ℝ → PDE.Vec n) (α τ S : ℝ) :
    boundedInnerOpenCylinder ρ Γ α τ S ⊆
      movingClosedSlab (PDE.euclideanBall 0 ρ) Γ α τ ∩ {p | radialSq p ≤ S ^ 2} :=
  fun _ hp => ⟨⟨hp.1.le, hp.2.1.le, subset_closure hp.2.2.1⟩, hp.2.2.2.le⟩

/-- A fixed bounded inner cylinder is eventually contained in the actual finite
ellipsoids, with positive radii. -/
theorem eventually_innerCylinder_mem_straightenedEllipsoid
    {n : ℕ} {α τ r0 δ S : ℝ} (hδ : 0 < δ) (hδr : δ < r0)
    {Γ : ℝ → PDE.Vec n} (β R : ℕ → ℝ)
    (hβlim : Tendsto β atTop (𝓝 0)) (hRlim : Tendsto R atTop atTop)
    (g : ℕ → ℝ → PDE.Vec n)
    (hclose : ∀ k s, s ∈ Icc α τ → PDE.vecEuclideanNorm (g k s - Γ s) ≤ β k / 2) :
    ∀ᶠ k : ℕ in atTop, 0 < r0 - β k ∧ 0 < R k ∧
      ∀ p ∈ movingClosedSlab (PDE.euclideanBall 0 (r0 - δ)) Γ α τ ∩
        {q | radialSq q ≤ S ^ 2},
      (straightenedPoint (g k) p).2 ∈
        openEllipsoid (straightenedEllipsoidMatrix n (r0 - β k) (R k)) := by
  obtain ⟨R0, hR0, hsize⟩ := exists_transportedRadius_common_innerCylinder
    (sub_pos.mpr hδr) (by linarith : 0 ≤ δ / 8)
    (by linarith : r0 - δ + δ / 8 < r0 - δ / 4) S
  filter_upwards [hβlim.eventually (gt_mem_nhds (by linarith : 0 < δ / 4)),
    hRlim.eventually (eventually_ge_atTop R0)] with k hk hRk
  have hr : 0 < r0 - β k := by linarith
  have hR : 0 < R k := hR0.trans_le hRk
  refine ⟨hr, hR, fun p hp => ?_⟩
  exact mem_straightenedEllipsoid_of_common_innerCylinder
    (sub_pos.mpr hδr) hr hR
    (fun s hs => (hclose k s hs).trans (by linarith))
    (hsize _ _ (by linarith : r0 - δ / 4 ≤ r0 - β k) hRk) hp

end HypoellipticAleksandrov.KineticAleksandrov

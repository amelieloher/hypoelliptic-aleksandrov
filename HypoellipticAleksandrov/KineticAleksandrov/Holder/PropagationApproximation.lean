module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.SkeletonApproximation
import Mathlib.Tactic

/-! # Halved corridors under uniform smooth skeleton approximation -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set

/-- A uniformly close path's halved corridor lies in the original full corridor. -/
theorem corridor_half_subset_of_approximation {d : ℕ}
    (tminus a b kx kv eps : ℝ) (x v y w : ℝ → PDE.Vec d)
    (hex : eps ≤ kx / 2) (hev : eps ≤ kv / 2)
    (hclose : ∀ s ∈ Icc a b, PDE.vecEuclideanNorm (y s - x s) < eps ∧
      PDE.vecEuclideanNorm (w s - v s) < eps) :
    corridor tminus a b (kx / 2) (kv / 2) y w ⊆ corridor tminus a b kx kv x v := by
  intro P hP
  obtain ⟨ht, hx, hv⟩ := hP
  have hc := hclose (P.time - tminus) ht
  refine ⟨ht, ?_, ?_⟩
  · have heq : P.position - x (P.time - tminus) =
        (P.position - y (P.time - tminus)) + (y (P.time - tminus) - x (P.time - tminus)) :=
      by abel
    rw [heq]
    apply (PDE.vecEuclideanNorm_add_le _ _).trans
    linarith only [hx, hc.1, hex]
  · have heq : P.velocity - v (P.time - tminus) =
        (P.velocity - w (P.time - tminus)) + (w (P.time - tminus) - v (P.time - tminus)) :=
      by abel
    rw [heq]
    apply (PDE.vecEuclideanNorm_add_le _ _).trans
    linarith only [hv, hc.2, hev]

end HypoellipticAleksandrov.KineticAleksandrov.Holder

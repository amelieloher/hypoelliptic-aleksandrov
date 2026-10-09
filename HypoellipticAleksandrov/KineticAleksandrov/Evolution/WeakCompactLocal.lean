module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.WeakDual

/-!
# Weak subsequences in separable real Hilbert spaces

The sequential Banach--Alaoglu theorem and the Riesz isometry give a subsequence
converging against every Hilbert-space test vector.
-/

@[expose] public section

open Filter Topology

namespace HypoellipticAleksandrov.KineticAleksandrov

/-- A bounded sequence in a separable real Hilbert space has a weakly convergent
subsequence. -/
theorem exists_hilbert_weak_subsequence
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (v : ℕ → H) (R : ℝ) (hv : ∀ j, ‖v j‖ ≤ R) :
    ∃ (u : H) (ν : ℕ → ℕ), StrictMono ν ∧
      ∀ w : H, Tendsto (fun j => inner ℝ (v (ν j)) w)
        atTop (nhds (inner ℝ u w)) := by
  let f : ℕ → WeakDual ℝ H := fun j =>
    StrongDual.toWeakDual ((InnerProductSpace.toDual ℝ H) (v j))
  have hf : ∀ j, f j ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 R := by
    intro j
    change dist ((InnerProductSpace.toDual ℝ H) (v j)) 0 ≤ R
    simpa only [dist_zero_right, LinearIsometryEquiv.norm_map] using hv j
  obtain ⟨g, _, ν, hν, hg⟩ := (WeakDual.isSeqCompact_closedBall
    (𝕜 := ℝ) (E := H) 0 R) hf
  refine ⟨(InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual g), ν, hν, ?_⟩
  intro w
  have hw := (WeakDual.eval_continuous w).continuousAt.tendsto.comp hg
  simpa only [Function.comp_def, f, InnerProductSpace.toDual_apply_apply,
    InnerProductSpace.toDual_symm_apply] using! hw

end HypoellipticAleksandrov.KineticAleksandrov

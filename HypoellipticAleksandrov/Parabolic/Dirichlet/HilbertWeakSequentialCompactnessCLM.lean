module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.HilbertWeakSequentialCompactness

/-! Sequential weak compactness against continuous linear functionals in separable real Hilbert
spaces. -/

@[expose] public section

open Filter Function Set
open scoped Topology

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- A norm-bounded sequence in a separable real Hilbert space has a strictly monotone
subsequence converging against every continuous linear functional. -/
theorem exists_strictMono_tendsto_clm_of_norm_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (u : ℕ → H) (R : ℝ) (hu : ∀ n, ‖u n‖ ≤ R) :
    ∃ (v : H) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ ell : H →L[ℝ] ℝ,
        Tendsto (fun n => ell (u (φ n))) atTop (𝓝 (ell v)) := by
  obtain ⟨v, φ, hφ, hinner⟩ := exists_strictMono_tendsto_inner_of_norm_le u R hu
  refine ⟨v, φ, hφ, fun ell => ?_⟩
  let z := (InnerProductSpace.toDual ℝ H).symm ell
  simp_rw [← InnerProductSpace.toDual_symm_apply]
  simpa only [z, real_inner_comm] using hinner z

end HypoellipticAleksandrov.Parabolic.Dirichlet

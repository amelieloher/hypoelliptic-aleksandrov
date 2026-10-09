module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.HilbertWeakSequentialCompactnessCLM
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Simultaneous weak subsequences for finite derivative families

One subsequence retains every entry of a finite family. This avoids making independent
subsequence choices when passing the derivative relations to a limit.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter
open scoped Topology BigOperators

/-- A bounded finite family in a Hilbert space has one common weakly convergent subsequence. -/
theorem exists_strictMono_tendsto_clm_family_of_sum_norm_sq_le
    {I H : Type*} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (u : ℕ → I → H) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ n, ∑ i, ‖u n i‖ ^ 2 ≤ C ^ 2) :
    ∃ (v : I → H) (σ : ℕ → ℕ), StrictMono σ ∧
      ∀ i (ell : H →L[ℝ] ℝ),
        Tendsto (fun n => ell (u (σ n) i)) atTop (𝓝 (ell (v i))) := by
  let q : ℕ → PiLp 2 (fun _ : I => H) := fun n => WithLp.toLp 2 (u n)
  have hq (n : ℕ) : ‖q n‖ ≤ C := by
    have heq : ‖q n‖ ^ 2 = ∑ i, ‖u n i‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ _
    have hsq := hb n
    rw [← heq] at hsq
    exact (sq_le_sq₀ (norm_nonneg _) hC).mp hsq
  obtain ⟨v, σ, hσ, hv⟩ :=
    Dirichlet.exists_strictMono_tendsto_clm_of_norm_le q C hq
  refine ⟨fun i => v i, σ, hσ, ?_⟩
  intro i ell
  exact hv (ell.comp (PiLp.proj 2 (fun _ : I => H) i))

end HypoellipticAleksandrov.Parabolic.LocalHolder

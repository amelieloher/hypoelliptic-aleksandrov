module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.WeakDual

/-! Sequential weak compactness for bounded sequences in separable real Hilbert spaces. -/

@[expose] public section

open Filter Function Set
open scoped Topology

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- A norm-bounded sequence in a separable real Hilbert space has a strictly monotone
subsequence whose inner products converge against every test vector. -/
theorem exists_strictMono_tendsto_inner_of_norm_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (u : ℕ → H) (R : ℝ) (hu : ∀ n, ‖u n‖ ≤ R) :
    ∃ (v : H) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ z : H,
        Tendsto (fun n => inner ℝ (u (φ n)) z) atTop
          (𝓝 (inner ℝ v z)) := by
  let f : ℕ → WeakDual ℝ H := fun n =>
    StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H (u n))
  have hf : ∀ n, f n ∈ WeakDual.toStrongDual ⁻¹'
      Metric.closedBall (0 : StrongDual ℝ H) R := by
    intro n
    rw [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm]
    change ‖InnerProductSpace.toDual ℝ H (u n) - 0‖ ≤ R
    simpa using hu n
  obtain ⟨ℓ, hℓ, φ, hφ, hlim⟩ :=
    (WeakDual.isSeqCompact_closedBall ℝ H (0 : StrongDual ℝ H) R) hf
  let v : H :=
    (InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual ℓ)
  refine ⟨v, φ, hφ, fun z => ?_⟩
  simpa [f, v, Function.comp_def] using
    ((WeakDual.eval_continuous z).tendsto ℓ).comp hlim

end HypoellipticAleksandrov.Parabolic.Dirichlet

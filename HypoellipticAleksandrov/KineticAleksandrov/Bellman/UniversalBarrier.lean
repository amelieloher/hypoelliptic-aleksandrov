module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.UniversalBarrierPositiveImage
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.UniversalBarrierLowerBound

/-! # The universal homogeneous Bellman barrier with the source adjoint exponent -/

@[expose] public section
noncomputable section
open Set
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- One homogeneous barrier and constant work for all punctured points and coefficients. -/
theorem exists_bellman_barrier (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    2 ≤ bellmanAdjointExponent (Lam / lam)
      (by apply (le_div_iff₀ hlam).2; simpa only [one_mul] using hLam) ∧
    bellmanAdjointExponent (Lam / lam)
      (by apply (le_div_iff₀ hlam).2; simpa only [one_mul] using hLam) < 3 ∧
    ∀ alpha : ℝ, bellmanAdjointExponent (Lam / lam)
      (by apply (le_div_iff₀ hlam).2; simpa only [one_mul] using hLam) - 2 < alpha →
      alpha < 1 → ∃ phi : (ℝ × ℝ) → ℝ, ∃ c : ℝ,
        IsBellmanHomogeneous alpha phi ∧ 0 < c ∧
          ∀ q ∈ bellmanPuncturedSet, ∀ b ∈ Icc lam Lam,
            c * bellmanGauge q ^ (alpha - 2) ≤ bellmanOperator b phi q := by
  have hr : 1 ≤ Lam / lam := by
    apply (le_div_iff₀ hlam).2
    simpa only [one_mul] using hLam
  obtain ⟨hlo, hhi⟩ := bellmanAdjointExponent_range (Lam / lam) hr
  refine ⟨hlo, hhi, ?_⟩
  intro alpha ha ha1
  obtain ⟨phi, hhom, hpos⟩ := exists_positive_bellman_image lam Lam hlam hLam alpha ha ha1
  obtain ⟨c, hc, hbound⟩ :=
    positive_bellman_image_lower_bound lam Lam hlam hLam alpha phi hhom hpos
  exact ⟨phi, c, hhom, hc, hbound⟩

end HypoellipticAleksandrov.KineticAleksandrov

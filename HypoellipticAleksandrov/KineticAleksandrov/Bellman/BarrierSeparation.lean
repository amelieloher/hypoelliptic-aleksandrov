module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.BarrierFunctionSpaceLinear
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.BarrierSeparationMeasure

/-! # The source probability separation alternative for C² homogeneous images -/

@[expose] public section
noncomputable section
open Set MeasureTheory
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- Failure of a strictly positive homogeneous image gives one annihilating probability. -/
theorem exists_annihilating_bellman_probability (lam Lam alpha : ℝ)
    (_hlam : 0 < lam) (_hLam : lam ≤ Lam) (_ha : 0 < alpha) (_ha1 : alpha < 1)
    (hno : ¬ ∃ phi : (ℝ × ℝ) → ℝ, IsBellmanHomogeneous alpha phi ∧
      ∀ z : BellmanSphere, ∀ b : BellmanCoefficient lam Lam,
        0 < bellmanOperator b.val phi z.val) :
    ∃ pi : Measure (BellmanSphere × BellmanCoefficient lam Lam),
      IsProbabilityMeasure pi ∧
      ∀ phi : (ℝ × ℝ) → ℝ, IsBellmanHomogeneous alpha phi →
        (∫ w, bellmanOperator w.2.val phi w.1.val ∂pi) = 0 := by
  have hd : Disjoint bellmanPositiveCone
      (bellmanImageSpace alpha lam Lam : Set C(BellmanSphere × BellmanCoefficient lam Lam, ℝ)) := by
    refine disjoint_left.mpr ?_
    intro f hf hS
    obtain ⟨phi, hphi, he⟩ := (mem_bellmanImageSpace_iff alpha lam Lam f).mp hS
    apply hno
    refine ⟨phi, hphi, ?_⟩
    intro z b
    have h := hf (z, b)
    rw [← he] at h
    exact h
  obtain ⟨pi, hpi, ht⟩ := exists_bellman_subspace_probability
    (bellmanImageSpace alpha lam Lam) hd
  refine ⟨pi, hpi, ?_⟩
  intro phi hphi
  exact ht (bellmanImage lam Lam phi hphi)
    ((mem_bellmanImageSpace_iff alpha lam Lam _).mpr ⟨phi, hphi, rfl⟩)

end HypoellipticAleksandrov.KineticAleksandrov

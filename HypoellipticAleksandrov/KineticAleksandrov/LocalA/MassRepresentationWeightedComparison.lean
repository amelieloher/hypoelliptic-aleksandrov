module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.MassRepresentationGrowth

/-! # Symmetric weighted trace comparison for actual homogeneous solutions -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set Parabolic

/-- Absolute weighted trace error bounds the difference of two actual homogeneous solutions. -/
theorem mass_homogeneous_abs_weighted {d : ℕ} {lam Lam : ℝ}
    (B : CoefficientField d) (hB : SectionTwo.IsSectionTwoCoefficient lam Lam B)
    (a T : ℝ) (haT : a < T) (v₀ : PDE.Vec d) (R : ℝ)
    (u v : KineticPoint d → ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ (KineticPoint.equivProd d).symm)
      ((KineticPoint.equivProd d) '' localStrip a T v₀ R))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) (v ∘ (KineticPoint.equivProd d).symm)
      ((KineticPoint.equivProd d) '' localStrip a T v₀ R))
    (heu : ∀ P ∈ localStrip a T v₀ R,
      forwardKineticOperator (ofTimeVelocityCoefficient B) u P = 0)
    (hev : ∀ P ∈ localStrip a T v₀ R,
      forwardKineticOperator (ofTimeVelocityCoefficient B) v P = 0)
    (hcu : ContinuousOn u (localClosedStrip a T v₀ R))
    (hcv : ContinuousOn v (localClosedStrip a T v₀ R))
    (hbu : ∃ M : ℝ, ∀ P ∈ localClosedStrip a T v₀ R, |u P| ≤ M)
    (hbv : ∃ M : ℝ, ∀ P ∈ localClosedStrip a T v₀ R, |v P| ≤ M)
    (ε : ℝ) (hε : 0 ≤ ε)
    (htr : ∀ P ∈ localTrace a T v₀ R, |u P - v P| ≤ ε * massGrowthBarrier Lam T P) :
    ∀ P ∈ localClosedStrip a T v₀ R, |u P - v P| ≤ ε * massGrowthBarrier Lam T P := by
  obtain ⟨M, hM⟩ := hbu
  obtain ⟨N, hN⟩ := hbv
  have hf : ∀ P ∈ localStrip a T v₀ R,
      forwardKineticOperator (ofTimeVelocityCoefficient B) (fun Q => u Q - v Q) P = 0 := by
    intro P hP
    rw [cone_forward_sub B (isOpen_localStrip a T v₀ R) u v hu hv P hP,
      heu P hP, hev P hP, sub_self]
  have hg : ∀ P ∈ localStrip a T v₀ R,
      forwardKineticOperator (ofTimeVelocityCoefficient B) (fun Q => v Q - u Q) P = 0 := by
    intro P hP
    rw [cone_forward_sub B (isOpen_localStrip a T v₀ R) v u hv hu P hP,
      hev P hP, heu P hP, sub_self]
  have h₁ := mass_weighted_trace_bound B hB a T haT v₀ R (fun P => u P - v P)
    (hu.sub hv) hf (hcu.sub hcv)
    ⟨M + N, fun P hP => (abs_sub _ _).trans (add_le_add (hM P hP) (hN P hP))⟩
    ε hε (fun P hP => (le_abs_self _).trans (htr P hP))
  have h₂ := mass_weighted_trace_bound B hB a T haT v₀ R (fun P => v P - u P)
    (hv.sub hu) hg (hcv.sub hcu)
    ⟨N + M, fun P hP => (abs_sub _ _).trans (add_le_add (hN P hP) (hM P hP))⟩
    ε hε (fun P hP => by
      have hh := htr P hP
      rw [abs_sub_comm] at hh
      exact (le_abs_self _).trans hh)
  intro P hP
  apply abs_le.mpr
  constructor
  · have hh := h₂ P hP
    linarith only [hh]
  · exact h₁ P hP

end HypoellipticAleksandrov.KineticAleksandrov.LocalA

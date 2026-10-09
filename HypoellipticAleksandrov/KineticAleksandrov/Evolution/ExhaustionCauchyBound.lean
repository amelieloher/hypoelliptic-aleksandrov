module

public import HypoellipticAleksandrov.Parabolic.ScalarMaximum
public import HypoellipticAleksandrov.Parabolic.AffineScalarCalculus

/-!
# The exhaustion-independent bound for supplied finite Dirichlet solutions

The constant bound is proved on the actual scalar cylinder before any exhaustion limit
is constructed. Only the supplied scalar C1,2 regularity is used.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set
open scoped MatrixOrder

/-- Zero-source, zero-lateral classical Dirichlet solutions inherit the terminal absolute
bound on their entire closed finite cylinder, independently of the cylinder size. -/
theorem abs_le_of_classicalBackwardDirichlet_zero
    {d : ℕ} {Ω : Set (PDE.Vec d)} {a τ : ℝ}
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (haτ : a < τ)
    (A : CoefficientField d) (β : ℝ → PDE.Vec d → PDE.Vec d)
    (hA : IsContinuousCoefficient A)
    (hβ : Continuous (fun q : TimeVelocity d => β q.1 q.2))
    (hAp : ∀ s x, (A s x).PosSemidef)
    (φ : PDE.Vec d → ℝ) (u : TimeVelocity d → ℝ)
    (hu : IsClassicalBackwardDirichletSolution a τ Ω A β
      (fun _ _ => 0) (fun _ _ => 0) φ (fun _ => 0) u)
    {C : ℝ} (hC : 0 ≤ C) (hφ : ∀ x ∈ closure Ω, |φ x| ≤ C) :
    ∀ q ∈ scalarParabolicClosedCylinder a τ Ω, |u q| ≤ C := by
  have side (s : ℝ) (hs : s = 1 ∨ s = -1) :
      ∀ q ∈ scalarParabolicClosedCylinder a τ Ω, s * u q + 0 ≤ C := by
    apply scalar_le_on_closedCylinder_of_terminal_lateral_le hΩ hΩb haτ A β hA hβ hAp
      (fun q => s * u q + 0)
    · exact (hu.1.const_smul s).add continuousOn_const
    · exact hu.2.1.const_mul_add_const s 0
    · intro q hq
      have heq := hu.2.2.1 q hq
      have hid := scalarParabolicZeroOrderOperator_const_mul_add_const
        A β (fun _ _ => 0) s 0 u q
      simp only [scalarParabolicZeroOrderOperator, zero_mul, add_zero] at heq hid
      simpa only [add_zero, hid, heq, mul_zero] using (le_refl (0 : ℝ))
    · rintro ⟨t, x⟩ ⟨ht, hx⟩
      simp only [mem_singleton_iff] at ht
      subst t
      rw [hu.2.2.2.1 x hx]
      rcases hs with rfl | rfl
      · simpa only [one_mul, add_zero] using (abs_le.mp (hφ x hx)).2
      · have := (abs_le.mp (hφ x hx)).1
        linarith
    · intro q hq
      rw [hu.2.2.2.2 q hq, mul_zero, zero_add]
      exact hC
  intro q hq
  have hp := side 1 (Or.inl rfl) q hq
  have hn := side (-1) (Or.inr rfl) q hq
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end HypoellipticAleksandrov.KineticAleksandrov

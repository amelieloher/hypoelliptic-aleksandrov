module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.HigherOrderLocalL2Regularity

/-! # Higher weak derivatives of homogeneous replacement jets

The source derivative family is literally zero. Restriction puts every solution's higher
family on the same target collar, with one constant chosen before the solution.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open MeasureTheory Set
open scoped BigOperators MatrixOrder Matrix.Norms.Elementwise

/-- The actual zero function has zero coordinate derivative of every multi-index order. -/
theorem coordinateIteratedFDeriv_zero_function {d : ℕ}
    (beta : TimeVelocityMultiIndex d) :
    TimeVelocityMultiIndex.coordinateIteratedFDeriv beta
      (fun _ : TimeVelocity d => (0 : ℝ)) = 0 := by
  funext z
  simp only [TimeVelocityMultiIndex.coordinateIteratedFDeriv, iteratedFDeriv_fun_zero,
    Pi.zero_apply, zero_apply]

/-- Homogeneous jets have uniformly controlled higher families on a common smaller collar. -/
theorem exists_homogeneous_higher_family_constant {d : ℕ}
    {Ω O₀ O : Set (PDE.Vec d)}
    (r₀ q₀ s₀ s₁ q₁ r₁ : ℝ)
    (hr₀q₀ : r₀ < q₀) (hq₀s₀ : q₀ < s₀) (hs₀s₁ : s₀ < s₁)
    (hs₁q₁ : s₁ < q₁) (hq₁r₁ : q₁ < r₁)
    (hΩopen : IsOpen Ω) (hO₀open : IsOpen O₀)
    (hO₀compact : IsCompact (closure O₀)) (hO₀Ω : closure O₀ ⊆ Ω)
    (hOopen : IsOpen O) (hOne : O.Nonempty)
    (hOcompact : IsCompact (closure O)) (hOO₀ : closure O ⊆ O₀)
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (A : CoefficientField d) (hA : IsSmoothCoefficient A)
    (hLower : ∀ z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω,
      lam • (1 : PDE.Mat d) ≤ A z.1 z.2)
    (hUpper : ∀ z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω,
      A z.1 z.2 ≤ Lam • (1 : PDE.Mat d)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ J : ParabolicW12Function d (Ioo q₀ q₁ ×ˢ O₀) 2,
      (∀ᵐ z ∂timeVelocityVolumeOn (Ioo q₀ q₁ ×ˢ O₀),
        J.timeDeriv z + ∑ i, ∑ j, A z.1 z.2 i j * J.velocityHessian z j i = 0) →
      ∃ D : ParabolicWeakDerivativeFamily d (2 * d + 8) (Ioo s₀ s₁ ×ˢ O) J.toFun,
        (∀ alpha : ParabolicDerivativeIndex d 2,
          D.representative (ParabolicDerivativeIndex.castLE
            (by omega : 2 ≤ 2 * d + 8) alpha) =
          (J.toWeakDerivativeFamily (isOpen_Ioo.prod hO₀open)).representative alpha) ∧
        D.squaredL2Norm ≤ C * (J.toWeakDerivativeFamily
          (isOpen_Ioo.prod hO₀open)).squaredL2Norm := by
  have hAs : IsSmoothOnNeighborhood (fun z : TimeVelocity d => A z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω) :=
    ⟨univ, isOpen_univ, subset_univ _, hA.contDiffOn⟩
  have hbs : IsSmoothOnNeighborhood (fun _ : TimeVelocity d => (0 : PDE.Vec d))
      (scalarParabolicClosedCylinder r₀ r₁ Ω) :=
    ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩
  have hcs : IsSmoothOnNeighborhood (fun _ : TimeVelocity d => (0 : ℝ))
      (scalarParabolicClosedCylinder r₀ r₁ Ω) :=
    ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩
  obtain ⟨C, hC, hrun⟩ :=
    Dirichlet.exists_higherOrderLocalL2WeakDerivativeFamily_of_strongJet
      r₀ q₀ s₀ s₁ q₁ r₁ hr₀q₀ hq₀s₀ hs₀s₁ hs₁q₁ hq₁r₁
      hΩopen hO₀open hO₀compact hO₀Ω hOopen hOne hOcompact hOO₀
      lam Lam hlam hlamLam A (fun _ _ => 0) (fun _ _ => 0)
      hAs hbs hcs hLower hUpper
  refine ⟨C, hC, ?_⟩
  intro J heq
  have hpde : ∀ᵐ z ∂timeVelocityVolumeOn (Ioo q₀ q₁ ×ˢ O₀),
      J.timeDeriv z + (∑ i, ∑ j, A z.1 z.2 i j * J.velocityHessian z j i) +
        (∑ j, (0 : PDE.Vec d) j * J.velocityGrad z j) + 0 * J.toFun z = 0 := by
    filter_upwards [heq] with z hz
    simpa using hz
  obtain ⟨l, r, Oc, B, E, D, hql, hls, hsr, hrq, hOc, hOcne, hOcc,
    hOOc, hOcO₀, hB, hFB, hErep, hEnorm, hDlow, hDnorm⟩ :=
    hrun (fun _ _ => 0) hcs J hpde
  have hEZ : E.squaredL2Norm = 0 := by
    unfold ParabolicWeakDerivativeFamily.squaredL2Norm
    apply Finset.sum_eq_zero
    intro beta _
    rw [hErep beta, coordinateIteratedFDeriv_zero_function]
    simp
  have hsub : Ioo s₀ s₁ ×ˢ O ⊆ Ioo l r ×ˢ Oc := by
    intro z hz
    exact ⟨⟨hls.trans hz.1.1, hz.1.2.trans hsr⟩, hOOc (subset_closure hz.2)⟩
  refine ⟨D.restrict hsub, ?_, ?_⟩
  · intro alpha
    exact hDlow alpha
  · apply (D.squaredL2Norm_restrict_le hsub).trans
    simpa only [hEZ, add_zero] using hDnorm

end HypoellipticAleksandrov.Parabolic.LocalHolder

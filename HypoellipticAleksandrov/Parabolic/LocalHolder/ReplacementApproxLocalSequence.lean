module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApproxUniformSeed
public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApproxControlledFamilies
public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApproxHomogeneousLimit
public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApproxCollarGeometry

/-! # Classical homogeneous convergence on a fixed interior collar

Outer value energy controls the seed jets, which control the common higher families.
Strong root convergence then gives both classical regularity and the literal equation.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter MeasureTheory Set
open scoped BigOperators Topology MatrixOrder Matrix.Norms.Elementwise

/-- A uniformly value-bounded homogeneous sequence has a classical limit on an inner collar. -/
theorem scalarC12_homogeneous_local_sequence_limit {d : ℕ}
    (a q₀ p₀ s₀ s₁ p₁ q₁ T : ℝ)
    (haq₀ : a < q₀) (hq₀p₀ : q₀ < p₀) (hp₀s₀ : p₀ < s₀)
    (hs₀s₁ : s₀ < s₁) (hs₁p₁ : s₁ < p₁) (hp₁q₁ : p₁ < q₁) (hq₁T : q₁ < T)
    (Ω O₀ O₁ O₂ : Set (PDE.Vec d)) (hΩ : IsOpen Ω)
    (hΩc : IsCompact (closure Ω))
    (hO₀ : IsOpen O₀) (hO₀c : IsCompact (closure O₀)) (hO₀Ω : closure O₀ ⊆ Ω)
    (hO₁ : IsOpen O₁) (hO₁c : IsCompact (closure O₁)) (hO₁O₀ : closure O₁ ⊆ O₀)
    (hO₂ : IsOpen O₂) (hO₂ne : O₂.Nonempty)
    (hO₂c : IsCompact (closure O₂)) (hO₂O₁ : closure O₂ ⊆ O₁)
    (A : CoefficientField d) (hA : IsSmoothCoefficient A)
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hlo : HasLowerEllipticity lam A) (hhi : HasUpperEllipticity Lam A)
    (u : ℕ → TimeVelocity d → ℝ)
    (hu : ∀ n, IsScalarC12On (u n) (Ioo a T ×ˢ Ω))
    (hEq : ∀ n z, z ∈ Ioo a T ×ˢ Ω → scalarTimeDerivative (u n) z +
      matrixContraction (coefficientAt A z) (scalarSpatialHessian (u n) z) = 0)
    (hq : ∀ n, IntegrableOn (fun z => u n z ^ 2) (Ioo a T ×ˢ Ω))
    (N : ℝ) (hN : 0 ≤ N) (hb : ∀ n, (∫ z in Ioo a T ×ˢ Ω, u n z ^ 2) ≤ N)
    (v : TimeVelocity d → ℝ) (hvcont : ContinuousOn v (Ioo s₀ s₁ ×ˢ O₂))
    (hun : ∀ n, ParabolicMemLpOn (Ioo s₀ s₁ ×ˢ O₂) 2 (u n))
    (hv : ParabolicMemLpOn (Ioo s₀ s₁ ×ˢ O₂) 2 v)
    (hstrong : Tendsto (fun n => (hun n).toLp (u n)) atTop (𝓝 (hv.toLp v))) :
    IsScalarC12On v (Ioo s₀ s₁ ×ˢ O₂) ∧
      ∀ z ∈ Ioo s₀ s₁ ×ˢ O₂, scalarTimeDerivative v z +
        matrixContraction (coefficientAt A z) (scalarSpatialHessian v z) = 0 := by
  have hQD := closure_local_product_subset haq₀ hq₁T hO₀Ω
  have hPQ := closure_local_product_subset hq₀p₀ hp₁q₁ hO₁O₀
  have hPD := hPQ.trans (subset_closure.trans hQD)
  have hPS : p₀ < p₁ := hp₀s₀.trans (hs₀s₁.trans hs₁p₁)
  have hO₁Ω := hO₁O₀.trans (subset_closure.trans hO₀Ω)
  let J (n : ℕ) := classicalLocalW12Jet (u n) (hu n) (isOpen_Ioo.prod hO₁)
    (isCompact_closure_local_product p₀ p₁ hO₁c) hPD
  obtain ⟨Cs, hCs, hseedrun⟩ := exists_uniform_classical_seed_constant
    a T q₀ p₀ p₁ q₁ hq₀p₀ hPS.le hp₁q₁ Ω O₀ O₁ hΩ
    (isCompact_closure_local_product a T hΩc) hO₀ hO₀c
    (isCompact_closure_local_product q₀ q₁ hO₀c) hQD hO₁ hO₁c hO₁O₀
    (isCompact_closure_local_product p₀ p₁ hO₁c) hPQ A hA lam Lam hlam hlamLam hlo hhi
  have hseed (n : ℕ) : ((J n).toWeakDerivativeFamily
      (isOpen_Ioo.prod hO₁)).squaredL2Norm ≤ Cs * N :=
    (hseedrun (u n) (hu n) (hq n) (hEq n)).trans
      (mul_le_mul_of_nonneg_left (hb n) hCs)
  have hJEq (n : ℕ) := classicalLocalW12Jet_homogeneous_equation
    (u n) (hu n) (isOpen_Ioo.prod hO₁)
    (isCompact_closure_local_product p₀ p₁ hO₁c) hPD A (hEq n)
  obtain ⟨C, D, hC, hDb, hDzero⟩ := exists_controlled_homogeneous_higher_families
    a p₀ s₀ s₁ p₁ T (haq₀.trans hq₀p₀) hp₀s₀ hs₀s₁ hs₁p₁ (hp₁q₁.trans hq₁T)
    hΩ hO₁ hO₁c hO₁Ω hO₂ hO₂ne hO₂c hO₂O₁
    lam Lam hlam hlamLam A hA hlo hhi J hJEq (Cs * N) (mul_nonneg hCs hN) hseed
  exact scalarC12_homogeneous_of_strongL2_limit (Ioo s₀ s₁ ×ˢ O₂)
    (isOpen_Ioo.prod hO₂) A hA Lam
    (fun z _ i j => abs_apply_le_of_loewner hlam (hlo z.1 z.2) (hhi z.1 z.2) i j)
    u D hun v hv hvcont hstrong C hC hDb hDzero

end HypoellipticAleksandrov.Parabolic.LocalHolder

module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApproxHigherFamily
public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApproxWeakEquationLimit
public import HypoellipticAleksandrov.Parabolic.ParabolicW12WeakDerivativeFamilyEquation
public import HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamilyL2NormTruncate
import Mathlib.Tactic.Linarith

/-! # Common controlled higher families for homogeneous jet sequences

Uniform seed energy produces actual higher families with the literal homogeneous equation
retained. The norm bound is independent of the sequence index.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter MeasureTheory Set
open scoped BigOperators MatrixOrder Matrix.Norms.Elementwise

/-- Uniform homogeneous seed jets give a common sequence of controlled higher families. -/
theorem exists_controlled_homogeneous_higher_families {d : ℕ}
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
    (hlo : HasLowerEllipticity lam A) (hhi : HasUpperEllipticity Lam A)
    (J : ℕ → ParabolicW12Function d (Ioo q₀ q₁ ×ˢ O₀) 2)
    (hEq : ∀ n, ∀ᵐ z ∂timeVelocityVolumeOn (Ioo q₀ q₁ ×ˢ O₀),
      (J n).timeDeriv z + ∑ i, ∑ j, A z.1 z.2 i j * (J n).velocityHessian z j i = 0)
    (N : ℝ) (hN : 0 ≤ N)
    (hseed : ∀ n, ((J n).toWeakDerivativeFamily
      (isOpen_Ioo.prod hO₀open)).squaredL2Norm ≤ N) :
    ∃ (C : ℝ) (D : ∀ n, ParabolicWeakDerivativeFamily d (2 * (d + 4))
      (Ioo s₀ s₁ ×ˢ O) (J n).toFun),
      0 ≤ C ∧ (∀ n, (D n).squaredL2Norm ≤ C ^ 2) ∧
      ∀ n, homogeneousWeakFamilyResidual (by omega : 2 ≤ 2 * (d + 4)) A (D n)
        =ᵐ[timeVelocityVolumeOn (Ioo s₀ s₁ ×ˢ O)] 0 := by
  classical
  obtain ⟨Ci, hCi, hrun⟩ := exists_homogeneous_higher_family_constant
    r₀ q₀ s₀ s₁ q₁ r₁ hr₀q₀ hq₀s₀ hs₀s₁ hs₁q₁ hq₁r₁
    hΩopen hO₀open hO₀compact hO₀Ω hOopen hOne hOcompact hOO₀
    lam Lam hlam hlamLam A hA (fun z _ => hlo z.1 z.2) (fun z _ => hhi z.1 z.2)
  have hex (n : ℕ) : ∃ D : ParabolicWeakDerivativeFamily d (2 * (d + 4))
      (Ioo s₀ s₁ ×ˢ O) (J n).toFun,
      (∀ alpha : ParabolicDerivativeIndex d 2, D.representative
        (ParabolicDerivativeIndex.castLE (by omega : 2 ≤ 2 * (d + 4)) alpha) =
        ((J n).toWeakDerivativeFamily (isOpen_Ioo.prod hO₀open)).representative alpha) ∧
      D.squaredL2Norm ≤ Ci * ((J n).toWeakDerivativeFamily
        (isOpen_Ioo.prod hO₀open)).squaredL2Norm := by
    obtain ⟨G, hGlow, hGnorm⟩ := hrun (J n) (hEq n)
    refine ⟨G.truncate (by omega : 2 * (d + 4) ≤ 2 * d + 8), ?_, ?_⟩
    · intro alpha
      exact hGlow alpha
    · exact (G.squaredL2Norm_truncate_le _).trans hGnorm
  choose D hlow hnorm using hex
  refine ⟨Ci * N + 1, D, by positivity, ?_, ?_⟩
  · intro n
    have hb := (hnorm n).trans (mul_le_mul_of_nonneg_left (hseed n) hCi)
    have hp : 0 ≤ Ci * N := mul_nonneg hCi hN
    nlinarith only [hb, hp, sq_nonneg (Ci * N)]
  · intro n
    have hEqfull : (fun z => (J n).timeDeriv z +
        (∑ i, ∑ j, A z.1 z.2 i j * (J n).velocityHessian z j i) +
        (∑ j, (0 : PDE.Vec d) j * (J n).velocityGrad z j) +
        0 * (J n).toFun z) =ᵐ[timeVelocityVolumeOn (Ioo q₀ q₁ ×ˢ O₀)] 0 := by
      filter_upwards [hEq n] with z hz
      simpa using hz
    have hcanon := (J n).toWeakDerivativeFamily_originalTimeEquation
      (isOpen_Ioo.prod hO₀open) A (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) hEqfull
    have hsub : Ioo s₀ s₁ ×ˢ O ⊆ Ioo q₀ q₁ ×ˢ O₀ := by
      intro z hz
      exact ⟨⟨hq₀s₀.trans hz.1.1, hz.1.2.trans hs₁q₁⟩, hOO₀ (subset_closure hz.2)⟩
    filter_upwards [hcanon.filter_mono (ae_mono (Measure.restrict_mono_set volume hsub))]
      with z hz
    simp only [homogeneousWeakFamilyResidual, hlow n] at ⊢
    simpa only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero] using hz

end HypoellipticAleksandrov.Parabolic.LocalHolder

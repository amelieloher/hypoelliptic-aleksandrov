module

public import PDEFoundation.Sobolev.WeakDerivative
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial
public import Mathlib.RingTheory.Polynomial.Bernstein

/-!
# Cutoff product-Bernstein spatial factors

This module bundles a product-Bernstein polynomial multiplied by a fixed smooth compactly
supported cutoff as a spatial weak test function.
-/

@[expose] public section

open scoped BigOperators

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- Multiplying a product-Bernstein polynomial by the fixed cutoff gives a spatial weak test. -/
theorem exists_cutoffPiBernsteinSpatialFactor
    {d n : ℕ} {O : Set (PDE.Vec d)}
    (χ : PDE.Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχcompact : IsCompact (tsupport χ)) (hχO : tsupport χ ⊆ O)
    (R : ℝ) (hR : 0 < R)
    (k : Fin d → Fin (n + 1)) :
    ∃ ψ : PDE.WeakTestFunction O,
      (∀ y, ψ y = χ y *
        ∏ i : Fin d, (bernsteinPolynomial ℝ n (k i)).eval (((y i / R) + 1) / 2)) ∧
      tsupport (ψ : PDE.Vec d → ℝ) ⊆ tsupport χ := by
  have _hRne : R ≠ 0 := hR.ne'
  let p : PDE.Vec d → ℝ := fun y =>
    ∏ i : Fin d, (bernsteinPolynomial ℝ n (k i)).eval (((y i / R) + 1) / 2)
  have hp : ContDiff ℝ (⊤ : ℕ∞) p := by
    apply contDiff_prod
    intro i _
    have hcoordinate : ContDiff ℝ (⊤ : ℕ∞) (fun y : PDE.Vec d => ((y i / R) + 1) / 2) :=
      (((contDiff_apply ℝ ℝ i).div_const R).add contDiff_const).div_const 2
    simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id,
      Function.comp_def] using
      (Polynomial.contDiff_aeval (𝕜 := ℝ) (bernsteinPolynomial ℝ n (k i))
        (↑(⊤ : ℕ∞) : WithTop ℕ∞)).comp hcoordinate
  let ψ : PDE.WeakTestFunction O :=
    { toFun := fun y => χ y * p y
      contDiff := hχ.mul hp
      hasCompactSupport :=
        IsCompact.of_isClosed_subset hχcompact (isClosed_tsupport _) tsupport_mul_subset_left
      tsupport_subset := tsupport_mul_subset_left.trans hχO }
  refine ⟨ψ, ?_, ?_⟩
  · intro y
    rfl
  · exact tsupport_mul_subset_left

end HypoellipticAleksandrov.Parabolic.Dirichlet

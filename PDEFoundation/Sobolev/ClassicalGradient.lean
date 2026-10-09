module

public import PDEFoundation.Ambient.Basis
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Classical gradients in the native ambient space

The inherited norm on `PDE.Vec d` is the finite-product supremum norm. This
file packages the coordinate gradient of a classically differentiable scalar
function as a native vector and relates directional derivatives to the
explicit Euclidean dot product. Quantitative PDE estimates should use the
resulting Euclidean Cauchy--Schwarz inequality, not the operator norm induced
by the inherited product norm.
-/

@[expose] public section

namespace PDE

/-- The coordinate gradient of a scalar function, expressed in the native
vector carrier. -/
noncomputable def classicalGradient {d : ℕ}
    (f : Vec d → ℝ) (x : Vec d) : Vec d :=
  fun i => (fderiv ℝ f x) (basisVec i)

@[simp]
theorem classicalGradient_apply {d : ℕ}
    (f : Vec d → ℝ) (x : Vec d) (i : Fin d) :
    classicalGradient f x i =
      (fderiv ℝ f x) (basisVec i) :=
  rfl

/-- A continuous linear functional on native vectors is reconstructed from
its values on the coordinate basis. -/
theorem ContinuousLinearMap.apply_eq_vecDot_basisValues
    {d : ℕ} (L : Vec d →L[ℝ] ℝ) (v : Vec d) :
    L v = vecDot (fun i => L (basisVec i)) v := by
  calc
    L v = L (∑ i : Fin d, v i • basisVec i) := by
      rw [sum_smul_basisVec]
    _ = ∑ i : Fin d, v i * L (basisVec i) := by
      simp
    _ = ∑ i : Fin d, L (basisVec i) * v i := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = vecDot (fun i => L (basisVec i)) v := by
      rfl

/-- Directional derivatives are Euclidean dot products with the coordinate
gradient. -/
theorem fderiv_apply_eq_vecDot_classicalGradient {d : ℕ}
    (f : Vec d → ℝ) (x v : Vec d) :
    (fderiv ℝ f x) v = vecDot (classicalGradient f x) v :=
  PDE.ContinuousLinearMap.apply_eq_vecDot_basisValues
    (fderiv ℝ f x) v

/-- Euclidean Cauchy--Schwarz for a directional derivative. -/
theorem abs_fderiv_apply_le_vecEuclideanNorm_gradient_mul {d : ℕ}
    (f : Vec d → ℝ) (x v : Vec d) :
    |(fderiv ℝ f x) v| ≤
      vecEuclideanNorm (classicalGradient f x) *
        vecEuclideanNorm v := by
  rw [fderiv_apply_eq_vecDot_classicalGradient]
  exact abs_vecDot_le_vecEuclideanNorm_mul _ _

/-- The coordinate gradient of a `C¹` function is continuous. -/
theorem ContDiff.continuous_classicalGradient {d : ℕ}
    {f : Vec d → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (classicalGradient f) := by
  apply continuous_pi
  intro i
  exact
    (hf.continuous_fderiv (by simp)).clm_apply
      continuous_const

end PDE

module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import PDEFoundation.Ambient.Basis

/-!
# Native spatial coordinate derivatives

This module defines first and ordered second classical derivatives along the
native coordinate basis of `PDE.Vec d`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

/-- Classical derivative in one native spatial coordinate. -/
noncomputable def spatialPartial {d : ℕ} (i : Fin d)
    (f : PDE.Vec d → ℝ) (y : PDE.Vec d) : ℝ :=
  (fderiv ℝ f y) (PDE.basisVec i)

/-- A spatial coordinate derivative lowers finite differentiability by one
on an open set. -/
theorem ContDiffOn.spatialPartial
    {d n : ℕ} {O : Set (PDE.Vec d)} {f : PDE.Vec d → ℝ}
    (hf : ContDiffOn ℝ (n + 1) f O)
    (hO : IsOpen O) (k : Fin d) :
    ContDiffOn ℝ n (spatialPartial k f) O := by
  have hdf : ContDiffOn ℝ n (fderiv ℝ f) O :=
    hf.fderiv_of_isOpen hO (by simp)
  exact ContDiffOn.clm_apply hdf contDiffOn_const

/-- Ordered classical second derivative `∂_i(∂_j q)`. -/
noncomputable def spatialSecond {d : ℕ} (q : PDE.Vec d → ℝ)
    (j i : Fin d) (y : PDE.Vec d) : ℝ :=
  spatialPartial i (spatialPartial j q) y

end HypoellipticAleksandrov.Parabolic

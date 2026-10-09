module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Basic.Real.Basic

/-!
# Ambient carriers

The common finite-dimensional carriers used by the PDE libraries. The
inherited norm on `Vec d` is the finite-product supremum norm; Euclidean
quadratic structure is defined explicitly in `PDEFoundation.Ambient.EuclideanNorm`.
-/

@[expose] public section

namespace PDE

/-- The native coordinate model of `ℝ^d`. -/
abbrev Vec (d : ℕ) := Fin d → ℝ

/-- Real `d × d` matrices acting on project vectors. -/
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

end PDE

module

public import PDEFoundation.Ambient.EuclideanNorm
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Internal Hilbert realization of native vectors

Functional-analytic constructions sometimes need the Euclidean norm as the
typeclass norm. This file provides an internal `PiLp 2` realization together
with exact conversions to the native carrier `PDE.Vec`.

The native carrier remains the public ambient-space API. The wrapper in this
file is used only behind the conversion and norm identities below.
-/

@[expose] public section

namespace PDE

/-- Internal Hilbert realization of a native `d`-vector. -/
abbrev HilbertVec (d : ℕ) :=
  PiLp 2 (fun _ : Fin d => ℝ)

/-- Put a native vector into the internal Hilbert realization. -/
def Vec.toHilbertVec {d : ℕ} (x : Vec d) : HilbertVec d :=
  WithLp.toLp 2 x

/-- Return an internal Hilbert vector to the native coordinate carrier. -/
def HilbertVec.toVec {d : ℕ} (x : HilbertVec d) : Vec d :=
  WithLp.ofLp x

@[simp]
theorem Vec.toHilbertVec_apply {d : ℕ} (x : Vec d) (i : Fin d) :
    x.toHilbertVec i = x i :=
  rfl

@[simp]
theorem HilbertVec.toVec_apply {d : ℕ} (x : HilbertVec d) (i : Fin d) :
    x.toVec i = x i :=
  rfl

@[simp]
theorem HilbertVec.toVec_toHilbertVec {d : ℕ} (x : Vec d) :
    x.toHilbertVec.toVec = x :=
  rfl

@[simp]
theorem Vec.toHilbertVec_toVec {d : ℕ} (x : HilbertVec d) :
    x.toVec.toHilbertVec = x :=
  rfl

/-- The internal Hilbert norm is exactly the explicit Euclidean norm on the
native carrier. -/
theorem HilbertVec.norm_eq_vecEuclideanNorm {d : ℕ} (x : HilbertVec d) :
    ‖x‖ = vecEuclideanNorm x.toVec := by
  rw [PiLp.norm_eq_of_L2]
  simp only [Real.norm_eq_abs, sq_abs, vecEuclideanNorm,
    vecNormSq_eq_sum_sq, HilbertVec.toVec_apply]

/-- The explicit Euclidean norm of a native vector is the norm of its internal
Hilbert realization. -/
theorem Vec.vecEuclideanNorm_eq_norm_toHilbertVec {d : ℕ} (x : Vec d) :
    vecEuclideanNorm x = ‖x.toHilbertVec‖ := by
  rw [HilbertVec.norm_eq_vecEuclideanNorm,
    HilbertVec.toVec_toHilbertVec]

end PDE

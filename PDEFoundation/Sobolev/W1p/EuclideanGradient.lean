module

public import PDEFoundation.Measure.LpSpace
public import PDEFoundation.Sobolev.W1p.Basic
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Euclidean-gradient `L^p` representatives

The native gradient carrier `PDE.Vec d` has the finite-product supremum norm.
For Sobolev estimates, the gradient magnitude is instead the explicit
Euclidean norm `PDE.vecEuclideanNorm`.  This file transports native vector
fields to the internal Hilbert carrier and records the exact, factor-free
norm and `L^p` membership identities.

The coordinatewise predicate `PDE.GradMemLpOn` remains the compatibility
surface for existing developments.  Its equivalence with Hilbert-vector
`L^p` membership is exact and holds for every exponent.
-/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace PDE

open MeasureTheory

/-- Reinterpret a native vector field in the internal Euclidean Hilbert
carrier. -/
def toHilbertVecField {d : ℕ} (F : Vec d → Vec d) :
    Vec d → HilbertVec d :=
  fun x => (F x).toHilbertVec

@[simp]
theorem toHilbertVecField_apply {d : ℕ} (F : Vec d → Vec d)
    (x : Vec d) :
    toHilbertVecField F x = (F x).toHilbertVec :=
  rfl

/-- The internal Hilbert lift commutes exactly with pointwise subtraction. -/
@[simp]
theorem toHilbertVecField_sub {d : ℕ}
    (F G : Vec d → Vec d) :
    toHilbertVecField F - toHilbertVecField G =
      toHilbertVecField (fun x => F x - G x) := by
  funext x
  ext i
  rfl

/-- The Hilbert norm of a lifted native field is exactly its explicit
Euclidean magnitude.  There is no dimension-dependent comparison factor. -/
theorem norm_toHilbertVecField_apply {d : ℕ} (F : Vec d → Vec d)
    (x : Vec d) :
    ‖toHilbertVecField F x‖ = vecEuclideanNorm (F x) :=
  (Vec.vecEuclideanNorm_eq_norm_toHilbertVec (F x)).symm

/-- The `L^p` seminorm of the Hilbert lift is exactly the scalar `L^p`
seminorm of the explicit Euclidean magnitude, for an a.e. strongly measurable
field. -/
theorem eLpNorm_toHilbertVecField_eq
    {d : ℕ} (μ : Measure (Vec d)) (p : ℝ≥0∞)
    (F : Vec d → Vec d) (hF : AEStronglyMeasurable F μ) :
    eLpNorm (toHilbertVecField F) p μ =
      eLpNorm (fun x => vecEuclideanNorm (F x)) p μ := by
  calc
    eLpNorm (toHilbertVecField F) p μ =
        eLpNorm (fun x => ‖toHilbertVecField F x‖) p μ :=
      (eLpNorm_norm (toHilbertVecField F)
        ((PiLp.continuous_toLp 2 _).comp_aestronglyMeasurable hF)).symm
    _ = eLpNorm (fun x => vecEuclideanNorm (F x)) p μ := by
      apply eLpNorm_congr_ae
      exact Filter.Eventually.of_forall
        (norm_toHilbertVecField_apply F)

/-- Coordinatewise `L^p` membership of a native gradient is exactly
`L^p` membership of its Euclidean Hilbert lift. -/
theorem gradMemLpOn_iff_memLp_toHilbertVecField
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    {Du : Vec d → Vec d} :
    GradMemLpOn U p Du ↔
      MemLp (toHilbertVecField Du) p (volumeOn U) := by
  simpa only [GradMemLpOn, MemLpOn, toHilbertVecField,
    Vec.toHilbertVec_apply] using
    (memLp_piLp_iff
      (f := toHilbertVecField Du)
      (p := p) (μ := volumeOn U)).symm

namespace MemLpOn

/-- Promote a scalar representative on `U` to its quotient `L^p(U)` class. -/
def toScalarLp {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    {u : Vec d → ℝ} (hu : MemLpOn U p u) :
    ScalarLp U p :=
  hu.toLp u

/-- The scalar quotient class agrees almost everywhere with the representative
used to construct it. -/
theorem coeFn_toScalarLp {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    {u : Vec d → ℝ} (hu : MemLpOn U p u) :
    ⇑hu.toScalarLp =ᵐ[volumeOn U] u :=
  hu.coeFn_toLp

end MemLpOn

namespace GradMemLpOn

/-- Coordinatewise native-vector `L^p` membership implies scalar `L^p`
membership of the exact Euclidean magnitude, with no dimension-dependent
comparison factor. -/
theorem memLp_vecEuclideanNorm
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    {Du : Vec d → Vec d} (hDu : GradMemLpOn U p Du) :
    MemLp (fun x => vecEuclideanNorm (Du x)) p (volumeOn U) := by
  have hHilbert :
      MemLp (toHilbertVecField Du) p (volumeOn U) :=
    gradMemLpOn_iff_memLp_toHilbertVecField.mp hDu
  exact hHilbert.norm.ae_eq
    (Filter.Eventually.of_forall
      (norm_toHilbertVecField_apply Du))

/-- Promote a native gradient representative to Euclidean Hilbert-vector
`L^p(U)`. -/
def toHilbertVectorLp {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    {Du : Vec d → Vec d} (hDu : GradMemLpOn U p Du) :
    HilbertVectorLp U p :=
  (gradMemLpOn_iff_memLp_toHilbertVecField.mp hDu).toLp
    (toHilbertVecField Du)

/-- The Hilbert-vector quotient class agrees almost everywhere with the
lifted native gradient used to construct it. -/
theorem coeFn_toHilbertVectorLp
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    {Du : Vec d → Vec d} (hDu : GradMemLpOn U p Du) :
    ⇑hDu.toHilbertVectorLp =ᵐ[volumeOn U] toHilbertVecField Du :=
  (gradMemLpOn_iff_memLp_toHilbertVecField.mp hDu).coeFn_toLp

/-- Coordinatewise form of
`PDE.GradMemLpOn.coeFn_toHilbertVectorLp`. -/
theorem coeFn_toHilbertVectorLp_apply
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    {Du : Vec d → Vec d} (hDu : GradMemLpOn U p Du)
    (i : Fin d) :
    (fun x => hDu.toHilbertVectorLp x i) =ᵐ[volumeOn U]
      fun x => Du x i := by
  filter_upwards [hDu.coeFn_toHilbertVectorLp] with x hx
  exact congrArg (fun y : HilbertVec d => y i) hx

end GradMemLpOn

end PDE

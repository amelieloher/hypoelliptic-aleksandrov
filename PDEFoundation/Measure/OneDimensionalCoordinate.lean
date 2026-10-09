module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import PDEFoundation.Ambient.Basic
public import PDEFoundation.Geometry.AxisBox

/-!
# Native one-coordinate transport

This module identifies the project's native `Vec 1` carrier with scalar
Lebesgue measure.  The identification is the measurable equivalence supplied
by Mathlib for functions from a unique index type, so it preserves volume
exactly rather than merely up to an unspecified normalization.
-/

@[expose] public section

namespace PDE

open MeasureTheory Set

noncomputable section

/-- The sole-coordinate measurable equivalence from native `Vec 1` to
scalars. -/
def vecOneEquivReal : Vec 1 ≃ᵐ ℝ :=
  MeasurableEquiv.funUnique (Fin 1) ℝ

/-- The scalar coordinate of a native one-coordinate vector. -/
def vecOneCoordinate (x : Vec 1) : ℝ := x 0

/-- The native one-coordinate lift of a scalar. -/
def scalarToVecOne (t : ℝ) : Vec 1 := fun _ => t

/-- The native one-coordinate realization of a scalar open interval. -/
def oneDimensionalAxisBox (a b : ℝ) : Set (Vec 1) :=
  axisBox (fun _ => a) (fun _ => b)

/-- Pull a scalar function back along the sole coordinate of `Vec 1`. -/
def liftOneDimensional (f : ℝ → ℝ) : Vec 1 → ℝ :=
  fun x => f (vecOneCoordinate x)

@[simp] theorem vecOneEquivReal_apply (x : Vec 1) :
    vecOneEquivReal x = vecOneCoordinate x := by
  rw [vecOneEquivReal, MeasurableEquiv.funUnique_apply]
  change x default = x 0
  congr 1

@[simp] theorem vecOneEquivReal_symm_apply (t : ℝ) :
    vecOneEquivReal.symm t = scalarToVecOne t := by
  funext i
  rw [vecOneEquivReal, MeasurableEquiv.funUnique_symm_apply]
  rfl

@[simp] theorem vecOneCoordinate_scalarToVecOne (t : ℝ) :
    vecOneCoordinate (scalarToVecOne t) = t :=
  rfl

@[simp] theorem scalarToVecOne_vecOneCoordinate (x : Vec 1) :
    scalarToVecOne (vecOneCoordinate x) = x := by
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rfl

/-- The native coordinate equivalence preserves the project's volume measure
exactly. -/
theorem volumePreserving_vecOneEquivReal :
    MeasurePreserving vecOneEquivReal
      (volume : Measure (Vec 1)) (volume : Measure ℝ) := by
  simpa only [vecOneEquivReal] using!
    (volume_preserving_funUnique (Fin 1) ℝ)

/-- Membership in a native one-coordinate interval is precisely membership
of the scalar coordinate in the corresponding open interval. -/
@[simp] theorem mem_oneDimensionalAxisBox_iff {a b : ℝ} {x : Vec 1} :
    x ∈ oneDimensionalAxisBox a b ↔ vecOneCoordinate x ∈ Ioo a b := by
  change x ∈ axisBox (fun _ => a) (fun _ => b) ↔ _
  constructor
  · intro hx
    exact hx 0 (Set.mem_univ 0)
  · intro hx i _
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact hx

/-- The scalar interval is the exact preimage of the corresponding native
axis box under the volume-preserving coordinate equivalence. -/
theorem vecOneEquivReal_preimage_Ioo (a b : ℝ) :
    vecOneEquivReal ⁻¹' Ioo a b = oneDimensionalAxisBox a b := by
  ext x
  rw [Set.mem_preimage, vecOneEquivReal_apply]
  exact mem_oneDimensionalAxisBox_iff.symm

/-- Exact transport of a scalar set integral to the native one-coordinate
axis box. -/
theorem setIntegral_axisBox_one_eq_setIntegral_Ioo
    {f : ℝ → ℝ} (a b : ℝ) :
    (∫ x in oneDimensionalAxisBox a b, liftOneDimensional f x) =
      ∫ t in Ioo a b, f t := by
  rw [← vecOneEquivReal_preimage_Ioo a b]
  simpa only [Function.comp_apply, vecOneEquivReal_apply, liftOneDimensional] using
    (volumePreserving_vecOneEquivReal.setIntegral_preimage_emb
      vecOneEquivReal.measurableEmbedding f (Ioo a b))

/-- Exact `IntegrableOn` transport between a scalar interval and its native
one-coordinate axis box. -/
theorem integrableOn_axisBox_one_iff_integrableOn_Ioo
    {f : ℝ → ℝ} (a b : ℝ) :
    IntegrableOn (liftOneDimensional f) (oneDimensionalAxisBox a b) ↔
      IntegrableOn f (Ioo a b) := by
  rw [← vecOneEquivReal_preimage_Ioo a b]
  simpa only [Function.comp_apply, vecOneEquivReal_apply, liftOneDimensional] using!
    (volumePreserving_vecOneEquivReal.integrableOn_comp_preimage
      vecOneEquivReal.measurableEmbedding (f := f) (s := Ioo a b))

end

end PDE

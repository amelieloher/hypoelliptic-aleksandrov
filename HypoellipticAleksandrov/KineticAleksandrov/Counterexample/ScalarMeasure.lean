module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarClassical
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # Exact one-dimensional native coordinate and volume equivalence -/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory

/-- Literal native point with scalar position and velocity coordinates. -/
def scalarPoint (x v : ℝ) : XV 1 := (fun _ => x, fun _ => v)

/-- Coordinate evaluation is a measurable equivalence, with no Euclidean carrier replacement. -/
def scalarNativeCoordinates : XV 1 ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.funUnique (Fin 1) ℝ).prodCongr (MeasurableEquiv.funUnique (Fin 1) ℝ)

/-- The inverse coordinate map is exactly the literal native point constructor. -/
theorem scalarNativeCoordinates_symm_apply (p : ℝ × ℝ) :
    scalarNativeCoordinates.symm p = scalarPoint p.1 p.2 := rfl

/-- Coordinate evaluation preserves precisely the native product volume normalization. -/
theorem scalarNativeCoordinates_measurePreserving :
    MeasurePreserving scalarNativeCoordinates volume volume := by
  have hh := (volume_preserving_funUnique (Fin 1) ℝ).prod
    (volume_preserving_funUnique (Fin 1) ℝ)
  rw [Measure.volume_eq_prod, Measure.volume_eq_prod]
  convert hh using 1
  · funext q
    rfl
  · rfl

/-- The inverse coordinate map also preserves the exact product volume normalization. -/
theorem scalarNativeCoordinates_symm_measurePreserving :
    MeasurePreserving scalarNativeCoordinates.symm volume volume :=
  MeasurePreserving.symm scalarNativeCoordinates scalarNativeCoordinates_measurePreserving

/-- Scalar coordinate construction is continuous as a native product-valued map. -/
theorem scalarPoint_continuous : Continuous (fun p : ℝ × ℝ => scalarPoint p.1 p.2) := by
  unfold scalarPoint
  fun_prop

/-- The position-line tangent is the native position basis vector. -/
theorem scalarPoint_hasDerivAt_x (x v : ℝ) :
    HasDerivAt (fun t => scalarPoint t v) (Pi.single 0 1, 0) x :=
  scalarPositionSlice_hasDerivAt (scalarPoint 0 v) x

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

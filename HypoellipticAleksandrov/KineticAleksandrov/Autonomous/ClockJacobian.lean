module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockGeometry
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import PDEFoundation.Measure.OneDimensionalCoordinate
import Mathlib.Tactic.FinCases

/-! # Affine clock Jacobian in scalar coordinates

Scalar coordinates use Mathlib's native `Fin 3 → ℝ`, in the order `(sigma,z,y)`
for inputs of the inverse and `(s,X,v)` for its outputs.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open MeasureTheory

/-- Physical scalar coordinates on the existing kinetic point carrier. -/
def scalarCoordinates (p : Point) : Fin 3 → ℝ := ![p.time, p.position 0, p.velocity 0]

/-- Reconstruct a kinetic point from scalar coordinates. -/
def scalarPoint (p : Fin 3 → ℝ) : Point := ⟨p 0, fun _ => p 1, fun _ => p 2⟩

/-- Scalar coordinates retain all information on the one-dimensional kinetic carrier. -/
theorem scalarPoint_coordinates (p : Point) : scalarPoint (scalarCoordinates p) = p := by
  ext i
  · rfl
  · have hi := Fin.eq_zero i
    subst i
    rfl
  · have hi := Fin.eq_zero i
    subst i
    rfl

/-- The coordinate reconstruction is an inverse in the other direction as well. -/
theorem scalarCoordinates_point (p : Fin 3 → ℝ) : scalarCoordinates (scalarPoint p) = p := by
  ext i
  fin_cases i <;> rfl

/-- The actual matrix of the inverse clock's linear part. -/
def Clock.inverseMatrix (c : Clock) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![c.r ^ 2, -(c.r ^ 3 / c.vbar), 0;
    c.vbar * c.r ^ 2, 0, 0;
    0, 0, c.r]

/-- The inverse clock written on native scalar coordinates. -/
def Clock.inverseCoordinates (c : Clock) (e : Point) (q : Fin 3 → ℝ) : Fin 3 → ℝ :=
  scalarCoordinates (c.inverse e (scalarPoint q))

/-- Its linear part plus its physical starting-point translation is exactly the inverse clock. -/
theorem Clock.inverseCoordinates_eq (c : Clock) (e : Point) (q : Fin 3 → ℝ) :
    c.inverseCoordinates e q = c.inverseMatrix.mulVec q + ![e.time, e.position 0, c.vbar] := by
  ext i
  fin_cases i <;>
    simp [Clock.inverseCoordinates, Clock.inverseMatrix, Clock.inverse,
      scalarCoordinates, scalarPoint, dotProduct, Fin.sum_univ_succ] <;> ring

/-- The inverse clock determinant is positive and equals the source factor `r^6`. -/
theorem Clock.det_inverseMatrix (c : Clock) : c.inverseMatrix.det = c.r ^ 6 := by
  simp [Clock.inverseMatrix, Matrix.det_fin_three]
  field_simp [c.nonzero]

/-- The absolute Jacobian of the inverse is exactly the source normalization. -/
theorem Clock.abs_det_inverseMatrix (c : Clock) : |c.inverseMatrix.det| = c.r ^ 6 := by
  rw [c.det_inverseMatrix, abs_of_nonneg (pow_nonneg c.positive.le 6)]

/-- The displayed matrix is the genuine Frechet derivative of the affine inverse clock. -/
theorem Clock.hasFDerivAt_inverseCoordinates (c : Clock) (e : Point) (q : Fin 3 → ℝ) :
    HasFDerivAt (c.inverseCoordinates e)
      (Matrix.toLin' c.inverseMatrix).toContinuousLinearMap q := by
  have heq : c.inverseCoordinates e =
      fun q => Matrix.toLin' c.inverseMatrix q + ![e.time, e.position 0, c.vbar] := by
    funext q
    exact c.inverseCoordinates_eq e q
  rw [heq]
  exact (Matrix.toLin' c.inverseMatrix).toContinuousLinearMap.hasFDerivAt.add_const _

/-- In scalar coordinates, the inverse clock pushes volume to `r^(-6)` times volume. -/
theorem Clock.map_inverseCoordinates_volume (c : Clock) (e : Point) :
    Measure.map (c.inverseCoordinates e) volume =
      ENNReal.ofReal ((c.r ^ 6)⁻¹) • (volume : Measure (Fin 3 → ℝ)) := by
  have hdet : c.inverseMatrix.det ≠ 0 := by
    rw [c.det_inverseMatrix]
    exact pow_ne_zero _ (ne_of_gt c.positive)
  have heq : c.inverseCoordinates e =
      (fun p : Fin 3 → ℝ => p + ![e.time, e.position 0, c.vbar]) ∘
        Matrix.toLin' c.inverseMatrix := by
    funext q
    exact c.inverseCoordinates_eq e q
  rw [heq, ← Measure.map_map (by fun_prop) (by fun_prop),
    Real.map_matrix_volume_pi_eq_smul_volume_pi hdet, Measure.map_smul _ (by fun_prop),
    map_add_right_eq_self]
  rw [abs_inv, c.abs_det_inverseMatrix]

/-- The literal scalar-coordinate measurable equivalence. -/
def scalarMeasurableEquiv : Point ≃ᵐ (Fin 3 → ℝ) where
  toFun := scalarCoordinates
  invFun := scalarPoint
  left_inv := scalarPoint_coordinates
  right_inv := scalarCoordinates_point
  measurable_toFun := by
    apply Measurable.of_eval
    intro i
    fin_cases i
    · exact continuous_time.measurable
    · exact (continuous_apply 0 |>.comp continuous_position).measurable
    · exact (continuous_apply 0 |>.comp continuous_velocity).measurable
  measurable_invFun := by
    change Measurable ((KineticPoint.equivProd 1).symm ∘
      fun p : Fin 3 → ℝ => (p 0, (fun _ => p 1, fun _ => p 2)))
    exact (KineticPoint.measurable_equivProd_symm 1).comp
      ((measurable_pi_apply 0).prodMk
        ((Measurable.of_eval fun _ => measurable_pi_apply 1).prodMk
          (Measurable.of_eval fun _ => measurable_pi_apply 2)))

/-- The scalar coordinates preserve the source product volume without any factor. -/
theorem scalarCoordinates_volumePreserving :
    MeasurePreserving scalarMeasurableEquiv volume volume := by
  have hp := KineticPoint.measurePreserving_equivProd 1
  have hv := PDE.volumePreserving_vecOneEquivReal.prod
    PDE.volumePreserving_vecOneEquivReal
  have ht := (MeasurePreserving.id (volume : Measure ℝ)).prod hv
  have hf := (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).symm
  have hh := (MeasurePreserving.id (volume : Measure ℝ)).prod hf
  have hs := (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm
  have hm := hs.comp (hh.comp (ht.comp hp))
  apply hm.congr scalarMeasurableEquiv.measurable
  apply Filter.Eventually.of_forall
  intro p
  ext i
  fin_cases i <;> rfl

/-- The inverse clock rescales the actual kinetic volume, not a replacement measure. -/
theorem Clock.map_inverse_volume (c : Clock) (e : Point) :
    Measure.map (c.inverse e) volume = ENNReal.ofReal ((c.r ^ 6)⁻¹) •
      (volume : Measure Point) := by
  have hpoint := scalarCoordinates_volumePreserving.symm
  have heq : c.inverse e = scalarPoint ∘ c.inverseCoordinates e ∘ scalarCoordinates := by
    funext p
    simp only [Clock.inverseCoordinates, Function.comp_apply,
      scalarPoint_coordinates]
  have hc : Measurable scalarCoordinates := scalarMeasurableEquiv.measurable
  have hp : Measurable scalarPoint := scalarMeasurableEquiv.symm.measurable
  have hi : Measurable (c.inverseCoordinates e) := by
    rw [show c.inverseCoordinates e = fun p =>
      Matrix.toLin' c.inverseMatrix p + ![e.time, e.position 0, c.vbar] from
        funext (c.inverseCoordinates_eq e)]
    fun_prop
  have hm : Measure.map scalarCoordinates volume = volume :=
    scalarCoordinates_volumePreserving.map_eq
  rw [heq, ← Measure.map_map hp (hi.comp hc), ← Measure.map_map hi hc,
    hm, c.map_inverseCoordinates_volume,
    Measure.map_smul _ hp.aemeasurable]
  exact congrArg (fun m => ENNReal.ofReal ((c.r ^ 6)⁻¹) • m) hpoint.map_eq

/-- The forward clock in the same native scalar coordinates as its inverse. -/
def Clock.mapCoordinates (c : Clock) (e : Point) (q : Fin 3 → ℝ) : Fin 3 → ℝ :=
  scalarCoordinates (c.map e (scalarPoint q))

/-- Smoothness of the global forward coordinate map. -/
theorem Clock.mapCoordinates_smooth (c : Clock) (e : Point) :
    ContDiff ℝ (⊤ : ℕ∞) (c.mapCoordinates e) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;>
    dsimp [Clock.mapCoordinates, Clock.map, scalarCoordinates, scalarPoint] <;> fun_prop

/-- Smoothness of the global inverse coordinate map. -/
theorem Clock.inverseCoordinates_smooth (c : Clock) (e : Point) :
    ContDiff ℝ (⊤ : ℕ∞) (c.inverseCoordinates e) := by
  rw [show c.inverseCoordinates e = fun p =>
    Matrix.toLin' c.inverseMatrix p + ![e.time, e.position 0, c.vbar] from
      funext (c.inverseCoordinates_eq e)]
  exact (Matrix.toLin' c.inverseMatrix).toContinuousLinearMap.contDiff.add contDiff_const

/-- In the forward direction the source volume formula has factor `r^6`. -/
theorem Clock.map_volume (c : Clock) (e : Point) :
    Measure.map (c.map e) volume = ENNReal.ofReal (c.r ^ 6) •
      (volume : Measure Point) := by
  have hr : 0 < c.r ^ 6 := pow_pos c.positive 6
  have hs : ENNReal.ofReal (c.r ^ 6) • Measure.map (c.inverse e) volume =
      (volume : Measure Point) := by
    rw [c.map_inverse_volume, smul_smul, ← ENNReal.ofReal_mul hr.le,
      mul_inv_cancel₀ (ne_of_gt hr), ENNReal.ofReal_one, one_smul]
  have heq : c.map e ∘ c.inverse e = id := funext (c.map_inverse e)
  calc
    Measure.map (c.map e) volume =
        Measure.map (c.map e) (ENNReal.ofReal (c.r ^ 6) •
          Measure.map (c.inverse e) volume) := congrArg (Measure.map (c.map e)) hs.symm
    _ = ENNReal.ofReal (c.r ^ 6) • volume := by
      rw [Measure.map_smul _ (c.continuous_map e).measurable.aemeasurable,
        Measure.map_map (c.continuous_map e).measurable
          (c.continuous_inverse e).measurable, heq, Measure.map_id]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

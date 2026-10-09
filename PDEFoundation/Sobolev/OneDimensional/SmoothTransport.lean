module

public import PDEFoundation.Ambient.Basis
public import PDEFoundation.Measure.OneDimensionalCoordinate

/-!
# Smooth transport between `Vec 1` and scalars

The smooth-test-function bridge for one-dimensional weak derivatives is an
exact change of variables on the native carrier.  It uses the continuous
linear `piUnique` equivalence, while measure transport remains in
`OneDimensionalCoordinate`.
-/

@[expose] public section

namespace PDE

open MeasureTheory Set

noncomputable section

/-- The continuous linear scalar-to-native-one-coordinate equivalence. -/
def scalarToVecOneContinuousLinearEquiv : ℝ ≃L[ℝ] Vec 1 :=
  (ContinuousLinearEquiv.piUnique ℝ (fun _ : Fin 1 => ℝ)).symm

@[simp] theorem scalarToVecOneContinuousLinearEquiv_apply (t : ℝ) :
    scalarToVecOneContinuousLinearEquiv t = scalarToVecOne t := by
  funext i
  rw [scalarToVecOneContinuousLinearEquiv,
    ContinuousLinearEquiv.piUnique_symm_apply]
  rfl

@[simp] theorem scalarToVecOneContinuousLinearEquiv_one :
    scalarToVecOneContinuousLinearEquiv (1 : ℝ) = basisVec (0 : Fin 1) := by
  rw [scalarToVecOneContinuousLinearEquiv_apply]
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp [scalarToVecOne, basisVec]

/-- Pull a native smooth scalar function back to the scalar coordinate. -/
def scalarPullbackOne (φ : Vec 1 → ℝ) : ℝ → ℝ :=
  fun t => φ (scalarToVecOne t)

@[simp] theorem scalarPullbackOne_apply (φ : Vec 1 → ℝ) (t : ℝ) :
    scalarPullbackOne φ t = φ (scalarToVecOne t) :=
  rfl

/-- `C^n` regularity transports from the native one-coordinate carrier to
the scalar carrier without a loss of differentiability. -/
theorem ContDiff.scalarPullbackOne {n : WithTop ℕ∞} {φ : Vec 1 → ℝ}
    (hφ : ContDiff ℝ n φ) :
    ContDiff ℝ n (scalarPullbackOne φ) := by
  have he : ContDiff ℝ n scalarToVecOneContinuousLinearEquiv :=
    scalarToVecOneContinuousLinearEquiv.contDiff
  simpa only [scalarPullbackOne, Function.comp_apply,
    scalarToVecOneContinuousLinearEquiv_apply] using! hφ.comp he

/-- The scalar derivative of the pulled-back native function is exactly its
native directional derivative in the sole coordinate direction. -/
theorem deriv_scalarPullbackOne_eq_native_directional
    {φ : Vec 1 → ℝ} (hφ : ContDiff ℝ 1 φ) (t : ℝ) :
    deriv (scalarPullbackOne φ) t =
      (fderiv ℝ φ (scalarToVecOne t)) (basisVec (0 : Fin 1)) := by
  have hφdiff : DifferentiableAt ℝ φ (scalarToVecOne t) := by
    simpa only [scalarToVecOneContinuousLinearEquiv_apply] using
      (hφ.differentiable (by norm_num) (scalarToVecOneContinuousLinearEquiv t))
  have hcomp := hφdiff.hasFDerivAt.comp t
    scalarToVecOneContinuousLinearEquiv.hasFDerivAt
  have hderiv := hcomp.hasDerivAt.deriv
  have hone : scalarToVecOneContinuousLinearEquiv (1 : ℝ) =
      basisVec (0 : Fin 1) := scalarToVecOneContinuousLinearEquiv_one
  have hone' : (↑scalarToVecOneContinuousLinearEquiv : ℝ →L[ℝ] Vec 1) 1 =
      basisVec (0 : Fin 1) := hone
  rw [ContinuousLinearMap.comp_apply] at hderiv
  rw [hone'] at hderiv
  simpa only [scalarPullbackOne, Function.comp_apply,
    scalarToVecOneContinuousLinearEquiv_apply, ContinuousLinearMap.comp_apply] using! hderiv

/-- Topological-support containment transports from a native one-coordinate
axis box to the corresponding scalar interval. -/
theorem tsupport_scalarPullbackOne_subset_Ioo
    {φ : Vec 1 → ℝ} {a b : ℝ}
    (hφ : tsupport φ ⊆ oneDimensionalAxisBox a b) :
    tsupport (scalarPullbackOne φ) ⊆ Ioo a b := by
  have hpull : scalarPullbackOne φ = φ ∘ scalarToVecOneContinuousLinearEquiv := by
    funext t
    simp only [scalarPullbackOne, Function.comp_apply,
      scalarToVecOneContinuousLinearEquiv_apply]
  rw [hpull]
  change tsupport (φ ∘ scalarToVecOneContinuousLinearEquiv.toHomeomorph) ⊆ Ioo a b
  rw [tsupport_comp_eq_preimage φ scalarToVecOneContinuousLinearEquiv.toHomeomorph]
  intro t ht
  have hbox : scalarToVecOneContinuousLinearEquiv t ∈ oneDimensionalAxisBox a b :=
    hφ ht
  have hcoord := mem_oneDimensionalAxisBox_iff.mp hbox
  simpa only [scalarToVecOneContinuousLinearEquiv_apply,
    vecOneCoordinate_scalarToVecOne] using hcoord

/-- A native one-coordinate function is exactly the native lift of its scalar
pullback. -/
theorem liftOneDimensional_scalarPullbackOne (φ : Vec 1 → ℝ) :
    liftOneDimensional (scalarPullbackOne φ) = φ := by
  funext x
  simp only [liftOneDimensional, scalarPullbackOne,
    scalarToVecOne_vecOneCoordinate]

/-- Exact scalar/native integral transport for a native one-coordinate test
function. -/
theorem setIntegral_oneDimensionalAxisBox_eq_scalarPullbackOne
    (φ : Vec 1 → ℝ) (a b : ℝ) :
    (∫ x in oneDimensionalAxisBox a b, φ x) =
      ∫ t in Ioo a b, scalarPullbackOne φ t := by
  rw [← liftOneDimensional_scalarPullbackOne φ]
  exact setIntegral_axisBox_one_eq_setIntegral_Ioo a b

/-- Exact scalar/native integral transport for the sole native directional
derivative of a `C¹` test function. -/
theorem setIntegral_native_directional_eq_deriv_scalarPullbackOne
    {φ : Vec 1 → ℝ} (hφ : ContDiff ℝ 1 φ) (a b : ℝ) :
    (∫ x in oneDimensionalAxisBox a b,
      (fderiv ℝ φ x) (basisVec (0 : Fin 1))) =
      ∫ t in Ioo a b, deriv (scalarPullbackOne φ) t := by
  rw [← setIntegral_axisBox_one_eq_setIntegral_Ioo (a := a) (b := b)
    (f := fun t => deriv (scalarPullbackOne φ) t)]
  apply setIntegral_congr_fun (isOpen_axisBox _ _).measurableSet
  intro x hx
  rw [liftOneDimensional]
  have hx' : scalarToVecOne (vecOneCoordinate x) = x :=
    scalarToVecOne_vecOneCoordinate x
  rw [deriv_scalarPullbackOne_eq_native_directional hφ, hx']

end

end PDE

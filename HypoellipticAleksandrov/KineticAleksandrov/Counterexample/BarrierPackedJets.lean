module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoffProfileChain
import Mathlib.Tactic.Ring

/-! # Literal barrier jets in the measure-preserving spatial chart -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- The packed barrier differential acts only on the native velocity component. -/
theorem spatialPackedBarrier_fderiv (d : ℕ) (mu R t : ℝ)
    (x w : PDE.Vec (d + d)) :
    fderiv ℝ (spatialPackedBarrier d mu R t) x w =
      -(2 * Real.exp (-mu * t) / R ^ 2) *
        PDE.vecDot (spatialCoordinateCLE d x).2 (spatialCoordinateCLE d w).2 := by
  have hv := ((spatialCoordinateCLE d).hasFDerivAt (x := x)).snd
  have h := ((hasFDerivAt_const (c := (2 : ℝ)) x).sub
    (((hasFDerivAt_vecNormSq (spatialCoordinateCLE d x).2).comp x hv).mul_const
      ((R ^ 2)⁻¹))).const_mul (Real.exp (-mu * t))
  have he : HasFDerivAt (spatialPackedBarrier d mu R t)
      (Real.exp (-mu * t) • (0 - (R ^ 2)⁻¹ •
        (vecNormSqFDeriv (spatialCoordinateCLE d x).2).comp
          ((ContinuousLinearMap.snd ℝ (PDE.Vec d) (PDE.Vec d)).comp
            (spatialCoordinateCLE d).toContinuousLinearMap))) x := by
    simpa only [spatialPackedBarrier, barrier, div_eq_mul_inv] using! h
  rw [he.fderiv]
  simp only [_root_.smul_apply, _root_.sub_apply, _root_.zero_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul, vecNormSqFDeriv_apply]
  change Real.exp (-mu * t) *
    (0 - (R ^ 2)⁻¹ * (2 * PDE.vecDot (spatialCoordinateCLE d x).2
      (spatialCoordinateCLE d w).2)) = _
  rw [div_eq_mul_inv]
  ring

/-- The position gradient of the barrier is exactly zero in packed coordinates. -/
theorem spatialPackedBarrier_positionGradient {d : ℕ} (mu R t : ℝ)
    (x : PDE.Vec (d + d)) (i : Fin d) :
    PDE.classicalGradient (spatialPackedBarrier d mu R t) x (Fin.castAdd d i) = 0 := by
  change fderiv ℝ (spatialPackedBarrier d mu R t) x (PDE.basisVec (Fin.castAdd d i)) = 0
  rw [spatialPackedBarrier_fderiv, spatialCoordinate_basis_position]
  simp only [PDE.vecDot, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

/-- The velocity gradient has the same normalization as the native barrier. -/
theorem spatialPackedBarrier_velocityGradient {d : ℕ} (mu R t : ℝ)
    (x : PDE.Vec (d + d)) (i : Fin d) :
    PDE.classicalGradient (spatialPackedBarrier d mu R t) x (Fin.natAdd d i) =
      -(2 * Real.exp (-mu * t) / R ^ 2) * (spatialCoordinateCLE d x).2 i := by
  change fderiv ℝ (spatialPackedBarrier d mu R t) x (PDE.basisVec (Fin.natAdd d i)) = _
  rw [spatialPackedBarrier_fderiv, spatialCoordinate_basis_velocity]
  rw [PDE.vecDot_basisVec_right]

/-- The packed second velocity derivative is the exact diagonal barrier Hessian. -/
theorem spatialPackedBarrier_velocityHessian {d : ℕ} (mu R t : ℝ)
    (x : PDE.Vec (d + d)) (i k : Fin d) :
    PDE.classicalGradient
      (fun y => PDE.classicalGradient (spatialPackedBarrier d mu R t) y (Fin.natAdd d k))
      x (Fin.natAdd d i) =
        -(2 * Real.exp (-mu * t) / R ^ 2) * (1 : PDE.Mat d) i k := by
  have hg : (fun y => PDE.classicalGradient (spatialPackedBarrier d mu R t) y
      (Fin.natAdd d k)) =
      fun y => -(2 * Real.exp (-mu * t) / R ^ 2) * (spatialCoordinateCLE d y).2 k :=
    funext (fun y => spatialPackedBarrier_velocityGradient mu R t y k)
  rw [hg]
  let L : PDE.Vec (d + d) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj k).comp
      ((ContinuousLinearMap.snd ℝ (PDE.Vec d) (PDE.Vec d)).comp
        (spatialCoordinateCLE d).toContinuousLinearMap)
  have he := (L.hasFDerivAt (x := x)).const_mul (-(2 * Real.exp (-mu * t) / R ^ 2))
  change HasFDerivAt
    (fun y => -(2 * Real.exp (-mu * t) / R ^ 2) * (spatialCoordinateCLE d y).2 k) _ x at he
  change fderiv ℝ _ x (PDE.basisVec (Fin.natAdd d i)) = _
  rw [he.fderiv]
  change -(2 * Real.exp (-mu * t) / R ^ 2) *
    (spatialCoordinateCLE d (PDE.basisVec (Fin.natAdd d i))).2 k = _
  rw [spatialCoordinate_basis_velocity]
  simp only [PDE.basisVec_apply, Matrix.one_apply, eq_comm]

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

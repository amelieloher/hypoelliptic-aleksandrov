module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationWeakRegularity
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationWeakIntegration
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeTransfer
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeOperator
public import HypoellipticAleksandrov.Parabolic.HarnackUnitCylinder.ScalarHessian

/-! # Directional jets of the pulled back anisotropic Dirichlet solution -/

@[expose] public section

open Set Filter HypoellipticAleksandrov.Parabolic
open scoped Topology

namespace HypoellipticAleksandrov.KineticAleksandrov.Evolution

variable {n : ℕ}

/-- The straightening map on packed evolution coordinates. -/
def truncationPoint (g : ℝ → PDE.Vec n) (x : EvolutionVec n) : TimeVelocity (n + n) :=
  (timeCoord n x, spatialPack (diffusedCoord n x - g (timeCoord n x)) (transportedCoord n x))

/-- The straightening map is smooth when its curve is smooth. -/
theorem contDiff_truncationPoint {g : ℝ → PDE.Vec n}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) : ContDiff ℝ (⊤ : ℕ∞) (truncationPoint g) :=
  (timeCoord n).contDiff.prodMk (contDiff_spatialPack
    ((diffusedCoord n).contDiff.sub (hg.comp (timeCoord n).contDiff))
    (transportedCoord n).contDiff)

/-- A packed spatial line straightens to a line in the scalar spatial slice. -/
theorem truncationPoint_spatial_line (g : ℝ → PDE.Vec n) (x w : EvolutionVec n)
    (hw : timeCoord n w = 0) (t : ℝ) :
    truncationPoint g (x + t • w) =
      ((truncationPoint g x).1, (truncationPoint g x).2 +
        t • spatialPack (diffusedCoord n w) (transportedCoord n w)) := by
  unfold truncationPoint
  simp only [map_add, map_smul, hw, smul_zero, add_zero]
  congr 1
  rw [show diffusedCoord n x + t • diffusedCoord n w - g (timeCoord n x) =
    (diffusedCoord n x - g (timeCoord n x)) + t • diffusedCoord n w by abel]
  rw [spatialPack_add, spatialPack_smul]

/-- A scalar C1,2 function pulls back with the expected first spatial line derivative. -/
theorem truncation_hasLineDerivAt_spatial {g : ℝ → PDE.Vec n}
    {u : TimeVelocity (n + n) → ℝ} {U : Set (TimeVelocity (n + n))}
    (hu : IsScalarC12On u U) {x w : EvolutionVec n}
    (hx : truncationPoint g x ∈ U) (hw : timeCoord n w = 0) :
    HasLineDerivAt ℝ (u ∘ truncationPoint g)
      (PDE.vecDot (scalarSpatialGradient u (truncationPoint g x))
        (spatialPack (diffusedCoord n w) (transportedCoord n w))) x w := by
  have h := ((hu.spatialSlice_contDiffAt hx).differentiableAt (by norm_num)).hasFDerivAt
    |>.hasLineDerivAt (spatialPack (diffusedCoord n w) (transportedCoord n w))
  rw [PDE.fderiv_apply_eq_vecDot_classicalGradient] at h
  unfold HasLineDerivAt at h ⊢
  simpa only [Function.comp_def, truncationPoint_spatial_line g x w hw,
    scalarSpatialGradient] using! h

/-- Spatial line derivatives of gradient entries are scalar Hessian entries. -/
theorem truncation_gradient_hasLineDerivAt {g : ℝ → PDE.Vec n}
    {u : TimeVelocity (n + n) → ℝ} {U : Set (TimeVelocity (n + n))}
    (hu : IsScalarC12On u U) {x w : EvolutionVec n}
    (hx : truncationPoint g x ∈ U) (hw : timeCoord n w = 0)
    (i j : Fin (n + n))
    (hdir : spatialPack (diffusedCoord n w) (transportedCoord n w) = PDE.basisVec i) :
    HasLineDerivAt ℝ (fun y => scalarSpatialGradient u (truncationPoint g y) j)
      (scalarSpatialHessian u (truncationPoint g x) i j) x w := by
  have hc2 := hu.spatialSlice_contDiffAt hx
  have hd : DifferentiableAt ℝ (fderiv ℝ (fun y => u ((truncationPoint g x).1, y)))
      (truncationPoint g x).2 :=
    (hc2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h := (hd.clm_apply (differentiableAt_const (PDE.basisVec j))).hasFDerivAt
    |>.hasLineDerivAt (PDE.basisVec i)
  have he : fderiv ℝ (fun y => fderiv ℝ
      (fun y => u ((truncationPoint g x).1, y)) y (PDE.basisVec j))
      (truncationPoint g x).2 (PDE.basisVec i) =
      scalarSpatialHessian u (truncationPoint g x) i j := by
    have hz : fderiv ℝ (fun _ : PDE.Vec (n + n) => PDE.basisVec j)
        (truncationPoint g x).2 = 0 := (hasFDerivAt_const (PDE.basisVec j) _).fderiv
    rw [fderiv_clm_apply hd (differentiableAt_const (PDE.basisVec j))]
    erw [hz]
    simpa only [ContinuousLinearMap.comp_zero, zero_add,
      ContinuousLinearMap.flip_apply] using! (scalarSpatialHessian_eq_secondFDeriv hc2 i j).symm
  rw [he] at h
  unfold HasLineDerivAt at h ⊢
  simpa only [truncationPoint_spatial_line g x w hw, hdir,
    scalarSpatialGradient, PDE.classicalGradient] using! h

/-- The time line derivative includes the exact moving-frame correction. -/
theorem truncation_hasLineDerivAt_time {g : ℝ → PDE.Vec n}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) {u : TimeVelocity (n + n) → ℝ}
    {U : Set (TimeVelocity (n + n))} (hU : IsOpen U) (hu : IsScalarC12On u U)
    {x : EvolutionVec n} (hx : truncationPoint g x ∈ U) :
    HasLineDerivAt ℝ (u ∘ truncationPoint g)
      (scalarTimeDerivative u (truncationPoint g x) +
        PDE.vecDot (-deriv g (timeCoord n x))
          (spatialY (scalarSpatialGradient u (truncationPoint g x)))) x basisT := by
  have hdu := scalarC12_differentiableAt hU hu hx
  have hd : DifferentiableAt ℝ (u ∘ truncationPoint g) x :=
    hdu.comp x ((contDiff_truncationPoint hg).differentiable (by simp) x)
  have he : u ∘ truncationPoint g = straightenedPullback g u ∘ evolutionHomeomorph n := rfl
  have h := hd.hasFDerivAt.hasLineDerivAt basisT
  rw [he, ← kineticTimeDerivative_comp (he ▸ hd),
    kineticTimeDerivative_straightenedPullback
      ((hg.differentiable (by simp)) (timeCoord n x)) hdu] at h
  simpa only [← he] using! h

end HypoellipticAleksandrov.KineticAleksandrov.Evolution

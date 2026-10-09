module

public import HypoellipticAleksandrov.Parabolic.ContDiffOnTwoToScalarC12

/-!
# Scalar jets of equal point germs

This module proves that ambient C² functions agreeing near a point have equal
scalar time, gradient, and ordered Hessian jets at that point.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic
open Filter
open scoped Topology
noncomputable section
open TimeVelocityMultiIndex

private theorem scalarTimeDerivative_eq_coordinate_open_local
    {d : ℕ} (u : TimeVelocity d → ℝ) (z : TimeVelocity d)
    (hu : ContDiffAt ℝ 1 u z) :
    scalarTimeDerivative u z =
      coordinateIteratedFDeriv (Pi.single (timeCoord d) 1) u z := by
  have h := coordinateIteratedFDeriv_add_single_at
    (0 : TimeVelocityMultiIndex d) (timeCoord d) u z
      (by simpa [TimeVelocityMultiIndex.order, TimeVelocityMultiIndex.timeOrder,
        TimeVelocityMultiIndex.velocity, VelocityMultiIndex.order] using hu)
  simp only [zero_add, timeVelocityBasis_time] at h
  rw [show coordinateIteratedFDeriv (0 : TimeVelocityMultiIndex d) u = u by
    funext x; exact coordinateIteratedFDeriv_zero u x] at h
  rw [h]
  unfold scalarTimeDerivative
  have hsF := (hu.differentiableAt (by norm_num)).hasFDerivAt.comp z.1
    ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))
  have hs : HasDerivAt (fun r : ℝ ↦ u (r, z.2))
      ((fderiv ℝ u z) (1, 0)) z.1 := by
    convert hsF.hasDerivAt using 1
    all_goals simp [Function.comp_def]
  exact hs.deriv

private theorem scalarSpatialGradient_eq_coordinate_open_local
    {d : ℕ} (u : TimeVelocity d → ℝ) (z : TimeVelocity d) (j : Fin d)
    (hu : ContDiffAt ℝ 1 u z) :
    scalarSpatialGradient u z j =
      coordinateIteratedFDeriv (Pi.single (velocityCoord j) 1) u z := by
  have h := coordinateIteratedFDeriv_add_single_at
    (0 : TimeVelocityMultiIndex d) (velocityCoord j) u z
      (by simpa [TimeVelocityMultiIndex.order, TimeVelocityMultiIndex.timeOrder,
        TimeVelocityMultiIndex.velocity, VelocityMultiIndex.order] using hu)
  simp only [zero_add, timeVelocityBasis_velocity] at h
  rw [show coordinateIteratedFDeriv (0 : TimeVelocityMultiIndex d) u = u by
    funext x; exact coordinateIteratedFDeriv_zero u x] at h
  rw [h, scalarSpatialGradient, PDE.classicalGradient_apply]
  have hs : HasFDerivAt (fun y : PDE.Vec d ↦ u (z.1, y))
      ((fderiv ℝ u z).comp (ContinuousLinearMap.inr ℝ ℝ (PDE.Vec d))) z.2 :=
    (hu.differentiableAt (by norm_num)).hasFDerivAt.comp z.2
      ((hasFDerivAt_const (x := z.2) z.1).prodMk (hasFDerivAt_id z.2))
  rw [hs.fderiv]
  simp

private theorem scalarSpatialHessian_eq_coordinate_open_local
    {d : ℕ} (u : TimeVelocity d → ℝ) (z : TimeVelocity d) (i j : Fin d)
    (hu : ContDiffAt ℝ 2 u z) :
    scalarSpatialHessian u z i j =
      coordinateIteratedFDeriv
        (Pi.single (velocityCoord j) 1 + Pi.single (velocityCoord i) 1) u z := by
  classical
  let q : TimeVelocity d → ℝ :=
    coordinateIteratedFDeriv (Pi.single (velocityCoord j) 1) u
  have hq : ContDiffAt ℝ 1 q z := by
    have hr : ContDiffAt ℝ 1
        (fun x ↦ (fderiv ℝ u x) (timeVelocityBasis (velocityCoord j))) z :=
      (hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
    apply hr.congr_of_eventuallyEq
    filter_upwards [hu.eventually (by simp)] with x hx
    have hadd := coordinateIteratedFDeriv_add_single_at
      (0 : TimeVelocityMultiIndex d) (velocityCoord j) u x
      (by simpa [TimeVelocityMultiIndex.order, TimeVelocityMultiIndex.timeOrder,
        TimeVelocityMultiIndex.velocity, VelocityMultiIndex.order] using hx.of_le (by norm_num))
    rw [show coordinateIteratedFDeriv (0 : TimeVelocityMultiIndex d) u = u by
      funext y; exact coordinateIteratedFDeriv_zero u y] at hadd
    simpa [q] using hadd
  have hgradient : (fun x : TimeVelocity d ↦ scalarSpatialGradient u x j) =ᶠ[nhds z] q := by
    filter_upwards [hu.eventually (by simp)] with x hx
    exact scalarSpatialGradient_eq_coordinate_open_local u x j (hx.of_le (by norm_num))
  have hgradientDiff : DifferentiableAt ℝ
      (fun x : TimeVelocity d ↦ scalarSpatialGradient u x j) z :=
    hgradient.differentiableAt_iff.mpr (hq.differentiableAt (by norm_num))
  have hslice : ContDiffAt ℝ 2 (fun y : PDE.Vec d ↦ u (z.1, y)) z.2 :=
    hu.comp z.2 (contDiffAt_const.prodMk contDiffAt_id)
  have hgradientApply :
      (fderiv ℝ (fun y : PDE.Vec d ↦
          PDE.classicalGradient (fun w : PDE.Vec d ↦ u (z.1, w)) y j) z.2)
          (PDE.basisVec i) =
        (fderiv ℝ (fun y : PDE.Vec d ↦
          PDE.classicalGradient (fun w : PDE.Vec d ↦ u (z.1, w)) y) z.2
          (PDE.basisVec i)) j := by
    have hgrad : DifferentiableAt ℝ
        (fun y ↦ PDE.classicalGradient (fun w : PDE.Vec d ↦ u (z.1, w)) y) z.2 := by
      apply differentiableAt_pi.2
      intro k
      have hd : DifferentiableAt ℝ
          (fderiv ℝ (fun w : PDE.Vec d ↦ u (z.1, w))) z.2 :=
        (hslice.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
      exact hd.clm_apply (differentiableAt_const (c := PDE.basisVec k))
    rw [fderiv_pi (fun k ↦ (differentiableAt_pi.mp hgrad) k)]
    simp
  have hcomp :
      fderiv ℝ (fun y : PDE.Vec d ↦ scalarSpatialGradient u (z.1, y) j) z.2 =
        (fderiv ℝ (fun x : TimeVelocity d ↦ scalarSpatialGradient u x j) z).comp
          (ContinuousLinearMap.inr ℝ ℝ (PDE.Vec d)) := by
    change fderiv ℝ ((fun x : TimeVelocity d ↦ scalarSpatialGradient u x j) ∘
      fun y : PDE.Vec d ↦ (z.1, y)) z.2 = _
    rw [fderiv_comp z.2 hgradientDiff
      ((differentiableAt_const (c := z.1)).prodMk differentiableAt_id)]
    congr 1
    exact ((hasFDerivAt_const (x := z.2) z.1).prodMk (hasFDerivAt_id z.2)).fderiv
  have hsucc := coordinateIteratedFDeriv_add_single_at
    (Pi.single (velocityCoord j) 1) (velocityCoord i) u z (by
      convert hu using 1 <;>
        norm_num [TimeVelocityMultiIndex.order, TimeVelocityMultiIndex.timeOrder,
        TimeVelocityMultiIndex.velocity, VelocityMultiIndex.order,
        TimeVelocityMultiIndex.velocity, velocityCoord, timeCoord, Pi.single_apply])
  change (fderiv ℝ (fun y : PDE.Vec d ↦
      PDE.classicalGradient (fun w : PDE.Vec d ↦ u (z.1, w)) y) z.2
      (PDE.basisVec i)) j = _
  rw [← hgradientApply]
  change (fderiv ℝ (fun y : PDE.Vec d ↦
    scalarSpatialGradient u (z.1, y) j) z.2) (PDE.basisVec i) = _
  rw [hcomp, hgradient.fderiv_eq]
  simpa [q] using hsucc.symm

/-- Two ambient `C²` germs that agree near a point have the same scalar time,
gradient, and ordered Hessian jets at that point. -/
theorem scalarJet_eqAt_of_eventuallyEq
    {d : ℕ} {f g : TimeVelocity d → ℝ} {z : TimeVelocity d}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z)
    (hfg : f =ᶠ[nhds z] g) :
    scalarTimeDerivative f z = scalarTimeDerivative g z ∧
    scalarSpatialGradient f z = scalarSpatialGradient g z ∧
    scalarSpatialHessian f z = scalarSpatialHessian g z := by
  constructor
  · rw [scalarTimeDerivative_eq_coordinate_open_local f z (hf.of_le (by norm_num)),
      scalarTimeDerivative_eq_coordinate_open_local g z (hg.of_le (by norm_num))]
    exact coordinateIteratedFDeriv_congr_of_eventuallyEq
      (Pi.single (timeCoord d) 1) hfg
  constructor
  · funext j
    rw [scalarSpatialGradient_eq_coordinate_open_local f z j (hf.of_le (by norm_num)),
      scalarSpatialGradient_eq_coordinate_open_local g z j (hg.of_le (by norm_num))]
    exact coordinateIteratedFDeriv_congr_of_eventuallyEq
      (Pi.single (velocityCoord j) 1) hfg
  · funext i j
    rw [scalarSpatialHessian_eq_coordinate_open_local f z i j hf,
      scalarSpatialHessian_eq_coordinate_open_local g z i j hg]
    exact coordinateIteratedFDeriv_congr_of_eventuallyEq
      (Pi.single (velocityCoord j) 1 + Pi.single (velocityCoord i) 1) hfg

end
end HypoellipticAleksandrov.Parabolic

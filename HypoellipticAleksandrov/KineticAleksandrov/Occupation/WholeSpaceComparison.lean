module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.WholeSpaceCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.WholeSpaceQuadratic
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.WholeSpaceCoefficient
public import HypoellipticAleksandrov.Parabolic.ScalarMaximum
public import HypoellipticAleksandrov.Parabolic.ScalarDirichletData

/-! # Maximum-principle comparison with the occupation quadratic -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic SectionTwo Set
open scoped MatrixOrder Matrix.Norms.Elementwise

/-- The quadratic is nonnegative before the terminal time. -/
theorem occupationQuadratic_nonneg {d : ℕ} {Lam : ℝ} (hLam : 0 ≤ Lam)
    (vStar : PDE.Vec d) {z : TimeVelocity d} (hz : z.1 ≤ 1) :
    0 ≤ occupationQuadratic Lam vStar z := by
  unfold occupationQuadratic
  exact add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (mul_nonneg (by positivity) (sub_nonneg.mpr hz))

/-- A smooth quadratic majorant controls a classical comparison defect. -/
theorem wholeSpace_quadratic_comparison {d : ℕ} {lam Lam α R H : ℝ}
    {B : CoefficientField d} (hB : IsSectionTwoCoefficient lam Lam B)
    (hα : α < 1) (vStar : PDE.Vec d)
    (hΩbounded : Bornology.IsBounded (PDE.euclideanBall vStar R))
    (hH : 0 ≤ H)
    (W V : TimeVelocity d → ℝ) (F : TimeVelocity d → ℝ)
    (hWcont : ContinuousOn W
      (scalarParabolicClosedCylinder α 1 (PDE.euclideanBall vStar R)))
    (hWreg : IsScalarC12On W
      (scalarParabolicOpenCylinder α 1 (PDE.euclideanBall vStar R)))
    (hWeq : ∀ z ∈ scalarParabolicOpenCylinder α 1 (PDE.euclideanBall vStar R),
      scalarParabolicOperator B (fun _ _ => 0) W z = -F z)
    (hV : IsClassicalBackwardDirichletSolution α 1 (PDE.euclideanBall vStar R) B
      (fun _ _ => 0) (fun _ _ => 0) (fun r v => -F (r, v))
      (fun _ => 0) (fun _ => 0) V)
    (hterminal : ∀ z ∈ scalarParabolicTerminalFace 1 (PDE.euclideanBall vStar R),
      W z = 0)
    (hlateral : ∀ z ∈ scalarParabolicLateralFace α 1 (PDE.euclideanBall vStar R),
      W z ≤ H * occupationQuadratic Lam vStar z / R ^ 2) :
    ∀ z ∈ scalarParabolicClosedCylinder α 1 (PDE.euclideanBall vStar R),
      W z ≤ V z + H * occupationQuadratic Lam vStar z / R ^ 2 := by
  let c := H / R ^ 2
  let Q := occupationQuadratic Lam vStar
  let ψ := fun z => c * Q z + 0
  have hc : 0 ≤ c := div_nonneg hH (sq_nonneg R)
  have hQreg : IsScalarC12On Q
      (scalarParabolicOpenCylinder α 1 (PDE.euclideanBall vStar R)) :=
    isScalarC12On_of_contDiff_two
      ((contDiff_occupationQuadratic Lam vStar).of_le (by simp)) _
  have hψreg := hQreg.const_mul_add_const c 0
  have hdiff := isScalarC12On_sub hWreg hV.2.1
  let u := fun z => W z - V z - ψ z
  have hureg : IsScalarC12On u
      (scalarParabolicOpenCylinder α 1 (PDE.euclideanBall vStar R)) :=
    isScalarC12On_sub hdiff hψreg
  have huc : ContinuousOn u
      (scalarParabolicClosedCylinder α 1 (PDE.euclideanBall vStar R)) :=
    (hWcont.sub hV.1).sub
      (((contDiff_occupationQuadratic Lam vStar).continuous.const_mul c).add
        continuous_const).continuousOn
  have hsub : ∀ z ∈ scalarParabolicOpenCylinder α 1 (PDE.euclideanBall vStar R),
      0 ≤ scalarParabolicOperator B (fun _ _ => 0) u z := by
    intro z hz
    have huop := scalarParabolicZeroOrderOperator_sub B (fun _ _ => 0)
      (fun _ _ => 0) hdiff hψreg hz
    have hdop := scalarParabolicZeroOrderOperator_sub B (fun _ _ => 0)
      (fun _ _ => 0) hWreg hV.2.1 hz
    have hψop := scalarParabolicZeroOrderOperator_const_mul_add_const B
      (fun _ _ => 0) (fun _ _ => 0) c 0 Q z
    have hVeq := hV.2.2.1 z hz
    have hQop := scalarParabolicOperator_occupationQuadratic_le B Lam vStar z
      (hB.2.2.2.2.2 z.1 z.2)
    simp only [scalarParabolicZeroOrderOperator, zero_mul, add_zero] at huop hdop hψop hVeq
    change 0 ≤ scalarParabolicOperator B (fun _ _ => 0) u z
    simp only [u, ψ, add_zero]
    rw [huop, hdop, hψop, hWeq z hz, hVeq]
    simpa only [Prod.mk.eta, sub_self] using
      sub_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hc hQop)
  have ht : ∀ z ∈ scalarParabolicTerminalFace 1 (PDE.euclideanBall vStar R),
      u z ≤ 0 := by
    intro z hz
    obtain ⟨htime, hv⟩ := mem_scalarParabolicTerminalFace_iff.mp hz
    have hVz : V z = 0 := by
      have he : z = (1, z.2) := Prod.ext htime rfl
      rw [he]
      exact hV.2.2.2.1 z.2 hv
    have hQ0 := occupationQuadratic_nonneg (hB.1.le.trans hB.2.1) vStar
      (show z.1 ≤ 1 from htime.le)
    dsimp [u, ψ]
    rw [hterminal z hz, hVz]
    nlinarith [mul_nonneg hc hQ0]
  have hl : ∀ z ∈ scalarParabolicLateralFace α 1 (PDE.euclideanBall vStar R),
      u z ≤ 0 := by
    intro z hz
    have hw := hlateral z hz
    have hv := hV.2.2.2.2 z hz
    dsimp [u, ψ, c, Q]
    rw [hv]
    simpa only [sub_zero, add_zero, div_mul_eq_mul_div, sub_nonpos] using hw
  have hmax := scalar_le_on_closedCylinder_of_terminal_lateral_le
    (PDE.isOpen_euclideanBall vStar R) hΩbounded hα B (fun _ _ => 0)
    (sectionTwoCoefficient_smooth hB).continuous continuous_const
    (sectionTwoCoefficient_posSemidef hB) u huc hureg hsub ht hl
  intro z hz
  have hu := hmax z hz
  dsimp [u, ψ, c, Q] at hu
  rw [div_mul_eq_mul_div] at hu
  linarith

end HypoellipticAleksandrov.KineticAleksandrov.Occupation

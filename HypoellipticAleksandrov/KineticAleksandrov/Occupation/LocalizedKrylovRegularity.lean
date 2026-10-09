module

public import HypoellipticAleksandrov.KineticAleksandrov.ClassicalInputs
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.LocalizedKrylovGeometry
public import HypoellipticAleksandrov.Parabolic.ScalarDirichletComparison
public import HypoellipticAleksandrov.Parabolic.AffineScalarCalculus

/-!
# Closure regularity and nonnegativity of the localized source solution

For the classical solution `V` of `∂_r V + B : D_v² V = -F` on `(α, 1) × B_R(v_*)`
with zero terminal and lateral data (proof of the companion paper, Proposition 4.2), the weak
maximum principle proves `V ≥ 0`. Jet congruence on open sets is also recorded here.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter
open scoped Topology MatrixOrder Matrix.Norms.Elementwise

variable {d : ℕ}

section Congruence

variable {V W : TimeVelocity d → ℝ} {D : Set (TimeVelocity d)}

private theorem eventually_slice_time (hD : IsOpen D) {z : TimeVelocity d} (hz : z ∈ D) :
    ∀ᶠ r in 𝓝 z.1, (r, z.2) ∈ D := by
  have hcont : Continuous (fun r : ℝ => (r, z.2)) := by fun_prop
  exact hcont.continuousAt.preimage_mem_nhds (hD.mem_nhds hz)

private theorem eventually_slice_space (hD : IsOpen D) {z : TimeVelocity d} (hz : z ∈ D) :
    ∀ᶠ y in 𝓝 z.2, (z.1, y) ∈ D := by
  have hcont : Continuous (fun y : PDE.Vec d => (z.1, y)) := by fun_prop
  exact hcont.continuousAt.preimage_mem_nhds (hD.mem_nhds hz)

/-- Two functions agreeing on an open set have the same `C^{1,2}` jets there. -/
theorem scalarJet_eqOn_of_eqOn_open (hD : IsOpen D) (hVW : EqOn V W D) :
    EqOn (scalarTimeDerivative V) (scalarTimeDerivative W) D ∧
    EqOn (scalarSpatialGradient V) (scalarSpatialGradient W) D ∧
    EqOn (scalarSpatialHessian V) (scalarSpatialHessian W) D := by
  have hgrad : EqOn (scalarSpatialGradient V) (scalarSpatialGradient W) D := by
    intro z hz
    have hs : (fun y => V (z.1, y)) =ᶠ[𝓝 z.2] (fun y => W (z.1, y)) := by
      filter_upwards [eventually_slice_space hD hz] with y hy using hVW hy
    unfold scalarSpatialGradient PDE.classicalGradient
    ext i
    rw [hs.fderiv_eq (𝕜 := ℝ)]
  refine ⟨?_, hgrad, ?_⟩
  · intro z hz
    have ht : (fun r => V (r, z.2)) =ᶠ[𝓝 z.1] (fun r => W (r, z.2)) := by
      filter_upwards [eventually_slice_time hD hz] with r hr using hVW hr
    exact ht.deriv_eq
  · intro z hz
    have hg : (fun y => PDE.classicalGradient (fun w => V (z.1, w)) y) =ᶠ[𝓝 z.2]
        (fun y => PDE.classicalGradient (fun w => W (z.1, w)) y) := by
      filter_upwards [eventually_slice_space hD hz] with y hy using hgrad hy
    unfold scalarSpatialHessian
    ext i j
    rw [hg.fderiv_eq (𝕜 := ℝ)]

/-- `C^{1,2}` regularity on an open set is invariant under equality on that set. -/
theorem isScalarC12On_congr_open (hD : IsOpen D) (hW : IsScalarC12On W D)
    (hVW : EqOn V W D) : IsScalarC12On V D := by
  obtain ⟨ht, hg, hh⟩ := scalarJet_eqOn_of_eqOn_open hD hVW
  refine ⟨hW.continuousOn.congr hVW, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have h : (fun r => V (r, z.2)) =ᶠ[𝓝 z.1] (fun r => W (r, z.2)) := by
      filter_upwards [eventually_slice_time hD hz] with r hr using hVW hr
    exact (hW.timeSlice_differentiableAt hz).congr_of_eventuallyEq h
  · intro z hz
    have h : (fun y => V (z.1, y)) =ᶠ[𝓝 z.2] (fun y => W (z.1, y)) := by
      filter_upwards [eventually_slice_space hD hz] with y hy using hVW hy
    exact (hW.spatialSlice_contDiffAt hz).congr_of_eventuallyEq h
  · exact hW.continuousOn_scalarTimeDerivative.congr ht
  · exact hW.continuousOn_scalarSpatialGradient.congr hg
  · exact hW.continuousOn_scalarSpatialHessian.congr hh

/-- Closure regularity transfers between functions agreeing on the closed carrier. -/
theorem isScalarC12UpTo_congr {Q K : Set (TimeVelocity d)} (hQ : IsOpen Q) (hQK : Q ⊆ K)
    (hW : IsScalarC12UpTo W Q K) (hVW : EqOn V W K) (hV : ContinuousOn V K) :
    IsScalarC12UpTo V Q K := by
  obtain ⟨hC, -, dt, dv, dvv, hdt, hdv, hdvv, e1, e2, e3⟩ := hW
  have hVWQ : EqOn V W Q := fun z hz => hVW (hQK hz)
  obtain ⟨ht, hg, hh⟩ := scalarJet_eqOn_of_eqOn_open hQ hVWQ
  refine ⟨isScalarC12On_congr_open hQ hC hVWQ, hV, dt, dv, dvv, hdt, hdv, hdvv, ?_, ?_, ?_⟩
  · intro z hz
    rw [e1 hz, ht hz]
  · intro z hz
    rw [e2 hz, hg hz]
  · intro z hz
    rw [e3 hz, hh hz]

end Congruence

section Solution

variable {lam Lam : ℝ} {B : CoefficientField d} {F : TimeVelocity d → ℝ}
  {α : ℝ} {vStar : PDE.Vec d} {R : ℝ}

/-- Positive lower Loewner bound makes the coefficient positive semidefinite. -/
theorem posSemidef_of_lower_loewner (hlam : 0 < lam)
    (hlow : ∀ r v, lam • (1 : PDE.Mat d) ≤ B r v) (r : ℝ) (v : PDE.Vec d) :
    (B r v).PosSemidef := by
  have h0 : (0 : PDE.Mat d) ≤ lam • (1 : PDE.Mat d) := by
    rw [Matrix.nonneg_iff_posSemidef]
    exact Matrix.PosSemidef.one.smul hlam.le
  exact Matrix.nonneg_iff_posSemidef.mp (h0.trans (hlow r v))

/-- Nonnegativity of the localized source solution (weak maximum principle). -/
theorem classical_solution_nonneg (hlam : 0 < lam) (hF0 : ∀ z, 0 ≤ F z)
    (hα1 : α < 1) (hR : 0 < R)
    (hsmooth : IsSmoothCoefficient B) (hlow : ∀ r v, lam • (1 : PDE.Mat d) ≤ B r v)
    {V : TimeVelocity d → ℝ}
    (hV : IsClassicalBackwardDirichletSolution α 1 (PDE.euclideanBall vStar R) B
      (fun _ _ => 0) (fun _ _ => 0) (fun r v => -F (r, v)) (fun _ => 0) (fun _ => 0) V) :
    ∀ z ∈ scalarParabolicClosedCylinder α 1 (PDE.euclideanBall vStar R), 0 ≤ V z := by
  obtain ⟨hcont, hC12, hpde, hterm, hlat⟩ := hV
  have hw := scalar_le_zero_on_closedCylinder_of_zeroOrderOperator_nonneg
    (PDE.isOpen_euclideanBall vStar R) (isBounded_euclideanBall vStar hR) hα1 B
    (fun _ _ => 0) (fun _ _ => 0) hsmooth.continuous continuous_const
    (posSemidef_of_lower_loewner hlam hlow) (fun _ _ => le_rfl)
    (fun z => -1 * V z + 0)
    ((continuousOn_const.mul hcont).add continuousOn_const)
    (IsScalarC12On.const_mul_add_const hC12 (-1) 0)
    (by
      intro z hz
      rw [scalarParabolicZeroOrderOperator_const_mul_add_const, hpde z hz]
      simpa using hF0 z)
    (by
      rintro ⟨r, y⟩ hz
      rw [mem_scalarParabolicTerminalFace_iff] at hz
      obtain ⟨rfl, hy⟩ := hz
      have h0 : V (1, y) = 0 := hterm y hy
      show -1 * V (1, y) + 0 ≤ 0
      rw [h0]
      norm_num)
    (by
      intro z hz
      have h0 : V z = 0 := hlat z hz
      show -1 * V z + 0 ≤ 0
      rw [h0]
      norm_num)
  intro z hz
  have := hw z hz
  linarith

end Solution

end HypoellipticAleksandrov.KineticAleksandrov.Occupation

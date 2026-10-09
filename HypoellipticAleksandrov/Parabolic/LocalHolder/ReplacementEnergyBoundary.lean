module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementEnergyBall
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonTracesBall
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.LocalizedKrylovRegularity

/-! # Classical signed corrections continuous up to the ball boundary

A finite earlier time collar supplies continuity at the lower face. The two proved
envelopes supply zero terminal and lateral traces, without compact-source restrictions.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter MeasureTheory Set Dirichlet KineticAleksandrov
open scoped ENNReal MatrixOrder Matrix.Norms.Elementwise

/-- Every smooth signed source has a continuous zero-boundary classical correction on a ball. -/
theorem exists_signed_source_ball_correction {d : ℕ} (hd : 0 < d)
    (v₀ : PDE.Vec d) (r : ℝ) (hr : 0 < r) (a T : ℝ) (haT : a < T)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : CoefficientField d) (hA : IsSmoothCoefficient A)
    (hlo : HasLowerEllipticity lam A) (hhi : HasUpperEllipticity Lam A)
    (F : TimeVelocity d → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ∃ W : TimeVelocity d → ℝ,
      IsClassicalBackwardDirichletSolution a T (PDE.euclideanBall v₀ r) A
        (fun _ _ => 0) (fun _ _ => 0) (fun t y => F (t, y))
        (fun _ => 0) (fun _ => 0) W := by
  classical
  let Ω := PDE.euclideanBall v₀ r
  have hΩ : IsOpen Ω := PDE.isOpen_euclideanBall v₀ r
  have hΩb : Bornology.IsBounded Ω := Occupation.isBounded_euclideanBall v₀ hr
  have hleft : a - 1 < a := by linarith
  have hleftT : a - 1 < T := hleft.trans haT
  have hK := isCompact_scalarParabolicClosedCylinder (a - 1) T hΩb
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF.continuous.continuousOn
  let M := max C 0
  have hM : 0 ≤ M := le_max_right _ _
  have hFM : ∀ z ∈ scalarParabolicClosedCylinder (a - 1) T Ω, |F z| ≤ M := by
    intro z hz
    rw [← Real.norm_eq_abs]
    exact (hC z hz).trans (le_max_left _ _)
  obtain ⟨w, hw, he, ht, hs⟩ := exists_signed_source_ballInterior_with_bounds hd
    v₀ r hr (a - 1) T hleftT lam Lam hlam hLam A hA hlo hhi F hF M hM hFM
  let U := scalarParabolicOpenCylinder (a - 1) T Ω
  let D := scalarParabolicOpenCylinder a T Ω
  let W := sourceInteriorZeroExtension (a - 1) T Ω w
  have hsub : D ⊆ U := prod_mono (Ioo_subset_Ioo hleft.le le_rfl) (Subset.refl _)
  have hWD : EqOn W w D := by
    intro z hz
    exact piecewise_eq_of_mem U w (fun _ => 0) (hsub hz)
  have hwD : IsScalarC12On w D :=
    ⟨hw.continuousOn.mono hsub,
      fun z hz => hw.timeSlice_differentiableAt (hsub hz),
      fun z hz => hw.spatialSlice_contDiffAt (hsub hz),
      hw.continuousOn_scalarTimeDerivative.mono hsub,
      hw.continuousOn_scalarSpatialGradient.mono hsub,
      hw.continuousOn_scalarSpatialHessian.mono hsub⟩
  have hD : IsOpen D := isOpen_Ioo.prod hΩ
  have hWc := continuousOn_source_zeroExtension_closed_ball (a - 1) a T hleft
    v₀ r lam M hM w hw.continuousOn ht hs
  have hWr := Occupation.isScalarC12On_congr_open hD hwD hWD
  obtain ⟨hdt, _, hdd⟩ := Occupation.scalarJet_eqOn_of_eqOn_open hD hWD
  refine ⟨W, hWc, hWr, ?_, ?_, ?_⟩
  · intro z hz
    simp only [scalarParabolicZeroOrderOperator_apply, Pi.zero_apply, PDE.vecDot,
      zero_mul, Finset.sum_const_zero, add_zero, hdt hz, hdd hz]
    exact he z (hsub hz)
  · intro y _
    exact piecewise_eq_of_notMem U w (fun _ => 0)
      (fun h => (lt_irrefl T) h.1.2)
  · intro z hz
    have hzo : z.2 ∉ Ω := by
      have hf : z.2 ∈ frontier Ω := hz.2
      rw [hΩ.frontier_eq] at hf
      exact hf.2
    exact piecewise_eq_of_notMem U w (fun _ => 0) (fun h => hzo h.2)

end HypoellipticAleksandrov.Parabolic.LocalHolder

module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApproxUniform
public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApproxClosedLimitRegularity

/-! # Homogeneous backward replacement for continuous closed-ball data

Smooth boundary approximation converges uniformly with the exact traces. The internally
proved local energy and compactness argument establishes the limit's classical equation.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter MeasureTheory Set
open scoped Topology Matrix.Norms.Elementwise

/-- Arbitrary continuous closed-ball data have an actual classical homogeneous replacement. -/
theorem exists_continuous_backward_homogeneous_replacement {d : ℕ} (hd : 0 < d)
    (v₀ : PDE.Vec d) (r : ℝ) (hr : 0 < r) (a T : ℝ) (haT : a < T)
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (A : CoefficientField d) (hA : IsSmoothCoefficient A)
    (hlo : HasLowerEllipticity lam A) (hhi : HasUpperEllipticity Lam A)
    (w : TimeVelocity d → ℝ)
    (hw : ContinuousOn w (scalarParabolicClosedCylinder a T (PDE.euclideanBall v₀ r))) :
    ∃ v : TimeVelocity d → ℝ,
      IsClassicalBackwardDirichletSolution a T (PDE.euclideanBall v₀ r) A
        (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun y => w (T, y)) w v := by
  classical
  let Ω := PDE.euclideanBall v₀ r
  let K := scalarParabolicClosedCylinder a T Ω
  obtain ⟨f, u, U, V, hf, hfb, hu, hUeq, hlim, htrace⟩ :=
    exists_uniform_smooth_boundary_replacements hd v₀ r hr a T haT
      lam Lam hlam hlamLam A hA hlo hhi w hw
  have hEq (n : ℕ) (z : TimeVelocity d) (hz : z ∈ Ioo a T ×ˢ Ω) :
      scalarTimeDerivative (u n) z +
        matrixContraction (coefficientAt A z) (scalarSpatialHessian (u n) z) = 0 := by
    have he := (hu n).2.2.1 z hz
    simpa only [scalarParabolicZeroOrderOperator_apply, coefficientAt, PDE.vecDot, Pi.zero_apply,
      zero_mul, Finset.sum_const_zero, add_zero] using he
  obtain ⟨hv12, hveq⟩ := homogeneous_continuousMap_limit_is_classical a T Ω
    (PDE.isOpen_euclideanBall v₀ r)
    (KineticAleksandrov.Occupation.isBounded_euclideanBall v₀ hr).isCompact_closure
    A hA lam Lam hlam hlamLam hlo hhi u (fun n => (hu n).2.1) hEq U V hUeq hlim
  refine ⟨continuousMapZeroExtension V,
    continuousOn_continuousMapZeroExtension V, hv12, ?_, ?_, ?_⟩
  · intro z hz
    simpa only [scalarParabolicZeroOrderOperator_apply, coefficientAt, PDE.vecDot, Pi.zero_apply,
      zero_mul, Finset.sum_const_zero, add_zero] using hveq z hz
  · intro y hy
    have hzK : (T, y) ∈ K := ⟨⟨haT.le, le_rfl⟩, hy⟩
    change continuousMapZeroExtension V (T, y) = w (T, y)
    rw [continuousMapZeroExtension, dite_eq_left hzK]
    exact htrace ⟨(T, y), hzK⟩ (Or.inl ⟨mem_singleton T, hy⟩)
  · intro z hz
    have hzK : z ∈ K := ⟨hz.1, frontier_subset_closure hz.2⟩
    rw [continuousMapZeroExtension, dite_eq_left hzK]
    exact htrace ⟨z, hzK⟩ (Or.inr hz)

end HypoellipticAleksandrov.Parabolic.LocalHolder

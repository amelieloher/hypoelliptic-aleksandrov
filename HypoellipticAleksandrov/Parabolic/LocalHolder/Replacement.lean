module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementSource

/-! # Homogeneous replacement for compact smooth residuals

Subtracting the signed zero-boundary correction preserves the supplied boundary data.
The general forward hLE-only replacement requires an additional approximation argument.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Set KineticAleksandrov
open scoped MatrixOrder Matrix.Norms.Elementwise

/-- Compact smooth backward residuals have a homogeneous replacement with the same boundary data. -/
theorem exists_backward_compact_source_homogeneous_replacement
    {d : ℕ} (hd : 0 < d)
    (α : ℝ) (hα : 0 ≤ α) (hα1 : α < 1)
    (v₀ : PDE.Vec d) (R : ℝ) (hR : 0 < R)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : CoefficientField d) (hs : ∀ t v, (B t v).IsSymm)
    (hB : IsSmoothCoefficient B)
    (hlo : ∀ t v, lam • (1 : PDE.Mat d) ≤ B t v)
    (hhi : ∀ t v, B t v ≤ Lam • (1 : PDE.Mat d))
    (F : TimeVelocity d → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hc : HasCompactSupport F) (hU : tsupport F ⊆ Ioo (0 : ℝ) 1 ×ˢ univ)
    (M : ℝ) (hM : 0 ≤ M) (hFb : ∀ z, |F z| ≤ M)
    (w : TimeVelocity d → ℝ)
    (hwc : ContinuousOn w (scalarParabolicClosedCylinder α 1 (PDE.euclideanBall v₀ R)))
    (hws : IsScalarC12On w (scalarParabolicOpenCylinder α 1 (PDE.euclideanBall v₀ R)))
    (hwe : ∀ z ∈ scalarParabolicOpenCylinder α 1 (PDE.euclideanBall v₀ R),
      scalarParabolicZeroOrderOperator B (fun _ _ => 0) (fun _ _ => 0) w z = -F z) :
    ∃ v : TimeVelocity d → ℝ,
      IsClassicalBackwardDirichletSolution α 1 (PDE.euclideanBall v₀ R) B
        (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
        (fun y => w (1, y)) w v ∧
      ∀ z ∈ scalarParabolicClosedCylinder α 1 (PDE.euclideanBall v₀ R),
        |w z - v z| ≤ M * (1 - z.1) := by
  obtain ⟨u, hu, hub⟩ := exists_signed_smooth_compact_source_correction_with_bound_direct
    hd α hα hα1 v₀ R hR lam Lam hlam hLam B hs hB hlo hhi F hF hc hU M hM hFb
  refine ⟨fun z => w z - u z, ⟨hwc.sub hu.1, isScalarC12On_sub hws hu.2.1,
    ?_, ?_, ?_⟩, ?_⟩
  · intro z hz
    rw [scalarParabolicZeroOrderOperator_sub B (fun _ _ => 0) (fun _ _ => 0)
      hws hu.2.1 hz, hwe z hz, hu.2.2.1 z hz]
    exact sub_self _
  · intro y hy
    change w (1, y) - u (1, y) = w (1, y)
    rw [hu.2.2.2.1 y hy, sub_zero]
  · intro z hz
    change w z - u z = w z
    rw [hu.2.2.2.2 z hz, sub_zero]
  · intro z hz
    change |w z - (w z - u z)| ≤ _
    rw [sub_sub_cancel]
    exact hub z hz

end HypoellipticAleksandrov.Parabolic.LocalHolder

module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementEnergyBoundary
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparison
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.LocalizedKrylovRegularity

/-! # Source corrections from the internal ball solver -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Set KineticAleksandrov
open scoped MatrixOrder Matrix.Norms.Elementwise

/-- The internal ball solver yields signed compact smooth corrections. -/
theorem exists_signed_smooth_compact_source_correction_direct
    {d : ℕ} (hd : 0 < d)
    (α : ℝ) (_hα : 0 ≤ α) (hα1 : α < 1)
    (v₀ : PDE.Vec d) (R : ℝ) (hR : 0 < R)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : CoefficientField d) (_hs : ∀ t v, (B t v).IsSymm)
    (hB : IsSmoothCoefficient B)
    (hlo : ∀ t v, lam • (1 : PDE.Mat d) ≤ B t v)
    (hhi : ∀ t v, B t v ≤ Lam • (1 : PDE.Mat d))
    (F : TimeVelocity d → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (_hc : HasCompactSupport F) (_hU : tsupport F ⊆ Ioo (0 : ℝ) 1 ×ˢ univ) :
    ∃ u : TimeVelocity d → ℝ,
      IsClassicalBackwardDirichletSolution α 1 (PDE.euclideanBall v₀ R) B
        (fun _ _ => 0) (fun _ _ => 0) (fun t v => -F (t, v))
        (fun _ => 0) (fun _ => 0) u := by
  exact exists_signed_source_ball_correction hd v₀ R hR α 1 hα1 lam Lam hlam hLam
    B hB hlo hhi (fun z => -F z) hF.neg

/-- Signed compact smooth corrections satisfy the source-independent time barrier. -/
theorem exists_signed_smooth_compact_source_correction_with_bound_direct
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
    (M : ℝ) (hM : 0 ≤ M) (hFb : ∀ z, |F z| ≤ M) :
    ∃ u : TimeVelocity d → ℝ,
      IsClassicalBackwardDirichletSolution α 1 (PDE.euclideanBall v₀ R) B
        (fun _ _ => 0) (fun _ _ => 0) (fun t v => -F (t, v))
        (fun _ => 0) (fun _ => 0) u ∧
      ∀ z ∈ scalarParabolicClosedCylinder α 1 (PDE.euclideanBall v₀ R),
        |u z| ≤ M * (1 - z.1) := by
  obtain ⟨u, hu⟩ := exists_signed_smooth_compact_source_correction_direct hd α hα hα1
    v₀ R hR lam Lam hlam hLam B hs hB hlo hhi F hF hc hU
  refine ⟨u, hu, ?_⟩
  apply abs_zeroBoundary_solution_le_time (PDE.isOpen_euclideanBall v₀ R)
    (Occupation.isBounded_euclideanBall v₀ hR) hα1 B hB.continuous
    (Occupation.posSemidef_of_lower_loewner hlam hlo) (fun t v => -F (t, v)) M hM
    (fun z _ => by simpa only [abs_neg] using hFb z) u hu

end HypoellipticAleksandrov.Parabolic.LocalHolder

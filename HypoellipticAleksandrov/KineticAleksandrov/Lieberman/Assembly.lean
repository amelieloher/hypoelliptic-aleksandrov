module

public import HypoellipticAleksandrov.KineticAleksandrov.Lieberman.TerminalLift
public import HypoellipticAleksandrov.KineticAleksandrov.Lieberman.DimensionZero
public import HypoellipticAleksandrov.KineticAleksandrov.Lieberman.SourceEllipsoidBoundary
public import HypoellipticAleksandrov.Parabolic.ScalarDirichletComparison

/-! # Ellipsoid Dirichlet solvability assembled from the proved source correction -/

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Lieberman Set
open scoped MatrixOrder Matrix.Norms.Elementwise

/-- Smooth ellipsoidal terminal Dirichlet existence and closed-cylinder uniqueness. -/
theorem ellipsoidDirichlet_aux
    {N : ℕ} {r₀ r₁ : ℝ} {Q : PDE.Mat N}
    (hQ : Q.PosDef)
    (hr : r₀ < r₁)
    (lam Lam : ℝ)
    (hlam : 0 < lam)
    (hlamLam : lam ≤ Lam)
    (a : CoefficientField N)
    (b : ℝ → PDE.Vec N → PDE.Vec N)
    (haSymm : ∀ t v, (a t v).IsSymm)
    (haSmooth : IsSmoothCoefficient a)
    (haLower : ∀ t v, lam • (1 : PDE.Mat N) ≤ a t v)
    (haUpper : ∀ t v, a t v ≤ Lam • (1 : PDE.Mat N))
    (hbSmooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : TimeVelocity N => b z.1 z.2))
    (φ : PDE.Vec N → ℝ)
    (hφSmooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφCompact : HasCompactSupport φ)
    (hφSupport : tsupport φ ⊆ openEllipsoid Q) :
    ∃ u : TimeVelocity N → ℝ,
      IsClassicalBackwardDirichletSolution
        r₀ r₁ (openEllipsoid Q) a b
        (fun _ _ => 0) (fun _ _ => 0) φ (fun _ => 0) u ∧
      ∀ v : TimeVelocity N → ℝ,
        IsClassicalBackwardDirichletSolution
          r₀ r₁ (openEllipsoid Q) a b
          (fun _ _ => 0) (fun _ _ => 0) φ (fun _ => 0) v →
          Set.EqOn v u
            (scalarParabolicClosedCylinder r₀ r₁ (openEllipsoid Q)) := by
  have _hcompact := hφCompact
  have hΩ := isOpen_openEllipsoid Q
  have hΩb := (openEllipsoid_geometry hQ).1
  have hlo : HasLowerEllipticity lam a := haLower
  have hhi : HasUpperEllipticity Lam a := haUpper
  have hex : ∃ u : TimeVelocity N → ℝ,
      IsClassicalBackwardDirichletSolution r₀ r₁ (openEllipsoid Q) a b
        (fun _ _ => 0) (fun _ _ => 0) φ (fun _ => 0) u := by
    cases N with
    | zero =>
      exact ⟨(fun z => φ z.2), dimension_zero_solution r₀ r₁ Q a b φ⟩
    | succ n =>
      let F : TimeVelocity (n + 1) → ℝ := fun z =>
        -scalarParabolicZeroOrderOperator a b (fun _ _ => 0) (fun p => φ p.2) z
      have hF := contDiff_terminal_lift_source a b φ haSmooth hbSmooth hφSmooth
      obtain ⟨W, hW⟩ := exists_signed_source_ellipsoid_correction (Nat.succ_pos n)
        hQ r₀ r₁ lam Lam hr hlam
        hlamLam a b haSymm haSmooth hlo hhi hbSmooth F hF
      exact ⟨(fun z => φ z.2 + W z),
        terminal_lift_assembly hΩ r₀ r₁ a b φ hφSmooth hφSupport W hW⟩
  obtain ⟨u, hu⟩ := hex
  refine ⟨u, hu, ?_⟩
  intro v hv
  exact eqOn_closedCylinder_of_isClassicalBackwardDirichletSolution hΩ hΩb hr
    a b (fun _ _ => 0) (fun _ _ => 0) φ (fun _ => 0) v u
    haSmooth.continuous hbSmooth.continuous
    (fun t y => (hlo.posDef hlam t y).posSemidef) (fun _ _ => le_rfl) hv hu


end HypoellipticAleksandrov.KineticAleksandrov

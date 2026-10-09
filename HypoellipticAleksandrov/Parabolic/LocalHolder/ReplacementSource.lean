module

public import HypoellipticAleksandrov.KineticAleksandrov.SourceProblem.SourceCorrection

public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApprox
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.ClassicalInputs
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparison
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.LocalizedKrylovRegularity

/-! # Signed smooth compact source corrections

The internal signed source solver gives the correction and its time-barrier bound.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Set
open KineticAleksandrov
open scoped MatrixOrder Matrix.Norms.Elementwise

/-- Subtracting supplied classical solutions subtracts their source and boundary data. -/
theorem isClassicalBackwardDirichletSolution_sub {n : ℕ}
    {a T : ℝ} {Ω : Set (PDE.Vec n)} {A : CoefficientField n}
    {b : ℝ → PDE.Vec n → PDE.Vec n} {c F G : ℝ → PDE.Vec n → ℝ}
    {φ χ : PDE.Vec n → ℝ} {h k u v : TimeVelocity n → ℝ}
    (hu : IsClassicalBackwardDirichletSolution a T Ω A b c F φ h u)
    (hv : IsClassicalBackwardDirichletSolution a T Ω A b c G χ k v) :
    IsClassicalBackwardDirichletSolution a T Ω A b c
      (fun t x => F t x - G t x) (fun x => φ x - χ x)
      (fun z => h z - k z) (fun z => u z - v z) := by
  refine ⟨hu.1.sub hv.1, isScalarC12On_sub hu.2.1 hv.2.1, ?_, ?_, ?_⟩
  · intro z hz
    rw [scalarParabolicZeroOrderOperator_sub A b c hu.2.1 hv.2.1 hz,
      hu.2.2.1 z hz, hv.2.2.1 z hz]
  · intro y hy
    change u (T, y) - v (T, y) = φ y - χ y
    rw [hu.2.2.2.1 y hy, hv.2.2.2.1 y hy]
  · intro z hz
    change u z - v z = h z - k z
    rw [hu.2.2.2.2 z hz, hv.2.2.2.2 z hz]

/-- The internal source solver yields signed compact smooth corrections. -/
theorem exists_signed_smooth_compact_source_correction
    {d : ℕ} (hd : 0 < d)
    (α : ℝ) (hα : 0 ≤ α) (hα1 : α < 1)
    (v₀ : PDE.Vec d) (R : ℝ) (hR : 0 < R)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : CoefficientField d) (hs : ∀ t v, (B t v).IsSymm)
    (hB : IsSmoothCoefficient B)
    (hlo : ∀ t v, lam • (1 : PDE.Mat d) ≤ B t v)
    (hhi : ∀ t v, B t v ≤ Lam • (1 : PDE.Mat d))
    (F : TimeVelocity d → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hc : HasCompactSupport F) (hU : tsupport F ⊆ Ioo (0 : ℝ) 1 ×ˢ univ) :
    ∃ u : TimeVelocity d → ℝ,
      IsClassicalBackwardDirichletSolution α 1 (PDE.euclideanBall v₀ R) B
        (fun _ _ => 0) (fun _ _ => 0) (fun t v => -F (t, v))
        (fun _ => 0) (fun _ => 0) u := by
  exact exists_signed_smooth_compact_source_correction_direct hd α hα hα1
    v₀ R hR lam Lam hlam hLam B hs hB hlo hhi F hF hc hU

/-- Signed compact smooth corrections satisfy the source-independent time barrier. -/
theorem exists_signed_smooth_compact_source_correction_with_bound
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
  obtain ⟨u, hu⟩ := exists_signed_smooth_compact_source_correction hd α hα hα1
    v₀ R hR lam Lam hlam hLam B hs hB hlo hhi F hF hc hU
  refine ⟨u, hu, ?_⟩
  apply abs_zeroBoundary_solution_le_time (PDE.isOpen_euclideanBall v₀ R)
    (Occupation.isBounded_euclideanBall v₀ hR) hα1 B hB.continuous
    (Occupation.posSemidef_of_lower_loewner hlam hlo) (fun t v => -F (t, v)) M hM
    (fun z _ => by simpa only [abs_neg] using hFb z) u hu

end HypoellipticAleksandrov.Parabolic.LocalHolder

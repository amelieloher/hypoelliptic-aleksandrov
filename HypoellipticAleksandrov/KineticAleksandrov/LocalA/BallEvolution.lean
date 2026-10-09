module

public import HypoellipticAleksandrov.KineticAleksandrov.ClassicalInputs
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.Geometry
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Realization
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Uniqueness
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.Assembly

/-! # Unique velocity-ball terminal evolution

The terminal evolution theorem supplies existence; uniqueness fixes both the
operator family and its master kernel. The existence and uniqueness statements are proved before
any choice-based boundary construction.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory SectionTwo Parabolic

/-- Operator family and kernel on the stationary Euclidean velocity ball. -/
abbrev LocalBallEvolution {d : ℕ} (v₀ : PDE.Vec d) (R : ℝ) :=
  TerminalOperatorFamily (PDE.euclideanBall v₀ R) (fun _ => 0) ×
    MovingFiberKernel (PDE.euclideanBall v₀ R) (fun _ => 0)

/-- Positive-radius Euclidean balls satisfy the source domain admissibility criterion. -/
theorem localBall_admissible {d : ℕ} (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R) :
    IsAdmissibleEvolutionDomain (PDE.euclideanBall v₀ R) :=
  Or.inr (Or.inl ⟨v₀, R, hR, rfl⟩)

/-- Ball terminal evolution is unique, relative only to the two analytic hypotheses. -/
theorem existsUnique_localBallEvolution
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R) :
    ∃! E : LocalBallEvolution v₀ R,
      RealizesTerminalEvolution (PDE.euclideanBall v₀ R) (fun _ => 0)
        (PDE.isOpen_euclideanBall v₀ R).measurableSet
        (zIndependentCoefficient B) (identityDrift d) E.1 E.2 := by
  have hΩ := localBall_admissible v₀ hR
  obtain ⟨hBs, hBsym, hBell⟩ := sectionTwoCoefficient_fullBounds lam Lam B hB
  have hb := identityDrift_bounds d
  obtain ⟨S, K, hc, -, -, -, -, hi, -, -, -, -, he, hcomp, -, -, -⟩ :=
    exists_terminalEvolution_of_classical hLE hH d hd lam Lam 1 1 hlam hLam
      one_pos le_rfl (PDE.euclideanBall v₀ R) (fun _ => 0)
      (zIndependentCoefficient B) (identityDrift d) hΩ (zeroCurve_piecewiseC1 d)
      hBs hBsym hBell (identityDrift_smooth d) hb.1 hb.2
  have hreal : RealizesTerminalEvolution (PDE.euclideanBall v₀ R) (fun _ => 0)
      (PDE.isOpen_euclideanBall v₀ R).measurableSet
      (zIndependentCoefficient B) (identityDrift d) S K := ⟨hc, hi, he, hcomp⟩
  refine ⟨(S, K), hreal, ?_⟩
  intro E hE
  obtain ⟨hS, hK⟩ := terminalEvolution_unique (PDE.euclideanBall v₀ R) (fun _ => 0)
    hΩ (zIndependentCoefficient B) (identityDrift d) E.1 S E.2 K hE hreal
  exact Prod.ext hS hK

end HypoellipticAleksandrov.KineticAleksandrov.LocalA

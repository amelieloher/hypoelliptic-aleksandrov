module

public import HypoellipticAleksandrov.KineticAleksandrov.SourceProblem.LocalizedBound

/-!
# The localized bound `0 ≤ V ≤ C R^(d/(d+1)) ‖F‖_{L^{d+1}}` (companion paper, Proposition 4.2)

The upper bound is the interior Krylov estimate
applied to the reflected and rescaled solution
of `LocalizedKrylov.lean`; the Jacobian of the scaling is `R^(d+2)`, giving the factor
`R^(d/(d+1))`.  The estimate holds on the whole closed cylinder: the open cylinder by Krylov,
the rest by continuity of `V`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic MeasureTheory Set Filter
open scoped Topology MatrixOrder Matrix.Norms.Elementwise ENNReal

variable {d : ℕ}

/-- The localized bound with the `L^{d+1}` norm of `F` over the source cylinder itself. -/
theorem localizedBound_cylinder
    (hd : 0 < d) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (B : CoefficientField d) (_ : ∀ r v, (B r v).IsSymm) (_ : IsSmoothCoefficient B)
        (_ : ∀ r v, lam • (1 : PDE.Mat d) ≤ B r v)
        (_ : ∀ r v, B r v ≤ Lam • (1 : PDE.Mat d))
        (F : TimeVelocity d → ℝ) (_ : ∀ z, 0 ≤ F z) (_ : ContDiff ℝ (⊤ : ℕ∞) F)
        (_ : HasCompactSupport F) (_ : tsupport F ⊆ Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ)
        (α : ℝ) (_ : 0 ≤ α) (_ : α < 1) (vStar : PDE.Vec d) (R : ℝ) (_ : 0 < R)
        (_ : R ^ 2 = max 1 (4 * d * Lam))
        (V : TimeVelocity d → ℝ)
        (_ : IsClassicalBackwardDirichletSolution α 1 (PDE.euclideanBall vStar R) B
          (fun _ _ => 0) (fun _ _ => 0) (fun r v => -F (r, v)) (fun _ => 0) (fun _ => 0) V),
        ∀ z ∈ scalarParabolicClosedCylinder α 1 (PDE.euclideanBall vStar R),
          0 ≤ V z ∧ V z ≤ C * R ^ ((d : ℝ) / ((d : ℝ) + 1)) *
            parabolicLpNormOn d F
              (scalarParabolicOpenCylinder α 1 (PDE.euclideanBall vStar R)) := by
  exact localizedBound_cylinder_direct hd hlam hLam

/-- The restricted `L^{d+1}` norm of a continuous compactly supported function is at most its
global one. -/
theorem parabolicLpNormOn_le_parabolicLpNorm {F : TimeVelocity d → ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) (S : Set (TimeVelocity d)) :
    parabolicLpNormOn d F S ≤ parabolicLpNorm d F := by
  have hfin : eLpNorm F (parabolicExponent d) volume ≠ ⊤ :=
    (hF.memLp_of_hasCompactSupport (p := parabolicExponent d) (μ := volume) hFc).ne
  exact ENNReal.toReal_mono hfin (eLpNorm_mono_measure F Measure.restrict_le_self)

/-- Localized bound `0 ≤ V ≤ C R^(d/(d+1)) ‖F‖_{L^{d+1}}`, with the global `L^{d+1}` norm. -/
theorem localizedBound
    (hd : 0 < d) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (B : CoefficientField d) (_ : ∀ r v, (B r v).IsSymm) (_ : IsSmoothCoefficient B)
        (_ : ∀ r v, lam • (1 : PDE.Mat d) ≤ B r v)
        (_ : ∀ r v, B r v ≤ Lam • (1 : PDE.Mat d))
        (F : TimeVelocity d → ℝ) (_ : ∀ z, 0 ≤ F z) (_ : ContDiff ℝ (⊤ : ℕ∞) F)
        (_ : HasCompactSupport F) (_ : tsupport F ⊆ Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ)
        (α : ℝ) (_ : 0 ≤ α) (_ : α < 1) (vStar : PDE.Vec d) (R : ℝ) (_ : 0 < R)
        (_ : R ^ 2 = max 1 (4 * d * Lam))
        (V : TimeVelocity d → ℝ)
        (_ : IsClassicalBackwardDirichletSolution α 1 (PDE.euclideanBall vStar R) B
          (fun _ _ => 0) (fun _ _ => 0) (fun r v => -F (r, v)) (fun _ => 0) (fun _ => 0) V),
        ∀ z ∈ scalarParabolicClosedCylinder α 1 (PDE.euclideanBall vStar R),
          0 ≤ V z ∧ V z ≤ C * R ^ ((d : ℝ) / ((d : ℝ) + 1)) * parabolicLpNorm d F := by
  obtain ⟨C, hC0, hbound⟩ := localizedBound_cylinder hd hlam hLam
  refine ⟨C, hC0, ?_⟩
  intro B hsymm hsmooth hlow hup F hF0 hFs hFc hFsupp α hα0 hα1 vStar R hR hRsq V hV z hz
  obtain ⟨h0, h1⟩ := hbound B hsymm hsmooth hlow hup F hF0 hFs hFc hFsupp α hα0 hα1 vStar R hR
    hRsq V hV z hz
  refine ⟨h0, h1.trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (parabolicLpNormOn_le_parabolicLpNorm hFs.continuous hFc _)
    (mul_nonneg hC0 (Real.rpow_nonneg hR.le _))

end HypoellipticAleksandrov.KineticAleksandrov.Occupation

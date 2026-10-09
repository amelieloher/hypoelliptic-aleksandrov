module

public import HypoellipticAleksandrov.KineticAleksandrov.SourceProblem.LocalizedAdmissibility
public import HypoellipticAleksandrov.KineticAleksandrov.SourceProblem.InteriorEstimate

/-!
# The localized bound `0 ≤ V ≤ C R^(d/(d+1)) ‖F‖_{L^{d+1}}` (companion paper, Proposition 4.2)

The upper bound uses the interior Aleksandrov estimate applied to the reflected and rescaled
solution
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
theorem localizedBound_cylinder_direct
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
  obtain ⟨C, hC0, hK⟩ :=
    LsuFree.parabolic_aleksandrov_direct d hd lam Lam hlam hLam
  refine ⟨C, hC0, ?_⟩
  intro B hsymm hsmooth hlow hup F hF0 hFs hFc hFsupp α hα0 hα1 vStar R hR hRsq V hV
  obtain ⟨hInterior, hValue, hcoef, hsy, hbd, hpos, hle, hmem, hpde, -, hzero, hnorm, hnonneg⟩ :=
    localizedKrylov_admissible_direct hd hlam hLam hsymm hsmooth hlow hup hF0 hFs hFc hFsupp
      hα0 hα1 hR hRsq hV
  set Qk := krylovCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d) with hQk
  set QV := scalarParabolicOpenCylinder α 1 (PDE.euclideanBall vStar R) with hQV
  set M : ℝ := C * R ^ ((d : ℝ) / ((d : ℝ) + 1)) *
    parabolicLpNormOn d F QV with hM
  -- Krylov's estimate on the open cylinder
  have hqk := hK (localHeight α R) (0 : PDE.Vec d) (localHeight α R) hpos hle
    (localizedCoefficient R vStar B) (localizedSource R vStar F) (localizedScaled R vStar V)
    hcoef hsy hbd hmem hInterior hValue
    (ae_restrict_of_forall_mem (isOpen_krylovCylinder _ _ _).measurableSet
      (fun z hz => (hpde z hz).le))
    (fun z hz => (hzero z hz).le)
  have hopen : ∀ w ∈ QV, V w ≤ M := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := exists_mem_krylovCylinder hR hw
    have h1 := hqk z hz
    rw [hnorm] at h1
    change V (reflectScale R vStar z) ≤ _ at h1
    simpa only [hM, mul_assoc] using h1
  -- extension to the closed cylinder by continuity
  have hclosure : closure QV = scalarParabolicClosedCylinder α 1 (PDE.euclideanBall vStar R) := by
    rw [hQV, scalarParabolicOpenCylinder, closure_prod_eq, closure_Ioo hα1.ne]
    rfl
  intro z hz
  refine ⟨hnonneg z hz, ?_⟩
  have hQK : QV ⊆ scalarParabolicClosedCylinder α 1 (PDE.euclideanBall vStar R) :=
    subset_closure.trans hclosure.le
  have hzc : z ∈ closure QV := by rw [hclosure]; exact hz
  exact ContinuousWithinAt.closure_le hzc ((hV.1 z hz).mono hQK) continuousWithinAt_const hopen

/-- The restricted `L^{d+1}` norm of a continuous compactly supported function is at most its
global one. -/
theorem parabolicLpNormOn_le_parabolicLpNorm_direct
    {F : TimeVelocity d → ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) (S : Set (TimeVelocity d)) :
    parabolicLpNormOn d F S ≤ parabolicLpNorm d F := by
  have hfin : eLpNorm F (parabolicExponent d) volume ≠ ⊤ :=
    (hF.memLp_of_hasCompactSupport (p := parabolicExponent d) (μ := volume) hFc).ne
  exact ENNReal.toReal_mono hfin (eLpNorm_mono_measure F Measure.restrict_le_self)

/-- Localized bound `0 ≤ V ≤ C R^(d/(d+1)) ‖F‖_{L^{d+1}}`, with the global `L^{d+1}` norm. -/
theorem localizedBound_direct
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
  obtain ⟨C, hC0, hbound⟩ := localizedBound_cylinder_direct hd hlam hLam
  refine ⟨C, hC0, ?_⟩
  intro B hsymm hsmooth hlow hup F hF0 hFs hFc hFsupp α hα0 hα1 vStar R hR hRsq V hV z hz
  obtain ⟨h0, h1⟩ := hbound B hsymm hsmooth hlow hup F hF0 hFs hFc hFsupp α hα0 hα1 vStar R hR
    hRsq V hV z hz
  refine ⟨h0, h1.trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (parabolicLpNormOn_le_parabolicLpNorm_direct hFs.continuous hFc _)
    (mul_nonneg hC0 (Real.rpow_nonneg hR.le _))

end HypoellipticAleksandrov.KineticAleksandrov.Occupation

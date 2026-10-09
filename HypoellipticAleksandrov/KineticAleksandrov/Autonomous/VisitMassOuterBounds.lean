module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationFiniteBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalBoundary

/-! # The actual retained exit terms have total partial mass at most one -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

/-- Every actual zero-extended exit kernel has mass at most one. -/
theorem visitUnionExitKernel_mass_le_one
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (s T : ℝ) (p : Point) :
    visitUnionExitKernel hH hLE hlam hLam A H s T p univ ≤ 1 := by
  classical
  change (if hp : p ∈ visitPoleSet H s T then
    finiteUnionExit hH hLE hlam hLam A H T
      (visitPoleInclusion H s T ⟨p, hp⟩) else 0) univ ≤ 1
  split
  · simp only [measure_univ, le_refl]
  · exact zero_le

/-- The real masses of all retained active exits in a finite visit sum add to at most one. -/
theorem visitRetainedExit_partial_real_mass_le_one
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (hT : s < T)
    (P : Point) (hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (N : ℕ) :
    ∑ n ∈ Finset.range N,
      (((visitUnionExitKernel hH hLE hlam hLam A (visitActiveUnion c J) s T ∘ₘ
        visitEntrancePiece hH hLE hlam hLam A c J s T P n).restrict
          (visitBoundary s T (visitActiveInterval c) J)ᶜ) univ).toReal ≤ 1 := by
  have he := visitActiveExit_partial_le hH hLE hlam hLam A c J s T hT P hP N
  have hm := (he univ).trans
    (visitUnionExitKernel_mass_le_one hH hLE hlam hLam A J.toFiniteUnion s T P)
  have hr := ENNReal.toReal_mono (by simp) hm
  rw [ENNReal.toReal_one, visit_partial_real_mass _ N univ MeasurableSet.univ] at hr
  convert hr using 1
  apply Finset.sum_congr rfl
  intro n _
  rw [visitActiveExitKernel_retained_eq_outer hH hLE hlam hLam A c J s T _
    (visitEntrancePiece_ae_activePole hH hLE hlam hLam A c J s T P hP n)]

/-- On an interior physical pole, the single-interval union kernel is the original strip Green. -/
theorem visitOuterGreen_eq_strip
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (J : Interval) (s T : ℝ) (P : Point)
    (hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) :
    visitUnionGreenKernel hH hLE hlam hLam A J.toFiniteUnion s T P =
      stripGreen hH hLE hlam hLam A J T
        ⟨P, WithTop.coe_lt_coe.mpr hP.2.1, hP.2.2⟩ := by
  classical
  have hp : P ∈ visitPoleSet J.toFiniteUnion s T := by
    exact ⟨hP.1, hP.2.1, by simpa only [Interval.toFiniteUnion_carrier] using hP.2.2⟩
  change (if ht : P ∈ visitPoleSet J.toFiniteUnion s T then
    finiteUnionGreen hH hLE hlam hLam A J.toFiniteUnion T
      (visitPoleInclusion _ s T ⟨P, ht⟩) else 0) = _
  rw [dite_eq_left hp]
  rfl

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

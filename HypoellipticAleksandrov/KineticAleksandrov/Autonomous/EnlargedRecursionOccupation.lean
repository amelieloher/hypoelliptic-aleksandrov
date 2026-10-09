module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionFullSpace

/-! # Domination of finite enlarged active occupations by full-space evolution -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal

/-- Every killed strip occupation is dominated by the full-space physical occupation. -/
theorem enlarged_stripGreen_le_fullspace
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (P : Point) (T : ℝ) (hT : 0 < T)
    (hv : P.velocity 0 ∈ H.carrier) :
    stripGreen hH hLE hlam hLam A H (P.time + T)
      ⟨P, WithTop.coe_lt_coe.mpr (by linarith), hv⟩ ≤
      enlargedFullSpaceOccupation hH hLE hlam hLam A P T := by
  let e : StripPole H ((P.time + T : ℝ) : WithTop ℝ) :=
    ⟨P, WithTop.coe_lt_coe.mpr (by linarith), hv⟩
  let E := fullSpaceEvolution hH hLE hlam hLam A
  have hmono := strip_kernel_le_fullspace hH hLE hlam hLam A E
    (fullSpaceEvolution_spec hH hLE hlam hLam A) H
    (stripEvolution hH hLE hlam hLam A H) (stripEvolution_spec hH hLE hlam hLam A H)
  apply Measure.le_iff.mpr
  intro B hB
  let F : Point → ℝ≥0∞ := B.indicator 1
  have hF : Measurable F := measurable_one.indicator hB
  rw [← lintegral_indicator_one hB, ← lintegral_indicator_one hB]
  change (∫⁻ p, F p ∂stripGreen hH hLE hlam hLam A H (P.time + T) e) ≤
    ∫⁻ p, F p ∂enlargedFullSpaceOccupation hH hLE hlam hLam A P T
  rw [stripGreen_lintegral hH hLE hlam hLam A H (P.time + T) e F hF,
    enlargedFullSpaceOccupation_elapsed_lintegral hH hLE hlam hLam A P T hT F hF]
  have hh : stripHorizon ((P.time + T : ℝ) : WithTop ℝ) P.time = ENNReal.ofReal T := by
    simp [stripHorizon]
  let K := (stripEvolution hH hLE hlam hLam A H).2
  let p := stripPoleState H ((P.time + T : ℝ) : WithTop ℝ) e
  change (∫⁻ t, ∫⁻ w, F (elapsedPhysicalPoint P.time (t, w))
    ∂K.master (elapsedQuery P.time p t)
    ∂elapsedVolume (stripHorizon ((P.time + T : ℝ) : WithTop ℝ) P.time)) ≤
      ∫⁻ t : ElapsedTime (ENNReal.ofReal T),
        ∫⁻ z, F (enlargedTerminalPoint (P.time + t.1) z)
          ∂kernelXV E (Real.toNNReal t.1) (P.position 0, P.velocity 0)
          ∂elapsedVolume (ENNReal.ofReal T)
  rw [hh]
  apply lintegral_mono
  intro t
  have hm := hmono (elapsedQuery P.time (stripPoleState H (P.time + T) e) t)
  have hi := lintegral_mono' hm (f := fun w => F ⟨P.time + t.1, w.2, w.1⟩) le_rfl
  have hq : largeQueryOfSmall (strip_subset_fullspace H)
      (elapsedQuery P.time (stripPoleState H (P.time + T) e) t) =
      wholeSpaceQuery P.time (P.time + t.1) (by linarith [t.2.1]) P.velocity P.position := rfl
  rw [hq] at hi
  exact hi.trans_eq (enlargedFullSpace_native_elapsed_lintegral
    hH hLE hlam hLam A P t.1 t.2.1.le F hF)

/-- Every finite enlarged active sum is dominated by the actual full-space occupation. -/
theorem enlarged_active_occupation_le_fullspace
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T : ℝ) (hT : 0 < T)
    (P : Point) (hv : P.velocity 0 ∈ J.carrier) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      enlargedActivePiece hH hLE hlam hLam A c J P.time (P.time + T) P n) ≤
        enlargedFullSpaceOccupation hH hLE hlam hLam A P T := by
  classical
  have hP : P.time ≤ P.time ∧ P.time < P.time + T ∧ P.velocity 0 ∈ J.carrier :=
    ⟨le_rfl, by linarith, hv⟩
  have h := (enlarged_piece_domination hH hLE hlam hLam A c J P.time (P.time + T) P hP N).2
  apply (h.trans Measure.restrict_le_self).trans
  have hp : P ∈ enlargedVisitPoleSet J.toFiniteUnion (P.time + T) :=
    ⟨by linarith, by simpa only [Interval.toFiniteUnion_carrier] using hv⟩
  change (if h : P ∈ enlargedVisitPoleSet J.toFiniteUnion (P.time + T) then
    finiteUnionGreen hH hLE hlam hLam A J.toFiniteUnion (P.time + T)
      (enlargedVisitPole _ _ ⟨P, h⟩) else 0) ≤ _
  rw [dite_eq_left hp]
  unfold finiteUnionGreen
  exact enlarged_stripGreen_le_fullspace hH hLE hlam hLam A _ P T hT
    (finiteUnionComponentPole J.toFiniteUnion (P.time + T)
      (enlargedVisitPole _ _ ⟨P, hp⟩)).2.2

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

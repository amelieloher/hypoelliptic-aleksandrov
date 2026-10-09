module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassGreenCapacity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassIntegratedGreen
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassArithmetic
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassSummation

/-! # Finiteness and uniform mass bounds for the actual entrance counting measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

/-- The actual finite entrance count satisfies the quadratic source estimate. -/
theorem visitCount_partial_quadratic_bound
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (hT : s < T)
    (P : Point) (hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) (N : ℕ) :
    5 / 16 * c.r ^ 2 *
      ((∑ n ∈ Finset.range N, visitEntrancePiece hH hLE hlam hLam A c J s T P n) univ).toReal ≤
        9 / 16 * c.r ^ 2 + 6 * Lam / lam * ((J.hi - J.lo) / 2) * c.r := by
  have h := visitQuadratic_partial_mass_bound hH hLE hlam hLam A c J s T P hP N
  have he := visitRetainedExit_partial_real_mass_le_one hH hLE hlam hLam A c J s T hT P hP N
  have hg := visitActiveGreen_partial_capacity hH hLE hlam hLam A c J s T hT P hP N
  dsimp only at h he hg
  have hh := h.trans (add_le_add
    (mul_le_mul_of_nonneg_left he (by positivity))
    (mul_le_mul_of_nonneg_left hg (by linarith)))
  rw [visit_partial_real_mass _ N univ MeasurableSet.univ]
  convert hh using 1 <;> ring

/-- One ellipticity constant bounds the genuine full visit count in every bounded outer strip. -/
theorem exists_visitCount_mass_constant {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
        (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (_hT : s < T)
        (P : Point) (_hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier),
        Measure.sum (visitEntrancePiece hH hLE hlam hLam A c J s T P) univ ≤
          ENNReal.ofReal (C * (1 + ((J.hi - J.lo) / 2) / c.r)) := by
  obtain ⟨C, hC, hc⟩ := exists_visit_mass_arithmetic_constant hlam hLam
  refine ⟨C, hC, ?_⟩
  intro hH hLE A c J s T hT P hP
  apply visit_sum_mass_le_of_partial_mass_le
  intro N
  have hw : 0 < J.hi - J.lo := sub_pos.mpr J.ordered
  have hr := c.positive
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ univ) (by positivity)).mpr
  exact hc ((J.hi - J.lo) / 2) c.r _ (by linarith [J.ordered]) c.positive
    (visitCount_partial_quadratic_bound hH hLE hlam hLam A c J s T hT P hP N)

/-- The actual full entrance count is finite, without assuming its finiteness in the proof. -/
theorem visitCount_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ) (hT : s < T)
    (P : Point) (hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier) :
    IsFiniteMeasure (Measure.sum (visitEntrancePiece hH hLE hlam hLam A c J s T P)) := by
  obtain ⟨C, _, hc⟩ := exists_visitCount_mass_constant hlam hLam
  exact ⟨(hc hH hLE A c J s T hT P hP).trans_lt ENNReal.ofReal_lt_top⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitTimePartialBound
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassSummation

/-! # Uniform short-time bounds for the full actual entrance counting measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

/-- The full genuine visit count in every closed clock-time interval has uniformly bounded mass. -/
theorem exists_visitTime_mass_constant {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
        (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T b : ℝ) (_hT : s < T)
        (P : Point) (_hP : s < P.time ∧ P.time < T ∧ P.velocity 0 ∈ J.carrier),
        Measure.sum (visitEntrancePiece hH hLE hlam hLam A c J s T P)
          {p | p.time ∈ Icc b (b + c.r ^ 2)} ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC, hc⟩ := exists_visitTime_partial_constant hlam hLam
  refine ⟨C, hC, ?_⟩
  intro hH hLE A c J s T b hT P hP
  let W : Set Point := {p | p.time ∈ Icc b (b + c.r ^ 2)}
  have hW : MeasurableSet W := isClosed_Icc.measurableSet.preimage continuous_time.measurable
  rw [Measure.sum_apply _ hW]
  apply ENNReal.tsum_le_of_sum_range_le
  intro N
  rw [← Measure.finsetSum_apply]
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ W) hC.le).mpr
  rw [visit_partial_real_mass _ N W hW]
  exact hc hH hLE A c J s T b hT P hP N

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

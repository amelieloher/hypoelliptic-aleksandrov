module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionStartDomination
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionCellCountBounds

/-! # The literal source box actions of full-space terminal and occupation measures -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory
open scoped Classical ENNReal

/-- Full-space terminal mass in the physical source box is its elapsed box probability. -/
theorem positionStartFullSpaceTerminal_box
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (P : Point) (Y b : ℝ) :
    enlargedFullSpaceTerminal hH hLE hlam hLam A P (P.time + b) (positionStartBox c Y) =
      kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal b)
        (P.position 0, P.velocity 0) (box 4 c.r Y) := by
  unfold enlargedFullSpaceTerminal
  rw [Measure.map_apply (enlargedTerminalPoint_measurable _)
    (measurableSet_positionStartBox c Y), add_sub_cancel_left]
  rfl

/-- The full-space occupation mass in a physical slab is the source iterated box action. -/
theorem positionStartFullSpaceOccupation_box_slab
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (P : Point) (Y a b T : ℝ)
    (ha : 0 ≤ a) (hb : b ≤ T) :
    enlargedFullSpaceOccupation hH hLE hlam hLam A P T
      ({q : Point | P.time + a < q.time ∧ q.time ≤ P.time + b} ∩ positionStartBox c Y) =
      ∫⁻ t in Ioc a b, kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal t)
        (P.position 0, P.velocity 0) (box 4 c.r Y) := by
  let S := {q : Point | P.time + a < q.time ∧ q.time ≤ P.time + b}
  let W := positionStartBox c Y
  have hS : MeasurableSet S :=
    (isOpen_lt continuous_const continuous_time).measurableSet.inter
      (isClosed_le continuous_time continuous_const).measurableSet
  have hW := measurableSet_positionStartBox c Y
  let F : Point → ℝ≥0∞ := (S ∩ W).indicator 1
  have hF : Measurable F := measurable_one.indicator (hS.inter hW)
  rw [← lintegral_indicator_one (hS.inter hW)]
  change (∫⁻ p, F p ∂enlargedFullSpaceOccupation hH hLE hlam hLam A P T) = _
  rw [enlargedFullSpaceOccupation_lintegral hH hLE hlam hLam A P T F hF]
  have he (t : ℝ) : (∫⁻ z, F (enlargedTerminalPoint (P.time + t) z)
      ∂kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal t)
        (P.position 0, P.velocity 0)) =
      (Ioc a b).indicator (fun u => kernelXV (fullSpaceEvolution hH hLE hlam hLam A)
        (Real.toNNReal u) (P.position 0, P.velocity 0) (box 4 c.r Y)) t := by
    by_cases ht : t ∈ Ioc a b
    · rw [indicator_of_mem ht, ← lintegral_indicator_one (box_measurable 4 c.r Y)]
      apply lintegral_congr
      intro z
      have heq : enlargedTerminalPoint (P.time + t) z ∈ S ∩ W ↔ z ∈ box 4 c.r Y := by
        change ((P.time + a < P.time + t ∧ P.time + t ≤ P.time + b) ∧
          z ∈ box 4 c.r Y) ↔ z ∈ box 4 c.r Y
        have hs : P.time + a < P.time + t ∧ P.time + t ≤ P.time + b := by
          constructor <;> linarith only [ht.1, ht.2]
        exact and_iff_right hs
      simp only [F, Set.indicator, heq, Pi.one_apply]
    · rw [indicator_of_notMem ht]
      have hz : (fun z : Z => F (enlargedTerminalPoint (P.time + t) z)) =
          fun _ => (0 : ℝ≥0∞) := by
        funext z
        have hn : enlargedTerminalPoint (P.time + t) z ∉ S ∩ W := by
          intro hz
          apply ht
          have hs : P.time + a < P.time + t ∧ P.time + t ≤ P.time + b := hz.1
          constructor <;> linarith only [hs.1, hs.2]
        exact indicator_of_notMem hn _
      rw [hz, lintegral_zero]
  simp_rw [he]
  rw [lintegral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc]
  have hs : Ioc a b ∩ Ioc 0 T = Ioc a b :=
    inter_eq_left.mpr (fun _ ht => ⟨ha.trans_lt ht.1, ht.2.trans hb⟩)
  rw [hs]

/-- The extended slab box action equals the ofReal of the actual integrable real action. -/
theorem positionStartBox_slab_ofReal_integral (E : FullSpaceEvolution) (z : Z)
    (r Y a b : ℝ) :
    ENNReal.ofReal (∫ t in Ioc a b, (kernelXV E (Real.toNNReal t) z (box 4 r Y)).toReal) =
      ∫⁻ t in Ioc a b, kernelXV E (Real.toNNReal t) z (box 4 r Y) := by
  rw [ofReal_integral_eq_lintegral_ofReal
    (position_box_probability_integrable E z 4 r Y a b)
    (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)]
  apply lintegral_congr
  intro t
  exact ENNReal.ofReal_toReal ((measure_mono (subset_univ _)).trans_lt
    ((kernelXV_mass_le_one E (Real.toNNReal t) z).trans_lt ENNReal.one_lt_top)).ne

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

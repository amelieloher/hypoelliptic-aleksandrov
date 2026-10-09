module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionStartPointBounds

/-! # The position-start count inequality before full-space domination -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

/-- Pull the literal phase-space source box back to physical spacetime. -/
def positionStartBox (c : Clock) (Y : ℝ) : Set Point :=
  {q | (q.position 0, q.velocity 0) ∈ box 4 c.r Y}

/-- The physical source box is measurable. -/
theorem measurableSet_positionStartBox (c : Clock) (Y : ℝ) :
    MeasurableSet (positionStartBox c Y) :=
  (box_measurable 4 c.r Y).preimage
    (((continuous_apply 0).comp continuous_position).measurable.prodMk
      ((continuous_apply 0).comp continuous_velocity).measurable)

/-- One uniform generator constant bounds the count in every finite entrance mixture. -/
theorem positionStartQuadratic_slab_mass_bound {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
      (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s x a b : ℝ) (k : ℤ)
      (mu : Measure Point) [IsFiniteMeasure mu],
      |c.vbar| = 2 * c.r → closure c.active ⊆ J.carrier → a ≤ b →
      (∀ᵐ p ∂mu, p.velocity 0 ∈ closure c.entrance) →
      let Y := x + ((k : ℝ) + 1 / 2) * c.r ^ 3
      5 * c.r ^ 2 / 16 * enlargedPositionSlabMass mu c s x a b k ≤
        9 * c.r ^ 2 / 16 *
          ((positionStartTerminalKernel hH hLE hlam hLam A c J (s + b) ∘ₘ mu)
            (positionStartBox c Y)).toReal +
        C * ((coreAllTimeGreenKernel hH hLE hlam hLam A c ∘ₘ mu)
          ({q : Point | s + a < q.time ∧ q.time ≤ s + b} ∩ positionStartBox c Y)).toReal := by
  obtain ⟨C, hC, hbound⟩ := positionStartQuadratic_operator_bound hlam hLam
  refine ⟨C, hC, ?_⟩
  intro hH hLE A c J s x a b k mu _ hc hJ hab hmu
  dsimp only
  let Y := x + ((k : ℝ) + 1 / 2) * c.r ^ 3
  let f := fun q : Point => positionStartCutoff Y c.r c.positive (q.position 0) *
    visitQuadratic c (q.velocity 0)
  let g := fun q : Point => forwardScalarOperator A.a f q
  let S := {q : Point | s + a < q.time ∧ q.time ≤ s + b}
  let W := positionStartBox c Y
  let B := positionStartTerminalKernel hH hLE hlam hLam A c J (s + b) ∘ₘ mu
  let D := positionStartTerminalKernel hH hLE hlam hLam A c J (s + a) ∘ₘ mu
  let G := coreAllTimeGreenKernel hH hLE hlam hLam A c ∘ₘ mu
  have hS : MeasurableSet S :=
    (isOpen_lt continuous_const continuous_time).measurableSet.inter
      (isClosed_le continuous_time continuous_const).measurableSet
  have hW : MeasurableSet W := measurableSet_positionStartBox c Y
  have hactive := hmu.mono fun _ hp => enlarged_closedEntrance_subset_active c hp
  have hfB : Integrable f B := positionStartQuadratic_integrable c Y B
    (positionStartTerminalMixture_ae_closedActive hH hLE hlam hLam A c J (s + b) mu)
  have hgG : Integrable g G := positionStartQuadratic_operator_integrable
    hlam hLam A c Y hc G (positionStartAllTimeMixture_ae_active hH hLE hlam hLam A c mu)
  have hterm : (∫ q, f q ∂B) ≤ 9 * c.r ^ 2 / 16 * (B W).toReal := by
    have hh : (∫ q, f q ∂B) ≤ ∫ q, W.indicator (fun _ => 9 * c.r ^ 2 / 16) q ∂B := by
      apply integral_mono_ae hfB ((integrable_const _).indicator hW)
      filter_upwards [positionStartTerminalMixture_ae_closedActive
        hH hLE hlam hLam A c J (s + b) mu] with q hq
      have h := (positionStartQuadratic_box_bound c Y q hc hq).2
      change f q ≤ W.indicator (fun _ => 9 * c.r ^ 2 / 16) q
      by_cases hw : q ∈ W
      · rw [indicator_of_mem hw]
        simpa only [indicator_of_mem
          (show (q.position 0, q.velocity 0) ∈ box 4 c.r Y from hw), mul_one] using h
      · rw [indicator_of_notMem hw]
        simpa only [indicator_of_notMem
          (show (q.position 0, q.velocity 0) ∉ box 4 c.r Y from hw), mul_zero] using h
    rw [integral_indicator hW, integral_const] at hh
    simpa only [smul_eq_mul, Measure.real,
      Measure.restrict_apply MeasurableSet.univ, univ_inter, mul_comm] using hh
  have hop : -(∫ q in S, g q ∂G) ≤ C * (G (S ∩ W)).toReal := by
    have hh : (∫ q in S, -g q ∂G) ≤ ∫ q in S, W.indicator (fun _ => C) q ∂G := by
      apply integral_mono_ae hgG.neg.restrict (((integrable_const C).indicator hW).restrict)
      have ha : ∀ᵐ q ∂G.restrict S, q.velocity 0 ∈ c.active :=
        (positionStartAllTimeMixture_ae_active hH hLE hlam hLam A c mu).filter_mono
          (ae_mono Measure.restrict_le_self)
      filter_upwards [ha] with q hq
      change -g q ≤ W.indicator (fun _ => C) q
      have hb := (neg_le_abs (g q)).trans (hbound A c Y q hc hq)
      by_cases hw : q ∈ W
      · rw [indicator_of_mem hw]
        simpa only [indicator_of_mem
          (show (q.position 0, q.velocity 0) ∈ box 4 c.r Y from hw), mul_one] using hb
      · rw [indicator_of_notMem hw]
        simpa only [indicator_of_notMem
          (show (q.position 0, q.velocity 0) ∉ box 4 c.r Y from hw), mul_zero] using hb
    rw [integral_neg, integral_indicator hW, integral_const] at hh
    simpa only [smul_eq_mul, Measure.real,
      Measure.restrict_apply MeasurableSet.univ, univ_inter,
      Measure.restrict_apply hW, inter_comm, mul_comm] using hh
  have hi := positionStartQuadratic_integrated_slab_identity
    hH hLE hlam hLam A c J Y (s + a) (s + b) hc hJ mu hactive (by linarith only [hab])
  have hlo := positionStartQuadratic_slab_lower mu c s x a b k hmu
  have hn := positionStartQuadratic_terminal_integral_nonneg
    hH hLE hlam hLam A c J Y (s + a) mu
  change (∫ q in S, f q ∂mu) = (∫ q, f q ∂B) - (∫ q, f q ∂D) -
    ∫ q in S, g q ∂G at hi
  change 5 * c.r ^ 2 / 16 * enlargedPositionSlabMass mu c s x a b k ≤
    (∫ q in S, f q ∂mu) at hlo
  change 0 ≤ ∫ q, f q ∂D at hn
  change 5 * c.r ^ 2 / 16 * enlargedPositionSlabMass mu c s x a b k ≤
    9 * c.r ^ 2 / 16 * (B W).toReal + C * (G (S ∩ W)).toReal
  linarith only [hlo, hi, hn, hterm, hop]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

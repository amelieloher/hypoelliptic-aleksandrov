module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionStartMixtures

/-! # Integrating the literal position-start identity against actual starting measures -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory
open scoped Classical

/-- Finite active starting measures satisfy the exact position-resolved slab identity. -/
theorem positionStartQuadratic_integrated_slab_identity
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (Y a b : ℝ)
    (hc : |c.vbar| = 2 * c.r) (hJ : closure c.active ⊆ J.carrier)
    (mu : Measure Point) [IsFiniteMeasure mu]
    (hmu : ∀ᵐ p ∂mu, p.velocity 0 ∈ c.active) (hab : a ≤ b) :
    let f := fun q : Point => positionStartCutoff Y c.r c.positive (q.position 0) *
      visitQuadratic c (q.velocity 0)
    (∫ p in {q : Point | a < q.time ∧ q.time ≤ b}, f p ∂mu) =
      (∫ q, f q ∂(positionStartTerminalKernel hH hLE hlam hLam A c J b ∘ₘ mu)) -
      (∫ q, f q ∂(positionStartTerminalKernel hH hLE hlam hLam A c J a ∘ₘ mu)) -
      ∫ q in {q : Point | a < q.time ∧ q.time ≤ b}, forwardScalarOperator A.a f q
        ∂(coreAllTimeGreenKernel hH hLE hlam hLam A c ∘ₘ mu) := by
  dsimp only
  let f := fun q : Point => positionStartCutoff Y c.r c.positive (q.position 0) *
    visitQuadratic c (q.velocity 0)
  let g := fun q : Point => forwardScalarOperator A.a f q
  let S := {q : Point | a < q.time ∧ q.time ≤ b}
  let B := positionStartTerminalKernel hH hLE hlam hLam A c J b
  let D := positionStartTerminalKernel hH hLE hlam hLam A c J a
  let G := coreAllTimeGreenKernel hH hLE hlam hLam A c
  have hS : MeasurableSet S :=
    (isOpen_lt continuous_const continuous_time).measurableSet.inter
      (isClosed_le continuous_time continuous_const).measurableSet
  have hB : Integrable f (B ∘ₘ mu) :=
    positionStartQuadratic_integrable c Y _
      (positionStartTerminalMixture_ae_closedActive hH hLE hlam hLam A c J b mu)
  have hD : Integrable f (D ∘ₘ mu) :=
    positionStartQuadratic_integrable c Y _
      (positionStartTerminalMixture_ae_closedActive hH hLE hlam hLam A c J a mu)
  have hG : Integrable g (G ∘ₘ mu) :=
    positionStartQuadratic_operator_integrable hlam hLam A c Y hc _
      (positionStartAllTimeMixture_ae_active hH hLE hlam hLam A c mu)
  have hGs : Integrable (S.indicator g) (G ∘ₘ mu) := hG.indicator hS
  have hiB : Integrable (fun p => ∫ q, f q ∂B p) mu := by
    rw [Measure.comp_eq_comp_const_apply] at hB
    simpa only [Kernel.const_apply] using hB.integral_comp
  have hiD : Integrable (fun p => ∫ q, f q ∂D p) mu := by
    rw [Measure.comp_eq_comp_const_apply] at hD
    simpa only [Kernel.const_apply] using hD.integral_comp
  have hiG : Integrable (fun p => ∫ q, S.indicator g q ∂G p) mu := by
    rw [Measure.comp_eq_comp_const_apply] at hGs
    simpa only [Kernel.const_apply] using hGs.integral_comp
  have hp : S.indicator f =ᵐ[mu] fun p =>
      (∫ q, f q ∂B p) - (∫ q, f q ∂D p) - ∫ q, S.indicator g q ∂G p := by
    filter_upwards [hmu] with p hv
    have hi := positionStartQuadratic_slab_identity
      hH hLE hlam hLam A c J Y a b hc hJ p hv hab
    dsimp only at hi
    have he : G p = stripGreen hH hLE hlam hLam A c.activeInterval ⊤
        (densityClockPole c p hv) := by
      change (if h : p.velocity 0 ∈ c.active then _ else (0 : Measure Point)) = _
      rw [dite_eq_left hv]
      rfl
    rw [integral_indicator hS, he]
    exact hi
  change (∫ p in S, f p ∂mu) =
    (∫ q, f q ∂B ∘ₘ mu) - (∫ q, f q ∂D ∘ₘ mu) - ∫ q in S, g q ∂G ∘ₘ mu
  rw [← integral_indicator hS, integral_congr_ae hp]
  have he : (∫ p, (∫ q, f q ∂B p) - (∫ q, f q ∂D p) -
      (∫ q, S.indicator g q ∂G p) ∂mu) =
      (∫ p, (∫ q, f q ∂B p) - (∫ q, f q ∂D p) ∂mu) -
        ∫ p, ∫ q, S.indicator g q ∂G p ∂mu := integral_sub (hiB.sub hiD) hiG
  have hd : (∫ p, (∫ q, f q ∂B p) - (∫ q, f q ∂D p) ∂mu) =
      (∫ p, ∫ q, f q ∂B p ∂mu) - ∫ p, ∫ q, f q ∂D p ∂mu := integral_sub hiB hiD
  rw [he, hd,
    ← nested_integral_bind mu B B.measurable f hB,
    ← nested_integral_bind mu D D.measurable f hD,
    ← nested_integral_bind mu G G.measurable (S.indicator g) hGs,
    integral_indicator hS]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

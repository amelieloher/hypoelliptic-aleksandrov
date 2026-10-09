module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockCalculusAssembly
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockExtensionsSetting

/-! # Joint source conclusion of the position-clock lemma

All components use the same literal clock and the same constructed extensions.
No external analytic statement is needed for this coordinate change.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open MeasureTheory
open HypoellipticAleksandrov.KineticAleksandrov.TheoremA
open HypoellipticAleksandrov.KineticAleksandrov.Decay

/-- `l:clock`: the exact position clock, volume factor, operator conjugacy, and uniform
case-I coefficient extensions, with a single pair of extension witnesses. -/
theorem positionClock_holds {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) :
    (∀ v ∈ c.active, Real.sign v = Real.sign c.vbar ∧
      |c.vbar| / 2 ≤ |v| ∧ |v| ≤ 3 * |c.vbar| / 2) ∧
    (∀ p, c.inverse e (c.map e p) = p ∧ c.map e (c.inverse e p) = p) ∧
    c.map e '' {p : Point | p.velocity 0 ∈ c.active} =
      {q : Point | q.velocity 0 ∈ normalizedActive} ∧
    ContDiff ℝ (⊤ : ℕ∞) (c.mapCoordinates e) ∧
    ContDiff ℝ (⊤ : ℕ∞) (c.inverseCoordinates e) ∧
    |c.inverseMatrix.det| = c.r ^ 6 ∧
    Measure.map (c.map e) volume = ENNReal.ofReal (c.r ^ 6) • (volume : Measure Point) ∧
    (∀ h : Point → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) (h ∘ scalarPoint)
        {q : Fin 3 → ℝ | q 2 ∈ normalizedActive} →
      ∀ p : Point, p.velocity 0 ∈ c.active →
        forwardScalarOperator A.a (h ∘ c.map e) p =
          |p.velocity 0| / (|c.vbar| * c.r ^ 2) *
            transportedForwardOperator (c.normalizedCoefficient A.a e) c.normalizedDrift
              (h ∘ sectionTwoPoint) (sectionTwoPoint (c.map e p))) ∧
    ∃ B : ℝ → ℝ → ℝ, ∃ b : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry B) ∧
      ContDiff ℝ (⊤ : ℕ∞) b ∧
      (∀ s y, y ∈ normalizedActive → B s y = c.diffusion A.a e s y) ∧
      (∀ y ∈ normalizedActive, b y = c.drift y) ∧
      (∀ s y, 3 * lam / 5 ≤ B s y ∧ B s y ≤ 3 * Lam) ∧
      (∀ y, (9 / 25 : ℝ) ≤ deriv b y ∧ deriv b y ≤ 9) ∧
      SourceSetting (3 * lam / 5) (3 * Lam) (9 / 25) 9
        (PDE.oneDimensionalAxisBox (-3 / 4) (3 / 4))
        (fun s y _ _ => B s (y 0)) (fun y _ => b (y 0)) := by
  refine ⟨?_, ?_, c.strip_image e, c.mapCoordinates_smooth e,
    c.inverseCoordinates_smooth e, c.abs_det_inverseMatrix, c.map_volume e, ?_, ?_⟩
  · intro v hv
    exact ⟨c.active_sign hv, c.active_abs_bounds hv⟩
  · intro p
    exact ⟨c.inverse_map e p, c.map_inverse e p⟩
  · intro h hh p hp
    exact c.conjugacy A.a e h hh p hp
  · refine ⟨c.extendedDiffusion lam A.a e, c.extendedDrift,
      c.extendedDiffusion_smooth A e, c.extendedDrift_smooth, ?_, ?_, ?_, ?_,
      c.extended_sourceSetting hlam hLam A e⟩
    · intro s y hy
      exact c.extendedDiffusion_eq A.a e s y hy
    · intro y hy
      exact c.extendedDrift_eq hy
    · intro s y
      exact c.extendedDiffusion_bounds hlam hLam A e s y
    · intro y
      exact c.extendedDrift_deriv_bounds y

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

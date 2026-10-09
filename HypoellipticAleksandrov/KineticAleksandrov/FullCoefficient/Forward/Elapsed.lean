module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Forward.Duhamel

/-!
# The forward equation in elapsed time

The forward equation: translating the absolute-time statement of `Forward/Duhamel.lean` by the
pole time `σ₀` gives the form with elapsed time `τ ∈ (0, T)`, in which the coefficient is
evaluated at `σ₀ + τ`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open Set MeasureTheory
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal

variable {d : ℕ}

/-- The forward expression in elapsed time: the coefficient is evaluated at `σ₀ + τ`. -/
def forwardReprAt (B : FullKineticCoefficient d) (σ₀ : ℝ)
    (G : ℝ × EvolutionAmbientState d → ℝ) (q : ℝ × EvolutionAmbientState d) : ℝ :=
  jointTimePartial G q +
    ∑ i, ∑ j, B (σ₀ + q.1) q.2.1 q.2.2 i j * jointVelocityPartial i (jointVelocityPartial j G) q +
      ∑ i, q.2.1 i * jointPositionPartial i G q

/-- The function `G` read in absolute time `σ₀ + τ`. -/
def absoluteTime (σ₀ : ℝ) (G : ℝ × EvolutionAmbientState d → ℝ) :
    ℝ × EvolutionAmbientState d → ℝ :=
  fun q => G (q.1 - σ₀, q.2)

theorem add_shift (σ₀ : ℝ) (q : ℝ × EvolutionAmbientState d) :
    q + (-σ₀, 0) = (q.1 - σ₀, q.2) := by
  ext <;> simp [sub_eq_add_neg]

theorem absoluteTime_eq (σ₀ : ℝ) (G : ℝ × EvolutionAmbientState d → ℝ) :
    absoluteTime σ₀ G = fun q => G (q + (-σ₀, 0)) := by
  funext q
  simp only [absoluteTime, add_shift]

theorem jointTimePartial_absoluteTime (σ₀ : ℝ) (G : ℝ × EvolutionAmbientState d → ℝ)
    (q : ℝ × EvolutionAmbientState d) :
    jointTimePartial (absoluteTime σ₀ G) q = jointTimePartial G (q.1 - σ₀, q.2) := by
  unfold jointTimePartial
  rw [absoluteTime_eq, fderiv_comp_add_right, add_shift]

theorem jointVelocityPartial_absoluteTime (σ₀ : ℝ) (G : ℝ × EvolutionAmbientState d → ℝ)
    (i : Fin d) :
    jointVelocityPartial i (absoluteTime σ₀ G) =
      absoluteTime σ₀ (jointVelocityPartial i G) := by
  funext q
  unfold jointVelocityPartial
  rw [absoluteTime_eq, fderiv_comp_add_right, add_shift]
  rfl

theorem jointPositionPartial_absoluteTime (σ₀ : ℝ) (G : ℝ × EvolutionAmbientState d → ℝ)
    (i : Fin d) :
    jointPositionPartial i (absoluteTime σ₀ G) =
      absoluteTime σ₀ (jointPositionPartial i G) := by
  funext q
  unfold jointPositionPartial
  rw [absoluteTime_eq, fderiv_comp_add_right, add_shift]
  rfl

theorem forwardRepr_absoluteTime (B : FullKineticCoefficient d) (σ₀ : ℝ)
    (G : ℝ × EvolutionAmbientState d → ℝ) (τ : ℝ) (y : EvolutionAmbientState d) :
    forwardRepr B (identityDrift d) (absoluteTime σ₀ G) (σ₀ + τ, y) =
      forwardReprAt B σ₀ G (τ, y) := by
  unfold forwardRepr forwardReprAt
  rw [jointTimePartial_absoluteTime]
  simp only [jointVelocityPartial_absoluteTime, jointPositionPartial_absoluteTime,
    absoluteTime, identityDrift, id_eq, add_sub_cancel_left]

theorem contDiff_absoluteTime (σ₀ : ℝ) {G : ℝ × EvolutionAmbientState d → ℝ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) : ContDiff ℝ (⊤ : ℕ∞) (absoluteTime σ₀ G) := by
  rw [absoluteTime_eq]
  exact hG.comp (contDiff_id.add contDiff_const)

theorem hasCompactSupport_absoluteTime (σ₀ : ℝ) {G : ℝ × EvolutionAmbientState d → ℝ}
    (hG : HasCompactSupport G) : HasCompactSupport (absoluteTime σ₀ G) := by
  rw [absoluteTime_eq]
  exact hG.comp_homeomorph (Homeomorph.addRight ((-σ₀, 0) : ℝ × EvolutionAmbientState d))

theorem tsupport_absoluteTime_subset (σ₀ T : ℝ) {G : ℝ × EvolutionAmbientState d → ℝ}
    (hG : tsupport G ⊆ Ioo 0 T ×ˢ univ) :
    tsupport (absoluteTime σ₀ G) ⊆ Ioo σ₀ (σ₀ + T) ×ˢ univ := by
  rw [absoluteTime_eq]
  have := tsupport_comp_eq_preimage G
    (Homeomorph.addRight ((-σ₀, 0) : ℝ × EvolutionAmbientState d))
  intro q hq
  have hq' : q ∈ (Homeomorph.addRight ((-σ₀, 0) : ℝ × EvolutionAmbientState d)) ⁻¹'
      tsupport G := by
    rw [← this]
    exact hq
  have h := (hG hq').1
  simp only [Homeomorph.coe_addRight, Prod.fst_add, mem_Ioo] at h
  exact ⟨⟨by linarith [h.1], by linarith [h.2]⟩, trivial⟩

/-- **Forward equation, smooth compactly supported tests in elapsed time**. -/
theorem integral_forwardReprAt_green_eq_zero {lam Lam : ℝ} (hd : 1 ≤ d) (hlam : 0 < lam)
    (hLam : lam ≤ Lam) (B : FullKineticCoefficient d) (hB : IsSmoothFullKineticCoefficient B)
    (hBs : IsSymmetricFullKineticCoefficient B) (hell : HasEverywhereLoewnerBounds lam Lam B)
    (S : TerminalOperatorFamily (wholeSpace d) (fun _ => 0))
    (K : MovingFiberKernel (wholeSpace d) (fun _ => 0))
    (hreal : RealizesTerminalEvolution (wholeSpace d) (fun _ => 0) MeasurableSet.univ B
      (identityDrift d) S K)
    (σ₀ T : ℝ) (hT : 0 < T) (p : EvolutionState (wholeSpace d) (fun _ => 0) σ₀)
    (Γ : Measure (ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d))
    (hΓ : IsGreenMeasure K σ₀ (ENNReal.ofReal T) (Measure.dirac p) Γ)
    {G : ℝ × EvolutionAmbientState d → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hGc : HasCompactSupport G) (hGs : tsupport G ⊆ Ioo 0 T ×ˢ univ) :
    ∫ q, forwardReprAt B σ₀ G (q.1.1, q.2) ∂Γ = 0 := by
  obtain ⟨T', rfl⟩ : ∃ T', T = T' - σ₀ := ⟨σ₀ + T, by ring⟩
  have hs := tsupport_absoluteTime_subset σ₀ (T' - σ₀) hGs
  rw [add_sub_cancel] at hs
  have := integral_forwardRepr_green_eq_zero hd hlam hLam B hB hBs hell S K hreal σ₀ T'
    (by linarith) p Γ hΓ (contDiff_absoluteTime σ₀ hG) (hasCompactSupport_absoluteTime σ₀ hGc) hs
  simpa only [forwardRepr_absoluteTime] using this

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

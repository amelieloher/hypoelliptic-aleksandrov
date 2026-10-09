module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionHorizonOrder
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GreenTestExtension

/-! # Bounded homogeneous potentials stopped at an observation time -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Filter Parabolic
open SectionTwo TheoremA Evolution
open scoped Classical

/-- Keep a homogeneous potential up to the observation time and set it to zero afterwards. -/
def enlargedStoppedPotential (b : ℝ) (u : Point → ℝ) (p : Point) : ℝ :=
  if p.time ≤ b then u p else 0

/-- A continuous past potential has a measurable stopped extension. -/
theorem enlargedStoppedPotential_measurable (b : ℝ) (u : Point → ℝ)
    (hc : ContinuousOn u {p | p.time ≤ b}) : Measurable (enlargedStoppedPotential b u) :=
  hc.measurable_piecewise continuousOn_const
    (isClosed_le continuous_time continuous_const).measurableSet

/-- A bounded past potential has integrable stopped action against every finite measure. -/
theorem enlargedStoppedPotential_integrable (b : ℝ) (u : Point → ℝ)
    (hc : ContinuousOn u {p | p.time ≤ b}) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ p, p.time ≤ b → |u p| ≤ M) (mu : Measure Point) [IsFiniteMeasure mu] :
    Integrable (enlargedStoppedPotential b u) mu := by
  apply Integrable.mono' (integrable_const M)
    (enlargedStoppedPotential_measurable b u hc).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro p
  rw [Real.norm_eq_abs]
  unfold enlargedStoppedPotential
  split
  · exact hb p ‹p.time ≤ b›
  · simpa only [abs_zero] using hM

/-- The stopped exit action is bounded by the original homogeneous potential value.
Its C112 premises are discharged by the supplied full-space classical potential. -/
theorem enlarged_stripExit_stopped_potential_le
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤)
    (b T : ℝ) (hb : e.1.time < b) (hBT : b ≤ T) (u : Point → ℝ)
    (hphi : IsKineticC112On u {p | p.time < b})
    (hc : ContinuousOn u {p | p.time ≤ b}) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ p, p.time ≤ b → |u p| ≤ M)
    (hop : ∀ p, p.time < b → forwardScalarOperator A.a u p = 0)
    (hn : ∀ p, p.time ≤ b → 0 ≤ u p) :
    (∫ p, enlargedStoppedPotential b u p
      ∂stripExit hH hLE hlam hLam A H T (stripPoleFinite H e T (hb.trans_le hBT))) ≤
      u e.1 := by
  let S : Set Point := {p | p.time ≤ b}
  have hS : MeasurableSet S := (isClosed_le continuous_time continuous_const).measurableSet
  let E := stripExit hH hLE hlam hLam A H b (stripPoleFinite H e b hb)
  have hs : ∀ᵐ p ∂E, p ∈ S :=
    (stripExitOfRealization_ae_closed_future hH hlam hLam A H
      (stripEvolution hH hLE hlam hLam A H)
      (stripEvolution_spec hH hLE hlam hLam A H) b (stripPoleFinite H e b hb)).mono
        fun _ hp => hp.2.1
  have hint := enlargedStoppedPotential_integrable b u hc M hM hbound E
  have heq : enlargedStoppedPotential b u =ᵐ[E] u := hs.mono fun p hp => ite_eq_left hp
  have hu : Integrable u E := hint.congr heq
  have hdom : (stripExit hH hLE hlam hLam A H T
      (stripPoleFinite H e T (hb.trans_le hBT))).restrict S ≤ E := by
    rcases eq_or_lt_of_le hBT with rfl | hlt
    · exact Measure.restrict_le_self
    · exact enlarged_stripExit_early_closed_le hH hLE hlam hLam A H e b T hb hlt
  have hnn : 0 ≤ᵐ[E] u := hs.mono fun p hp => hn p hp
  have hm := integral_mono_measure hdom hnn hu
  have hsub : reconstructionStrip H (e.1.time - 1) b ⊆ {p | p.time < b} :=
    fun _ hp => hp.2.1
  have hr : IsKineticC112On u (reconstructionStrip H (e.1.time - 1) b) := by
    rcases hphi with ⟨hc0, ht, hx, hv, htc, hxc, hvc, hvvc⟩
    exact ⟨hc0.mono hsub, fun p hp => ht p (hsub hp), fun p hp => hx p (hsub hp),
      fun p hp => hv p (hsub hp), htc.mono hsub, hxc.mono hsub, hvc.mono hsub,
      hvvc.mono hsub⟩
  have hi := strip_identity_C112 hH hLE hlam hLam A H (e.1.time - 1) b
    (by linarith) (stripPoleFinite H e b hb) (by change e.1.time - 1 < e.1.time; linarith)
    u hr
      (hc.mono fun p hp => by
        rcases hp with hp | hp
        · exact hp.2.1.le
        · rcases hp with hp | hp
          · exact hp.1.le
          · exact hp.2.1.le)
      ⟨M, fun p hp => ⟨hbound p hp.2.1.le, by rw [hop p hp.2.1, abs_zero]; exact hM⟩⟩
  have hz : (∫ p, forwardScalarOperator A.a u p
      ∂stripGreen hH hLE hlam hLam A H b (stripPoleFinite H e b hb)) = 0 := by
    apply integral_eq_zero_of_ae
    exact (stripGreenOfKernel_ae_mem_stripPast H _ b (stripPoleFinite H e b hb)).mono
      fun p hp => hop p hp.1
  rw [hz, sub_zero] at hi
  rw [← hi] at hm
  change (∫ p, S.indicator u p ∂_) ≤ u e.1
  rw [integral_indicator hS]
  exact hm

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

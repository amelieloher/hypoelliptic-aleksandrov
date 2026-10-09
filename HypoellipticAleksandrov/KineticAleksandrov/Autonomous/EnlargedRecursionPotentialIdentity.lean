module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionStoppedPotential

/-! # Exact stopped exit action of a supplied bounded homogeneous potential -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Filter Parabolic
open SectionTwo TheoremA Evolution

/-- The actual exit action equals the value of a bounded homogeneous classical potential. -/
theorem enlarged_stripExit_potential_identity
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤)
    (b : ℝ) (hb : e.1.time < b) (u : Point → ℝ)
    (hphi : IsKineticC112On u {p | p.time < b})
    (hc : ContinuousOn u {p | p.time ≤ b}) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ p, p.time ≤ b → |u p| ≤ M)
    (hop : ∀ p, p.time < b → forwardScalarOperator A.a u p = 0) :
    (∫ p, u p ∂stripExit hH hLE hlam hLam A H b (stripPoleFinite H e b hb)) = u e.1 := by
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
  exact hi.symm

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

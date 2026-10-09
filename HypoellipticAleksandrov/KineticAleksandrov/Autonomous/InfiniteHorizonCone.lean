module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonFullTest

/-! # The literal finite-speed cone for actual infinite-horizon exits -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- The actual infinite exit inherits the literal physical upper cone from finite exits. -/
theorem stripInfiniteExit_ae_cone
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤) :
    ∀ᵐ p ∂stripInfiniteExit hH hLE hlam hLam A H e,
      |p.position 0 - e.1.position 0| ≤ max |H.lo| |H.hi| * (p.time - e.1.time) := by
  apply stripInfiniteExit_ae_of_finite hH hLE hlam hLam A H e
  intro T ht
  exact (strip_cone_ae_of_realization hH hlam hLam A H _
    (stripEvolution_spec hH hLE hlam hLam A H) T (stripPoleFinite H e T ht)).1

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonGreen

/-! # Arbitrary almost-everywhere Green properties pass through actual horizon restrictions -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- An almost-everywhere property of all finite Green measures holds for their actual infinite
  limit. -/
theorem stripGreen_infinite_ae_of_finite
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤)
    (P : Point → Prop)
    (hP : ∀ T : ℝ, ∀ ht : e.1.time < T,
      ∀ᵐ p ∂stripGreen hH hLE hlam hLam A H T (stripPoleFinite H e T ht), P p) :
    ∀ᵐ p ∂stripGreen hH hLE hlam hLam A H ⊤ e, P p := by
  let t (n : ℕ) := e.1.time + (n : ℝ) + 1
  have ht (n : ℕ) : e.1.time < t n := by
    dsimp only [t]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hn (n : ℕ) : ∀ᵐ p ∂stripGreen hH hLE hlam hLam A H ⊤ e,
      p.time < t n → P p := by
    apply (ae_restrict_iff'
      (isOpen_lt continuous_time continuous_const).measurableSet).mp
    have hr := stripGreen_finite_restrict_infinite hH hLE hlam hLam A H e (t n) (ht n)
    exact hr ▸ hP (t n) (ht n)
  filter_upwards [ae_all_iff.mpr hn] with p hp
  obtain ⟨n, hn⟩ := exists_nat_gt (p.time - e.1.time)
  apply hp n
  dsimp only [t]
  linarith

/-- Actual infinite Green measure is strictly future supported inside the velocity interval. -/
theorem stripGreen_infinite_ae_future_carrier
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤) :
    ∀ᵐ p ∂stripGreen hH hLE hlam hLam A H ⊤ e,
      e.1.time < p.time ∧ p.velocity 0 ∈ H.carrier := by
  apply stripGreen_infinite_ae_of_finite hH hLE hlam hLam A H e
  intro T ht
  filter_upwards [reconstruction_green_ae_time_gt H
    (stripEvolution hH hLE hlam hLam A H).2 T (stripPoleFinite H e T ht),
    stripGreenOfKernel_ae_mem_stripPast H (stripEvolution hH hLE hlam hLam A H).2 T
      (stripPoleFinite H e T ht)] with p hp hq
  exact ⟨hp, hq.2⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

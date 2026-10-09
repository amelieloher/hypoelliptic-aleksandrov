module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitConeFinite
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripGreenHorizon

/-! # Physical finite-speed Green support for every finite or infinite horizon -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution

/-- Finite-horizon zero-set statements pass to the actual infinite-horizon Green measure. -/
theorem reconstruction_green_infinite_zero_of_finite
    (H : Interval) (E : StripEvolution H) (e : StripPole H ⊤)
    (B : Set Point) (hB : MeasurableSet B)
    (hz : ∀ T : ℝ, ∀ hT : e.1.time < T,
      stripGreenOfKernel H E.2 T ⟨e.1, WithTop.coe_lt_coe.mpr hT, e.2.2⟩ B = 0) :
    stripGreenOfKernel H E.2 ⊤ e B = 0 := by
  let t (n : ℕ) := e.1.time + (n : ℝ) + 1
  have ht (n : ℕ) : e.1.time < t n := by
    dsimp only [t]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hzero (n : ℕ) : stripGreenOfKernel H E.2 ⊤ e (B ∩ {p | p.time < t n}) = 0 := by
    have hh := hz (t n) (ht n)
    rw [stripGreenOfKernel_horizonRestriction, Measure.restrict_apply hB] at hh
    exact hh
  have hcover : B = ⋃ n : ℕ, B ∩ {p | p.time < t n} := by
    ext p
    constructor
    · intro hp
      obtain ⟨n, hn⟩ := exists_nat_gt (p.time - e.1.time)
      apply mem_iUnion.mpr
      refine ⟨n, hp, ?_⟩
      change p.time < t n
      dsimp only [t]
      linarith
    · intro hp
      rcases mem_iUnion.mp hp with ⟨n, hn⟩
      exact hn.1
  rw [hcover]
  apply le_antisymm _ bot_le
  exact (measure_iUnion_le _).trans (by simp [hzero])

/-- The actual Green measure has finite-speed support for every terminal horizon. -/
theorem strip_cone_of_realization
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : WithTop ℝ) (e : StripPole H T) :
    stripGreenOfKernel H E.2 T e
      {p | |p.position 0 - e.1.position 0| > max |H.lo| |H.hi| * (p.time - e.1.time)} = 0 := by
  cases T with
  | coe T => exact strip_cone_finite_of_realization hH hlam hLam A H E hE T e
  | top =>
    apply reconstruction_green_infinite_zero_of_finite H E e
    · exact isOpen_lt
        ((continuous_const.mul (continuous_time.sub continuous_const)))
        ((((continuous_apply 0).comp continuous_position).sub continuous_const).abs)
          |>.measurableSet
    · intro T hT
      exact strip_cone_finite_of_realization hH hlam hLam A H E hE T _

/-- The canonical Green measure obeys the same literal physical cone for every horizon. -/
theorem strip_cone
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (T : WithTop ℝ) (e : StripPole H T) :
    stripGreen hH hLE hlam hLam A H T e
      {p | |p.position 0 - e.1.position 0| > max |H.lo| |H.hi| * (p.time - e.1.time)} = 0 :=
  strip_cone_of_realization hH hlam hLam A H _
    (stripEvolution_spec hH hLE hlam hLam A H) T e

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

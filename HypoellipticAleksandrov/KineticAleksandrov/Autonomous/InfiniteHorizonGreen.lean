module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceLimitsInfinite
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitConeOneSign

/-! # The exact infinite-horizon Green supremum and inherited quadratic bound -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- Every infinite pole determines the same physical pole at any later finite terminal time. -/
def stripPoleFinite (H : Interval) (e : StripPole H ⊤) (T : ℝ) (hT : e.1.time < T) :
    StripPole H (T : WithTop ℝ) := ⟨e.1, WithTop.coe_lt_coe.mpr hT, e.2.2⟩

/-- Every finite terminal Green measure is the physical-time restriction of the infinite one. -/
theorem stripGreen_finite_restrict_infinite
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤)
    (T : ℝ) (hT : e.1.time < T) :
    stripGreen hH hLE hlam hLam A H T (stripPoleFinite H e T hT) =
      (stripGreen hH hLE hlam hLam A H ⊤ e).restrict {p | p.time < T} :=
  stripGreenOfKernel_horizonRestriction H _ T (stripPoleFinite H e T hT)

/-- The actual infinite Green measure is the supremum over all later finite terminal times. -/
theorem stripGreen_infinite_eq_iSup
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤) :
    stripGreen hH hLE hlam hLam A H ⊤ e =
      ⨆ (T : ℝ) (hT : e.1.time < T),
        stripGreen hH hLE hlam hLam A H T (stripPoleFinite H e T hT) := by
  apply le_antisymm
  · apply Measure.le_iff.mpr
    intro B hB
    let t (n : ℕ) : ℝ := e.1.time + (n : ℝ) + 1
    let U (n : ℕ) : Set Point := {p | p.time < t n}
    have ht (n : ℕ) : e.1.time < t n := by
      dsimp only [t]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have hm : Monotone (fun n => B ∩ U n) := by
      intro n m hnm p hp
      refine ⟨hp.1, ?_⟩
      have hn : (n : ℝ) ≤ m := Nat.cast_le.mpr hnm
      have hp' : p.time < e.1.time + (n : ℝ) + 1 := hp.2
      change p.time < e.1.time + (m : ℝ) + 1
      linarith
    have hun : (⋃ n, B ∩ U n) = B := by
      ext p
      constructor
      · intro hp
        obtain ⟨n, hn⟩ := mem_iUnion.mp hp
        exact hn.1
      · intro hp
        obtain ⟨n, hn⟩ := exists_nat_gt (p.time - e.1.time)
        apply mem_iUnion.mpr
        refine ⟨n, hp, ?_⟩
        change p.time < e.1.time + (n : ℝ) + 1
        linarith
    conv_lhs => rw [← hun, hm.measure_iUnion]
    apply iSup_le
    intro n
    have hr := stripGreen_finite_restrict_infinite hH hLE hlam hLam A H e (t n) (ht n)
    have heq := congrArg (fun μ : Measure Point => μ B) hr
    rw [Measure.restrict_apply hB] at heq
    rw [← heq]
    have hle : stripGreen hH hLE hlam hLam A H (t n)
        (stripPoleFinite H e (t n) (ht n)) ≤
          ⨆ (T : ℝ) (hT : e.1.time < T),
            stripGreen hH hLE hlam hLam A H T (stripPoleFinite H e T hT) :=
      le_iSup_of_le (t n) (le_iSup_of_le (ht n) le_rfl)
    exact Measure.le_iff.mp hle B hB
  · apply iSup_le
    intro T
    apply iSup_le
    intro hT
    rw [stripGreen_finite_restrict_infinite hH hLE hlam hLam A H e T hT]
    exact Measure.restrict_le_self

/-- The source's infinite-horizon characterization includes its exact uniform quadratic mass. -/
theorem stripGreen_infinite_characterization
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤) :
    stripGreen hH hLE hlam hLam A H ⊤ e =
      (⨆ (T : ℝ) (hT : e.1.time < T),
        stripGreen hH hLE hlam hLam A H T (stripPoleFinite H e T hT)) ∧
      stripGreen hH hLE hlam hLam A H ⊤ e univ ≤
        ENNReal.ofReal ((e.1.velocity 0 - H.lo) * (H.hi - e.1.velocity 0) / (2 * lam)) :=
  ⟨stripGreen_infinite_eq_iSup hH hLE hlam hLam A H e,
    stripGreen_quadratic_mass hH hLE hlam hLam A H ⊤ e⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripMassQuadratic
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripGreenHorizon

/-! # Infinite-horizon quadratic Green mass and its finite-horizon specialization -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open scoped ENNReal

/-- The quadratic barrier controls total Green mass even at the infinite horizon. -/
theorem stripGreenOfRealization_infinite_quadratic_mass
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (e : StripPole H ⊤) :
    stripGreenOfKernel H E.2 ⊤ e univ ≤
      ENNReal.ofReal ((e.1.velocity 0 - H.lo) * (H.hi - e.1.velocity 0) / (2 * lam)) := by
  let T (n : ℕ) : ℝ := e.1.time + (n : ℝ) + 1
  have ht (n : ℕ) : e.1.time < T n := by
    dsimp [T]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  let pole (n : ℕ) : StripPole H (T n : WithTop ℝ) :=
    ⟨e.1, WithTop.coe_lt_coe.mpr (ht n), e.2.2⟩
  let B (n : ℕ) : Set Point := {p | p.time < T n}
  have hm : Monotone B := by
    intro n m hnm p hp
    have hnm' : (n : ℝ) ≤ m := Nat.cast_le.mpr hnm
    change p.time < e.1.time + (m : ℝ) + 1
    change p.time < e.1.time + (n : ℝ) + 1 at hp
    linarith
  have hun : (⋃ n, B n) = univ := by
    apply eq_univ_of_forall
    intro p
    obtain ⟨n, hn⟩ := exists_nat_gt (p.time - e.1.time)
    apply mem_iUnion.mpr
    refine ⟨n, ?_⟩
    change p.time < e.1.time + (n : ℝ) + 1
    linarith
  rw [← hun, hm.measure_iUnion]
  apply iSup_le
  intro n
  have hh := stripGreenOfKernel_horizonRestriction H E.2 (T n) (pole n)
  have he : stripPoleInfinite H (T n) (pole n) = e := rfl
  rw [he] at hh
  have hm := congrArg (fun μ : Measure Point => μ univ) hh
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter] at hm
  rw [← hm]
  exact stripGreenOfRealization_quadratic_mass hH hlam hLam A H E hE (T n) (pole n)

/-- The canonical Green measure has the exact quadratic bound at every admitted horizon. -/
theorem stripGreen_quadratic_mass
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (T : WithTop ℝ)
    (e : StripPole H T) :
    stripGreen hH hLE hlam hLam A H T e univ ≤
      ENNReal.ofReal ((e.1.velocity 0 - H.lo) * (H.hi - e.1.velocity 0) / (2 * lam)) := by
  cases T with
  | top =>
    exact stripGreenOfRealization_infinite_quadratic_mass hH hlam hLam A H _
      (stripEvolution_spec hH hLE hlam hLam A H) e
  | coe t => exact stripGreen_finite_quadratic_mass hH hLE hlam hLam A H t e

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

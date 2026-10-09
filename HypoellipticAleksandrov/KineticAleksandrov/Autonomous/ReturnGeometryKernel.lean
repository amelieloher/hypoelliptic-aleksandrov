module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnTimeMeasure
import Mathlib.Tactic

/-! # Finite terminal measures for the canonical physical return-time action -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic Set MeasureTheory
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

/-- Every physical terminal measure, including the harmless negative-time extension, is finite. -/
instance instIsFiniteMeasureKphysical
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (t : ℝ) (z : Z) :
    IsFiniteMeasure (Kphysical hH hLE hlam hLam A t z) := by
  unfold Kphysical
  split
  · let : IsFiniteMeasure ((fullSpaceEvolution hH hLE hlam hLam A).2.master
        (wholeSpaceQuery 0 t ‹0 ≤ t› (physicalState z).2 (physicalState z).1)) :=
      ⟨((fullSpaceEvolution hH hLE hlam hLam A).2.mass_le_one _).trans_lt
        ENNReal.one_lt_top⟩
    infer_instance
  · infer_instance

/-- The action is exactly the integral against the physical terminal measure. -/
theorem S_eq_integral
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (t : ℝ) (ht : 0 ≤ t)
    (F : BoundedBorel Z) (z : Z) :
    S hH hLE hlam hLam A t F z = ∫ w, F w ∂Kphysical hH hLE hlam hLam A t z := by
  unfold S Kphysical
  rw [fullSpaceAction_eq_zeroTime A _ (fullSpaceEvolution_spec hH hLE hlam hLam A)
    _ _ ht, dite_eq_left ht,
    integral_map_of_stronglyMeasurable (by unfold scalarState; fun_prop)
      F.measurable.stronglyMeasurable]
  rfl

/-- The physical terminal kernel has total mass one at nonnegative elapsed times. -/
theorem Kphysical_mass_one
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (t : ℝ) (ht : 0 ≤ t) (z : Z) :
    Kphysical hH hLE hlam hLam A t z univ = 1 := by
  unfold Kphysical
  rw [dite_eq_left ht, Measure.map_apply (by unfold scalarState; fun_prop)
    MeasurableSet.univ, preimage_univ]
  exact fullspace_mass_one hlam A _ (fullSpaceEvolution_spec hH hLE hlam hLam A) _

/-- A smooth-test comparison for the actual semigroup extends to bounded Borel data. -/
theorem return_time_borel_of_smooth_tests
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (C : ℝ) (hC : 0 ≤ C) (A : SmoothAutonomous lam Lam)
    (t s : ℝ) (ht : 0 ≤ t) (hs : 0 ≤ s) (z : Z)
    (htest : ∀ F : BoundedBorel Z, (∀ w, 0 ≤ F w) →
      ContDiff ℝ (⊤ : ℕ∞) F →
      S hH hLE hlam hLam A t F z ≤ C * S hH hLE hlam hLam A s F z)
    (F : BoundedBorel Z) (hF : ∀ w, 0 ≤ F w) :
    S hH hLE hlam hLam A t F z ≤ C * S hH hLE hlam hLam A s F z := by
  rw [S_eq_integral hH hLE hlam hLam A t ht,
    S_eq_integral hH hLE hlam hLam A s hs]
  apply return_measure_comparison _ _ C hC ?_ F hF
  intro f hf hfc hfn
  obtain ⟨B, hB⟩ := hf.continuous.bounded_above_of_compact_support hfc
  let G : BoundedBorel Z := ⟨f, hf.continuous.measurable, max B 0,
    le_max_right _ _, fun w =>
      (show |f w| ≤ B by simpa only [Real.norm_eq_abs] using hB w).trans (le_max_left _ _)⟩
  simpa only [S_eq_integral hH hLE hlam hLam A t ht,
    S_eq_integral hH hLE hlam hLam A s hs] using htest G hfn hf

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

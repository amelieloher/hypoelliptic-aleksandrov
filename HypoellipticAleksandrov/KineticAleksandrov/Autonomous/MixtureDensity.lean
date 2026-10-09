module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.MixtureDensityTests
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.MixtureDensityTransport

/-! # The quantitative density bound for the actual enlarged Green mixture

Source: companion paper, Corollary 8.4. Constants precede the coefficient, clock and pole measure.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open MeasureTheory
open scoped ENNReal

/-- Integrating the actual one-pole Green family preserves its uniform Lq estimate. -/
theorem enlargedActiveGreen_density
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (q : ℝ) (hq : 1 < q) (hq2 : q < (3 : ℝ) / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock)
      (nu : Measure Point) [IsFiniteMeasure nu],
      ∃ g : Point → ℝ, Measurable g ∧ (∀ x, 0 ≤ g x) ∧
        enlargedActiveGreen hH hLE hlam hLam A c nu =
          volume.withDensity (fun x => ENNReal.ofReal (g x)) ∧
        MemLp g (ENNReal.ofReal q) volume ∧
        (eLpNorm g (ENNReal.ofReal q) volume).toReal ≤
          C * c.r ^ (6 / q - 4) * (nu Set.univ).toReal := by
  have hpq : q.HolderConjugate (q / (q - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hq).2 rfl
  obtain ⟨C, hC, ht⟩ :=
    mixture_density_conjugate_tests hH hLE hlam hLam q _ hpq hq2
  refine ⟨C, hC, ?_⟩
  intro A c nu _
  let mu := enlargedActiveGreen hH hLE hlam hLam A c nu
  have : IsFiniteMeasure mu := enlargedActiveGreen_isFiniteMeasure hH hLE hlam hLam A c nu
  apply mixture_point_density_of_tests mu q
    (C * c.r ^ (6 / q - 4) * (nu Set.univ).toReal) hq
    (mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg c.positive.le _))
      ENNReal.toReal_nonneg)
  intro f hfp hfn
  simpa only [mul_assoc, mul_comm, mul_left_comm] using ht A c nu f hfp hfn

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

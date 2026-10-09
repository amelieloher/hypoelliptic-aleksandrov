module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PoleDensityNorm

/-! # Uniform one-sign pole density of the actual physical infinite Green measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open scoped ENNReal NNReal

/-- The actual one-sign infinite physical Green measure has a nonnegative Lebesgue density
with the exact `r^(6/q-4)` norm bound. The constant is uniform in coefficient derivatives,
clock centres, radii and starting points. The analytic classical inputs remain explicit. -/
theorem one_sign_pole_density
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (q : ℝ) (hq : 1 < q) (hq2 : q < (3 : ℝ) / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point)
      (he : e.velocity 0 ∈ c.active), ∃ g : Point → ℝ,
      Measurable g ∧ (∀ p, 0 ≤ g p) ∧
      stripGreen hH hLE hlam hLam A c.activeInterval ⊤ ⟨e, WithTop.coe_lt_top _, he⟩ =
        volume.withDensity (fun p => ENNReal.ofReal (g p)) ∧
      eLpNorm g (ENNReal.ofReal q) volume ≤ ENNReal.ofReal (C * c.r ^ (6 / q - 4 : ℝ)) ∧
      (∀ᵐ p ∂stripGreen hH hLE hlam hLam A c.activeInterval ⊤
        ⟨e, WithTop.coe_lt_top _, he⟩, e.time < p.time ∧ p.velocity 0 ∈ c.active) := by
  obtain ⟨C, hC, hc⟩ := clockGreen_real_density hH hLE hlam hLam q hq hq2
  refine ⟨2 * C, by positivity, ?_⟩
  intro A c e he
  obtain ⟨F, hFm, hFn, hFd, hFN⟩ := hc A c e he
  exact ⟨polePhysicalDensity c e F, polePhysicalDensity_measurable c e F hFm,
    polePhysicalDensity_nonneg c e F hFn,
    clock_physical_green_density hH hLE hlam hLam A c e he F hFm hFn hFd,
    polePhysicalDensity_eLpNorm_bound c e F hFm hFn q C (by linarith) hC.le hFN,
    stripGreen_infinite_ae_future_carrier hH hLE hlam hLam A c.activeInterval
      ⟨e, WithTop.coe_lt_top _, he⟩⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

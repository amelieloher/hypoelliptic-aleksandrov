module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitConeStrict

/-! # Removing the strict speed margin from the actual transport cone -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Filter
open SectionTwo TheoremA Evolution
open scoped Topology

/-- A nonpositive transport direction gives closed-cone support for both actual measures. -/
theorem reconstruction_transport_cone_ae
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ))
    (alpha beta gamma : ℝ)
    (he : reconstructionConeCoordinate alpha beta gamma e.1 = 0)
    (hdir : ∀ v ∈ H.carrier, alpha + v * beta ≤ 0) :
    (∀ᵐ p ∂stripExitOfRealization hH hlam hLam A H E hE T e,
      reconstructionConeCoordinate alpha beta gamma p ≤ 0) ∧
    ∀ᵐ p ∂stripGreenOfKernel H E.2 T e, reconstructionConeCoordinate alpha beta gamma p ≤ 0 := by
  let r (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hr (n : ℕ) : 0 < r n := by dsimp only [r]; positivity
  have hn (n : ℕ) := reconstruction_strict_transport_cone_ae hH hlam hLam A H E hE T e
    (alpha - r n) beta (gamma + r n * e.1.time) (r n) (hr n)
    (by dsimp only [reconstructionConeCoordinate] at he ⊢; nlinarith)
    (fun v hv => by have hh := hdir v hv; linarith)
  have hlimit (μ : Measure Point)
      (ha : ∀ n, ∀ᵐ p ∂μ,
        reconstructionConeCoordinate (alpha - r n) beta (gamma + r n * e.1.time) p ≤ 0) :
      ∀ᵐ p ∂μ, reconstructionConeCoordinate alpha beta gamma p ≤ 0 := by
    have hall := ae_all_iff.mpr ha
    filter_upwards [hall] with p hp
    have hr0 : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have ht : Tendsto (fun n => reconstructionConeCoordinate alpha beta gamma p -
        r n * p.time + r n * e.1.time) atTop
        (𝓝 (reconstructionConeCoordinate alpha beta gamma p)) := by
      simpa only [zero_mul, sub_zero, add_zero] using
        (tendsto_const_nhds.sub (hr0.mul_const p.time)).add (hr0.mul_const e.1.time)
    have hρ : Tendsto (fun n => reconstructionConeCoordinate (alpha - r n) beta
        (gamma + r n * e.1.time) p) atTop
        (𝓝 (reconstructionConeCoordinate alpha beta gamma p)) := by
      apply ht.congr
      intro n
      dsimp only [reconstructionConeCoordinate]
      ring
    exact le_of_tendsto hρ (Filter.Eventually.of_forall hp)
  exact ⟨hlimit _ (fun n => (hn n).1), hlimit _ (fun n => (hn n).2)⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

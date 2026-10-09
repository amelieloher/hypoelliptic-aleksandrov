module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.WeakCompactFinite
public import HypoellipticAleksandrov.Ambient.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Bounded weak subsequences on open Euclidean sets

An equivalent finite measure reduces compactness to a separable Hilbert space.
The Radon--Nikodym derivative transfers all L1 tests back to the original measure.
In particular the open set need not have finite volume.
-/

@[expose] public section

open Filter MeasureTheory Topology

namespace HypoellipticAleksandrov.KineticAleksandrov

/-- Uniformly bounded measurable functions for a sigma-finite measure on a
countably generated measurable space have a subsequence converging against all L1 tests. -/
theorem exists_sigmaFinite_bounded_weak_subsequence
    {α : Type*} [MeasurableSpace α] [MeasurableSpace.CountablyGenerated α]
    (μ : Measure α) [SigmaFinite μ]
    (v : ℕ → α → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hv : ∀ j, AEStronglyMeasurable (v j) μ)
    (hb : ∀ j, ∀ᵐ x ∂μ, |v j x| ≤ C) :
    ∃ (u : α → ℝ) (ν : ℕ → ℕ), StrictMono ν ∧ AEStronglyMeasurable u μ ∧
      (∀ᵐ x ∂μ, |u x| ≤ C) ∧
      ∀ ψ : α → ℝ, Integrable ψ μ →
        Tendsto (fun j => ∫ x, v (ν j) x * ψ x ∂μ)
          atTop (nhds (∫ x, u x * ψ x ∂μ)) := by
  obtain ⟨ρ, hρ, hμρ, hρμ⟩ := exists_isFiniteMeasure_absolutelyContinuous μ
  let : IsFiniteMeasure ρ := hρ
  obtain ⟨u, ν, hν, hu, hub, ht⟩ := exists_finite_bounded_weak_subsequence ρ v C hC
    (fun j => (hv j).mono_ac hρμ) (fun j => hρμ.ae_le (hb j))
  refine ⟨u, ν, hν, hu.mono_ac hμρ, hμρ.ae_le hub, ?_⟩
  intro ψ hψ
  have hmeasure : ρ.withDensity (μ.rnDeriv ρ) = μ := by
    have h := Measure.rnDeriv_add_singularPart μ ρ
    simpa only [Measure.singularPart_eq_zero_of_ac hμρ, add_zero] using h
  let Ψ (x : α) := (μ.rnDeriv ρ x).toReal * ψ x
  have hΨ : Integrable Ψ ρ := by
    have h := (integrable_withDensity_iff_integrable_smul'
      (Measure.measurable_rnDeriv μ ρ) (Measure.rnDeriv_lt_top μ ρ)).mp
      (hmeasure.symm ▸ hψ)
    simpa only [smul_eq_mul] using h
  have he (f : α → ℝ) : (∫ x, f x * ψ x ∂μ) = ∫ x, f x * Ψ x ∂ρ := by
    rw [← hmeasure, integral_withDensity_eq_integral_toReal_smul
      (Measure.measurable_rnDeriv μ ρ) (Measure.rnDeriv_lt_top μ ρ)]
    congr 1
    funext x
    dsimp only [Ψ]
    simp only [smul_eq_mul]
    ring
  simpa only [← he] using ht Ψ hΨ

/-- On any open Euclidean set, a uniformly bounded measurable sequence admits
a bounded measurable limit and a subsequence converging against every integrable test. -/
theorem exists_bounded_weak_subsequence
    {N : ℕ} (U : Set (PDE.Vec N)) (hU : IsOpen U)
    (v : ℕ → PDE.Vec N → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hv : ∀ j, AEStronglyMeasurable (v j) (volume.restrict U))
    (hb : ∀ j, ∀ᵐ x ∂volume.restrict U, |v j x| ≤ C) :
    ∃ (u : PDE.Vec N → ℝ) (ν : ℕ → ℕ),
      StrictMono ν ∧ AEStronglyMeasurable u (volume.restrict U) ∧
      (∀ᵐ x ∂volume.restrict U, |u x| ≤ C) ∧
      ∀ ψ : PDE.Vec N → ℝ, IntegrableOn ψ U volume →
        Tendsto (fun j => ∫ x in U, v (ν j) x * ψ x)
          atTop (nhds (∫ x in U, u x * ψ x)) := by
  exact exists_sigmaFinite_bounded_weak_subsequence (volume.restrict U) v C hC hv hb

end HypoellipticAleksandrov.KineticAleksandrov

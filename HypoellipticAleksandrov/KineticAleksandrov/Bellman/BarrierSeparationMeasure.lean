module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.BarrierSeparationFunctional
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Tactic

/-! # Riesz representation of the normalized positive separator -/

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace HypoellipticAleksandrov.KineticAleksandrov

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]

/-- A normalized positive continuous functional has a probability representing it. -/
theorem exists_bellman_functional_probability (L : C(X, ℝ) →L[ℝ] ℝ)
    (h1 : L 1 = 1) (hpos : ∀ f : C(X, ℝ), (∀ x, 0 ≤ f x) → 0 ≤ L f) :
    ∃ mu : Measure X, IsProbabilityMeasure mu ∧
      ∀ f : C(X, ℝ), ∫ x, f x ∂mu = L f := by
  let ell : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
    { toFun := fun f => L f.toContinuousMap
      map_add' := fun f g => by
        change L (f.toContinuousMap + g.toContinuousMap) = _
        exact map_add L _ _
      map_smul' := fun c f => by
        change L (c • f.toContinuousMap) = _
        exact map_smul L _ _
      monotone' := fun f g hfg => by
        have hp := hpos (g.toContinuousMap - f.toContinuousMap)
          (fun x => sub_nonneg.mpr (hfg x))
        rw [map_sub] at hp
        exact sub_nonneg.mp hp }
  let mu := RealRMK.rieszMeasure ell
  have ht (f : C(X, ℝ)) : ∫ x, f x ∂mu = L f := by
    let fc : C_c(X, ℝ) := ⟨f, HasCompactSupport.of_compactSpace f⟩
    exact RealRMK.integral_rieszMeasure ell fc
  have hmass : mu.real univ = 1 := by
    simpa only [ContinuousMap.one_apply, integral_const, smul_eq_mul, mul_one] using (ht 1).trans h1
  exact ⟨mu, isProbabilityMeasure_iff_real.mpr hmass, ht⟩

/-- A continuous subspace avoiding strict positivity has an annihilating probability. -/
theorem exists_bellman_subspace_probability (S : Submodule ℝ C(X, ℝ))
    (hno : Disjoint (bellmanPositiveCone (X := X)) (S : Set C(X, ℝ))) :
    ∃ mu : Measure X, IsProbabilityMeasure mu ∧
      ∀ f ∈ S, ∫ x, f x ∂mu = 0 := by
  obtain ⟨L, h1, hpos, hS⟩ := exists_bellman_positive_functional S hno
  obtain ⟨mu, hmu, ht⟩ := exists_bellman_functional_probability L h1 hpos
  exact ⟨mu, hmu, fun f hf => (ht f).trans (hS f hf)⟩

end HypoellipticAleksandrov.KineticAleksandrov

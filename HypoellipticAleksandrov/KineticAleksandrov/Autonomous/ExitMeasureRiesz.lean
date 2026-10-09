module

public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.MeasureTheory.Integral.CompactlySupported
public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Topology.Metrizable.Basic

/-! # Unique subprobability representation of a positive boundary functional

This measure-theoretic step takes a positive contraction functional, rather than an
uncharacterized measure. The functional's PDE construction is separate from this module.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open MeasureTheory Set TopologicalSpace
open scoped CompactlySupported ENNReal

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [PseudoMetrizableSpace X] [MeasurableSpace X] [BorelSpace X]

omit [SecondCountableTopology X] [PseudoMetrizableSpace X] in
/-- A positive contraction functional has a Riesz measure of total mass at most one. -/
theorem boundaryFunctional_rieszMeasure_mass (ℓ : C_c(X, ℝ) →ₚ[ℝ] ℝ)
    (hbd : ∀ (f : C_c(X, ℝ)) (c : ℝ), 0 ≤ c → (∀ x, |f x| ≤ c) → |ℓ f| ≤ c) :
    RealRMK.rieszMeasure ℓ univ ≤ 1 := by
  have hreg := RealRMK.regular_rieszMeasure ℓ
  rw [(MeasureTheory.Measure.Regular.innerRegular).measure_eq_iSup isOpen_univ]
  refine iSup_le fun K => iSup_le fun _ => iSup_le fun hKc => ?_
  obtain ⟨f, hf1, hfc, -, hf01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hKc isOpen_univ (subset_univ K)
  let g : C_c(X, ℝ) := ⟨f, hfc⟩
  have hg : ∀ x, 0 ≤ g x := fun x => (hf01 x).1
  refine (RealRMK.rieszMeasure_le_of_eq_one ℓ hg hKc fun x hx => hf1 hx).trans ?_
  have hb := hbd g 1 zero_le_one fun x => by
    rw [abs_of_nonneg (hg x)]
    exact (hf01 x).2
  calc ENNReal.ofReal (ℓ g) ≤ ENNReal.ofReal 1 :=
      ENNReal.ofReal_le_ofReal (le_of_abs_le hb)
    _ = 1 := ENNReal.ofReal_one

/-- Full compact-test characterization determines exactly one subprobability measure. -/
theorem existsUnique_boundaryFunctional_measure (ℓ : C_c(X, ℝ) →ₚ[ℝ] ℝ)
    (hbd : ∀ (f : C_c(X, ℝ)) (c : ℝ), 0 ≤ c → (∀ x, |f x| ≤ c) → |ℓ f| ≤ c) :
    ∃! μ : Measure X, μ univ ≤ 1 ∧ ∀ f : C_c(X, ℝ), ∫ x, f x ∂μ = ℓ f := by
  refine ⟨RealRMK.rieszMeasure ℓ,
    ⟨boundaryFunctional_rieszMeasure_mass ℓ hbd,
      fun f => RealRMK.integral_rieszMeasure ℓ f⟩,
    ?_⟩
  intro μ hμ
  let : IsFiniteMeasure μ := ⟨hμ.1.trans_lt (by simp)⟩
  exact Measure.ext_of_integral_eq_on_compactlySupported fun f => by
    rw [hμ.2 f, RealRMK.integral_rieszMeasure]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

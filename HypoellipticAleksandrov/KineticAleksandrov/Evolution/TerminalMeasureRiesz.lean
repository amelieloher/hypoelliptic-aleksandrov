module

public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.MeasureTheory.Integral.CompactlySupported
public import Mathlib.Topology.UrysohnsLemma
public import HypoellipticAleksandrov.KineticAleksandrov.MovingKernel

/-!
# The Riesz measure of a sup-norm bounded positive functional on an open fiber

Outside-context measure theory for On the open subtype `U` of the Euclidean ambient
state, a positive functional `ℓ` on `C_c(U, ℝ)` bounded by the sup norm has a Riesz measure of
total mass at most one.  Its push-forward to the ambient state is supported on `U`.  A
subprobability measure whose integrals against `C_c(U, ℝ)` are the values of `ℓ` is the Riesz
measure (regularity on the second countable locally compact space `U`).
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov MeasureTheory Set
open scoped CompactlySupported ENNReal

section Fiber

variable {n : ℕ} {U : Set (EvolutionAmbientState n)} [LocallyCompactSpace U]

/-- The Riesz measure of a sup-norm bounded positive functional has mass at most one. -/
theorem rieszMeasure_univ_le_one (ℓ : C_c(U, ℝ) →ₚ[ℝ] ℝ)
    (hbd : ∀ (f : C_c(U, ℝ)) (c : ℝ), 0 ≤ c → (∀ x, |f x| ≤ c) → |ℓ f| ≤ c) :
    RealRMK.rieszMeasure ℓ univ ≤ 1 := by
  have hreg := RealRMK.regular_rieszMeasure ℓ
  rw [(MeasureTheory.Measure.Regular.innerRegular).measure_eq_iSup isOpen_univ]
  refine iSup_le fun K => iSup_le fun _ => iSup_le fun hKc => ?_
  obtain ⟨f, hf1, hfc, -, hf01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hKc isOpen_univ (subset_univ K)
  let g : C_c(U, ℝ) := ⟨f, hfc⟩
  have hg : ∀ x, 0 ≤ g x := fun x => (hf01 x).1
  refine (RealRMK.rieszMeasure_le_of_eq_one ℓ hg hKc fun x hx => hf1 hx).trans ?_
  have hb := hbd g 1 zero_le_one fun x => by
    rw [abs_of_nonneg (hg x)]; exact (hf01 x).2
  calc ENNReal.ofReal (ℓ g) ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal (le_of_abs_le hb)
    _ = 1 := ENNReal.ofReal_one

/-- A subprobability measure with the integrals of the Riesz functional is the Riesz measure. -/
theorem eq_rieszMeasure_of_integral_eq (ℓ : C_c(U, ℝ) →ₚ[ℝ] ℝ)
    (μ' : Measure U) [IsFiniteMeasure μ'] (hint : ∀ f : C_c(U, ℝ), ∫ x, f x ∂μ' = ℓ f) :
    μ' = RealRMK.rieszMeasure ℓ :=
  Measure.ext_of_integral_eq_on_compactlySupported fun f => by
    rw [hint f, RealRMK.integral_rieszMeasure]

end Fiber

end HypoellipticAleksandrov.KineticAleksandrov

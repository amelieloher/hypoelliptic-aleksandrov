module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ViscosityWeakLimit
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.WeakCompactL1
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitMeasure
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Order.Lattice

/-!
# Local inequalities inherited by a bounded weak limit

Finite-volume indicator tests pass upper bounds to the weak limit. Continuity
of its smooth representative turns the resulting almost-everywhere inequalities
into pointwise inequalities on open sets.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov Set Filter MeasureTheory Evolution
open scoped Topology

private theorem weak_limit_le_on_finite_set {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (v : ℕ → α → ℝ) (u : α → ℝ) (C a : ℝ)
    (hv : ∀ j, AEStronglyMeasurable (v j) μ)
    (hb : ∀ j, ∀ᵐ x ∂μ, |v j x| ≤ C)
    (hu : AEStronglyMeasurable u μ) (hub : ∀ᵐ x ∂μ, |u x| ≤ C)
    (hlim : ∀ ψ : α → ℝ, Integrable ψ μ →
      Tendsto (fun j => ∫ x, v j x * ψ x ∂μ) atTop (𝓝 (∫ x, u x * ψ x ∂μ)))
    (E : Set α) (hE : MeasurableSet E) (hEf : μ E < ⊤)
    (hle : ∀ j, ∀ x ∈ E, v j x ≤ a) :
    ∀ᵐ x ∂μ.restrict E, u x ≤ a := by
  let : IsFiniteMeasure (μ.restrict E) := ⟨by simpa using hEf⟩
  have hui : Integrable u (μ.restrict E) := by
    apply (integrable_const C).mono hu.restrict
    filter_upwards [ae_restrict_of_ae hub] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg ((abs_nonneg _).trans hx)] using hx
  refine ae_le_of_forall_setIntegral_le hui (integrable_const a) ?_
  intro S hS _
  have hSE : MeasurableSet (S ∩ E) := hS.inter hE
  have hSEf : μ (S ∩ E) ≠ ⊤ := ne_of_lt ((measure_mono inter_subset_right).trans_lt hEf)
  let ψ : α → ℝ := (S ∩ E).indicator (fun _ => 1)
  have hψ : Integrable ψ μ := (integrable_indicator_iff hSE).2 (integrableOn_const hSEf)
  have hid (f : α → ℝ) : (∫ x, f x * ψ x ∂μ) = ∫ x in S ∩ E, f x ∂μ := by
    have heq : (fun x => f x * ψ x) = (S ∩ E).indicator f := by
      funext x
      by_cases hx : x ∈ S ∩ E <;> simp [ψ, hx]
    rw [heq, integral_indicator hSE]
  have ht := hlim ψ hψ
  simp only [hid] at ht
  have hineq : ∀ j, (∫ x in S ∩ E, v j x ∂μ) ≤ ∫ x in S ∩ E, a ∂μ := by
    intro j
    have hi : IntegrableOn (v j) (S ∩ E) μ := by
      apply (show Integrable (fun _ : α => C) (μ.restrict (S ∩ E)) from
        integrableOn_const hSEf).mono (hv j).restrict
      filter_upwards [ae_restrict_of_ae (hb j)] with x hx
      simpa only [Real.norm_eq_abs, abs_of_nonneg ((abs_nonneg _).trans hx)] using hx
    apply integral_mono_ae hi (integrableOn_const hSEf)
    filter_upwards [ae_restrict_mem hSE] with x hx
    exact hle j x hx.2
  have hh := le_of_tendsto ht (Filter.Eventually.of_forall hineq)
  simpa only [Measure.restrict_restrict hS] using hh

/-- The existing kinetic volume assigns positive mass to every nonempty open set. -/
instance kineticVolume_isOpenPosMeasure (n : ℕ) :
    Measure.IsOpenPosMeasure (volume : Measure (KineticPoint n)) := by
  change Measure.IsOpenPosMeasure
    (Measure.map (KineticPoint.equivProd n).symm volume)
  exact (KineticPoint.homeomorphProd n).symm.continuous.isOpenPosMeasure_map
    (KineticPoint.equivProd n).symm.surjective

/-- A smooth representative inherits every uniform upper bound on an open subregion. -/
theorem bounded_weak_limit_le_on_open {n : ℕ}
    (U W : Set (KineticPoint n)) (hW : IsOpen W) (hWU : W ⊆ U)
    (v : ℕ → KineticPoint n → ℝ) (u V : KineticPoint n → ℝ) (C a : ℝ)
    (hv : ∀ j, AEStronglyMeasurable (v j) (volume.restrict U))
    (hb : ∀ j, ∀ᵐ x ∂volume.restrict U, |v j x| ≤ C)
    (hu : AEStronglyMeasurable u (volume.restrict U))
    (hub : ∀ᵐ x ∂volume.restrict U, |u x| ≤ C)
    (hlim : ∀ ψ : KineticPoint n → ℝ, IntegrableOn ψ U volume →
      Tendsto (fun j => ∫ x in U, v j x * ψ x) atTop (𝓝 (∫ x in U, u x * ψ x)))
    (hV : ContinuousOn V U) (hrep : u =ᵐ[volume.restrict U] V)
    (hle : ∀ j, ∀ x ∈ W, v j x ≤ a) : ∀ x ∈ W, V x ≤ a := by
  intro x hx
  obtain ⟨E, hEx, hEf⟩ := (volume : Measure (KineticPoint n)).finiteAt_nhds x
  obtain ⟨O, hOE, hO, hxO⟩ := mem_nhds_iff.mp (inter_mem hEx (hW.mem_nhds hx))
  have hOU : O ⊆ U := (fun p hp => hWU (hOE hp).2)
  have hOW : O ⊆ W := fun p hp => (hOE hp).2
  have hOf : (volume.restrict U) O < ⊤ := by
    rw [Measure.restrict_apply hO.measurableSet, inter_eq_left.mpr hOU]
    exact (measure_mono (fun p hp => (hOE hp).1)).trans_lt hEf
  have hweak := weak_limit_le_on_finite_set (volume.restrict U) v u C a hv hb hu hub
    hlim O hO.measurableSet hOf (fun j p hp => hle j p (hOW hp))
  have hrestrict : (volume.restrict U).restrict O = volume.restrict O := by
    rw [Measure.restrict_restrict hO.measurableSet, inter_eq_left.mpr hOU]
  have hleV : ∀ᵐ p ∂volume.restrict O, V p ≤ a := by
    rw [← hrestrict]
    filter_upwards [hweak, ae_restrict_of_ae hrep] with p hp he
    rwa [← he]
  have hae : V =ᵐ[volume.restrict O] fun p => min (V p) a := by
    filter_upwards [hleV] with p hp
    exact (min_eq_left hp).symm
  have hcV := hV.mono hOU
  have heq := Measure.eqOn_open_of_ae_eq hae hO hcV (hcV.inf continuousOn_const)
  rw [heq hxO]
  exact min_le_right _ _

/-- Uniform local absolute trace bounds pass to the continuous weak-limit representative. -/
theorem bounded_weak_limit_abs_sub_le_on_open {n : ℕ}
    (U W : Set (KineticPoint n)) (hW : IsOpen W) (hWU : W ⊆ U)
    (v : ℕ → KineticPoint n → ℝ) (u V : KineticPoint n → ℝ) (C a η : ℝ)
    (hv : ∀ j, AEStronglyMeasurable (v j) (volume.restrict U))
    (hb : ∀ j, ∀ᵐ x ∂volume.restrict U, |v j x| ≤ C)
    (hu : AEStronglyMeasurable u (volume.restrict U))
    (hub : ∀ᵐ x ∂volume.restrict U, |u x| ≤ C)
    (hlim : ∀ ψ : KineticPoint n → ℝ, IntegrableOn ψ U volume →
      Tendsto (fun j => ∫ x in U, v j x * ψ x) atTop (𝓝 (∫ x in U, u x * ψ x)))
    (hV : ContinuousOn V U) (hrep : u =ᵐ[volume.restrict U] V)
    (hbound : ∀ j, ∀ x ∈ W, |v j x - a| ≤ η) :
    ∀ x ∈ W, |V x - a| ≤ η := by
  have hupp := bounded_weak_limit_le_on_open U W hW hWU v u V C (a + η)
    hv hb hu hub hlim hV hrep (fun j x hx => by
      have h := (abs_le.mp (hbound j x hx)).2
      linarith)
  have hlimneg : ∀ ψ : KineticPoint n → ℝ, IntegrableOn ψ U volume →
      Tendsto (fun j => ∫ x in U, (-v j x) * ψ x)
        atTop (𝓝 (∫ x in U, (-u x) * ψ x)) := by
    intro ψ hψ
    simpa only [neg_mul, integral_neg] using (hlim ψ hψ).neg
  have hneg := bounded_weak_limit_le_on_open U W hW hWU (fun j x => -v j x)
    (fun x => -u x) (fun x => -V x) C (η - a) (fun j => (hv j).neg)
    (fun j => by simpa only [abs_neg] using hb j) hu.neg
    (by simpa only [abs_neg] using hub) hlimneg hV.neg
    (by filter_upwards [hrep] with x hx; simp only [hx])
    (fun j x hx => by have h := (abs_le.mp (hbound j x hx)).1; linarith)
  intro x hx
  exact abs_le.mpr ⟨by linarith [hneg x hx], by linarith [hupp x hx]⟩

end HypoellipticAleksandrov.KineticAleksandrov

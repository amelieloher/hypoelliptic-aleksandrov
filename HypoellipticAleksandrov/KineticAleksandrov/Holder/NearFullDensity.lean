module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullCutoffAffine
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometryTopology
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Tactic

/-! # Finite cylinder volume and the density defect in the near-full argument -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set MeasureTheory

/-- Every compact set in physical kinetic coordinates has finite native volume. -/
theorem kinetic_volume_compact_lt_top {d : ℕ} {K : Set (KineticPoint d)}
    (hK : IsCompact K) : volume K < ⊤ := by
  let e := KineticPoint.homeomorphProd d
  have hc := hK.image e.continuous
  have heq := (KineticPoint.measurePreserving_equivProd d).measure_preimage
    hc.measurableSet.nullMeasurableSet
  have hpre : (KineticPoint.equivProd d) ⁻¹' (e '' K) = K := by
    ext P
    exact (KineticPoint.equivProd d).injective.mem_set_image
  rw [hpre] at heq
  rw [heq]
  exact hc.measure_lt_top

/-- Positive-radius backward cylinders have finite native volume. -/
theorem volume_backwardCylinder_lt_top {d : ℕ} (P₀ : KineticPoint d)
    {R : ℝ} (hR : 0 < R) : volume (backwardCylinder P₀ R) < ⊤ :=
  (measure_mono subset_closure).trans_lt
    (kinetic_volume_compact_lt_top (isCompact_closure_backwardCylinder P₀ R hR))

/-- The density hypothesis bounds the volume of the strict sublevel set. -/
theorem near_full_sublevel_volume {d : ℕ} {O : Set (KineticPoint d)}
    (hO : IsOpen O) {u : KineticPoint d → ℝ} (hu : ContinuousOn u O)
    (P₀ : KineticPoint d) {R : ℝ} (hR : 0 < R)
    (hQO : backwardCylinder P₀ R ⊆ O) (ell eta : ℝ)
    (hdensity : (1 - eta) * (volume (backwardCylinder P₀ R)).toReal ≤
      (volume ({P | ell ≤ u P} ∩ backwardCylinder P₀ R)).toReal) :
    (volume ({P | u P < ell} ∩ backwardCylinder P₀ R)).toReal ≤
      eta * (volume (backwardCylinder P₀ R)).toReal := by
  let Q := backwardCylinder P₀ R
  let E := {P | u P < ell} ∩ Q
  have hE : MeasurableSet E := by
    have ho : IsOpen ((O ∩ u ⁻¹' Iio ell) ∩ Q) :=
      (hu.isOpen_inter_preimage hO isOpen_Iio).inter
      (isOpen_backwardCylinder P₀ R hR)
    have heq : E = (O ∩ u ⁻¹' Iio ell) ∩ Q := by
      ext P
      change (u P < ell ∧ P ∈ Q) ↔ ((P ∈ O ∧ u P < ell) ∧ P ∈ Q)
      exact ⟨fun h => ⟨⟨hQO h.2, h.1⟩, h.2⟩, fun h => ⟨h.1.2, h.2⟩⟩
    rw [heq]
    exact ho.measurableSet
  have hdiff : Q \ E = {P | ell ≤ u P} ∩ Q := by
    ext P
    simp only [E, mem_sdiff, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨hP, h⟩
      exact ⟨le_of_not_gt (fun ht => h ⟨ht, hP⟩), hP⟩
    · rintro ⟨huP, hP⟩
      exact ⟨hP, fun h => (not_lt_of_ge huP) h.1⟩
  have hsum := measureReal_inter_add_sdiff (μ := volume) (s := Q) hE
    (volume_backwardCylinder_lt_top P₀ hR).ne
  have hQE : Q ∩ E = E := inter_eq_right.mpr inter_subset_right
  rw [hQE, hdiff] at hsum
  change (volume E).toReal ≤ eta * (volume Q).toReal
  change (volume E).toReal + (volume ({P | ell ≤ u P} ∩ Q)).toReal =
    (volume Q).toReal at hsum
  linarith

end HypoellipticAleksandrov.KineticAleksandrov.Holder

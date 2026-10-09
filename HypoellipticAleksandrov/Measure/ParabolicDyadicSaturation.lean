module

public import HypoellipticAleksandrov.Measure.ParabolicDyadicOpenCover
public import HypoellipticAleksandrov.Measure.ParabolicDyadicInkSpotsBridge

/-!
# Parabolic dyadic saturation of the first ink-spots union

This file proves the measure part of the crawling-of-ink-spots lemma for the
actual clipped first enlargement union.  The proof separates the root cell
from the first-entry cover and performs the resulting countable sum in
extended nonnegative reals.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/-- The non-root dyadic cells which first enter the actual source D1 union. -/
def parabolicDyadicD1Entry {d : Nat} (Gamma : Set (TimeVelocity d)) (xi : Real) :
    Set (ParabolicDyadicAddress d) :=
  parabolicDyadicFirstEntry (inkSpotsD1 Gamma xi)

private theorem parabolicDyadicD1_subset_unit
    (d : Nat) (Gamma : Set (TimeVelocity d)) (xi : Real) :
    inkSpotsD1 Gamma xi ⊆ inkSpotsUnitBox d := by
  intro z hz
  simp only [inkSpotsD1, Set.mem_iUnion] at hz
  obtain ⟨q, hqDense, hzq⟩ := hz
  exact hzq.2

private theorem parabolicDyadicRoot_openCell_eq_inkSpotsUnitBox (d : Nat) :
    parabolicDyadicOpenCell (fun i => Fin.elim0 i : ParabolicDyadicIndex d 0) =
      inkSpotsUnitBox d := by
  ext z
  rcases z with ⟨time, velocity⟩
  rw [mem_parabolicDyadicOpenCell_iff, inkSpotsUnitBox, mem_parabolicBox_iff,
    mem_velocityCube_iff]
  simp [parabolicDyadicTimeCode, parabolicDyadicVelocityCode, abs_lt]
  intro _ _
  constructor <;> intro hvelocity <;> intro coordinate
  · exact ⟨(hvelocity coordinate).1, by linarith [(hvelocity coordinate).2]⟩
  · exact ⟨(hvelocity coordinate).1, by linarith [(hvelocity coordinate).2]⟩

private theorem volume_inkSpotsUnitBox_ne_top (d : Nat) :
    volume (inkSpotsUnitBox d) ≠ ∞ := by
  intro htop
  have hformula : (volume (inkSpotsUnitBox d)).toReal =
      ((1 : Real) * 1 ^ 2) * (2 * 1) ^ d := by
    simpa only [inkSpotsUnitBox] using
      (volume_parabolicBox_toReal (d := d) (vartheta := (1 : Real)) (r := (1 : Real))
        (t₀ := (0 : Real)) (v₀ := (0 : PDE.Vec d)) (by norm_num) (by norm_num))
  rw [htop] at hformula
  norm_num at hformula
  exact (ne_of_gt (pow_pos (by norm_num : (0 : Real) < 2) d)) hformula.symm

private theorem parabolicDyadicD1Entry_openCell_subset
    {d : Nat} (Gamma : Set (TimeVelocity d)) (xi : Real)
    (a : {a : ParabolicDyadicAddress d // a ∈ parabolicDyadicD1Entry Gamma xi}) :
    parabolicDyadicOpenCell a.1.2 ⊆ inkSpotsD1 Gamma xi := by
  rcases a with ⟨⟨n, index⟩, ha⟩
  cases n with
  | zero => exact False.elim ha
  | succ n => exact ha.1

private theorem parabolicDyadicD1_entry_density_le
    {d : Nat} (Gamma : Set (TimeVelocity d)) (xi : Real)
    (a : {a : ParabolicDyadicAddress d // a ∈ parabolicDyadicD1Entry Gamma xi}) :
    (volume (Gamma ∩ parabolicDyadicOpenCell a.1.2)).toReal ≤
      xi * (volume (parabolicDyadicOpenCell a.1.2)).toReal := by
  rcases a with ⟨⟨n, index⟩, ha⟩
  cases n with
  | zero => exact False.elim ha
  | succ n =>
      change parabolicDyadicOpenCell index ⊆ inkSpotsD1 Gamma xi ∧
        ¬ parabolicDyadicOpenCell (parabolicDyadicParent index) ⊆ inkSpotsD1 Gamma xi at ha
      by_contra hle
      have hstrict : xi * (volume (parabolicDyadicOpenCell index)).toReal <
          (volume (Gamma ∩ parabolicDyadicOpenCell index)).toReal :=
        lt_of_not_ge hle
      exact ha.2
        (parabolicDyadicOpenCell_parent_subset_inkSpotsD1_of_density_gt Gamma xi index hstrict)

theorem volume_Gamma_le_xi_volume_inkSpotsD1
    (d : Nat) (Gamma : Set (TimeVelocity d)) (xi : Real)
    (hGamma : MeasurableSet Gamma) (hGammaUnit : Gamma ⊆ inkSpotsUnitBox d)
    (hxi : xi ∈ Set.Ioo (0 : Real) 1)
    (hsubcritical : (volume Gamma).toReal <
      xi * (volume (inkSpotsUnitBox d)).toReal) :
    Gamma ≤ᵐ[volume] inkSpotsD1 Gamma xi ∧
      (volume Gamma).toReal ≤ xi * (volume (inkSpotsD1 Gamma xi)).toReal := by
  let U : Set (TimeVelocity d) := inkSpotsD1 Gamma xi
  let root : ParabolicDyadicIndex d 0 := fun i => Fin.elim0 i
  have hGammaAE : Gamma ≤ᵐ[volume] U := by
    simpa only [U] using
      (ae_le_inkSpotsD1_of_parabolicDyadicDensity d Gamma xi hGamma hGammaUnit hxi)
  have hUUnit : U ⊆ inkSpotsUnitBox d := by
    simpa only [U] using parabolicDyadicD1_subset_unit d Gamma xi
  have hrootEq : parabolicDyadicOpenCell root = inkSpotsUnitBox d := by
    simpa only [root] using parabolicDyadicRoot_openCell_eq_inkSpotsUnitBox d
  have hURoot : U ⊆ parabolicDyadicOpenCell root := by
    rw [hrootEq]
    exact hUUnit
  refine ⟨by simpa only [U] using hGammaAE, ?_⟩
  by_cases hroot : parabolicDyadicOpenCell root ⊆ U
  · have hUeq : U = inkSpotsUnitBox d := by
      apply Set.Subset.antisymm hUUnit
      rw [← hrootEq]
      exact hroot
    simpa only [U, hUeq] using hsubcritical.le
  · let E := {a : ParabolicDyadicAddress d | a ∈ parabolicDyadicD1Entry Gamma xi}
    let C : E → Set (TimeVelocity d) := fun a => parabolicDyadicOpenCell a.1.2
    let V : Set (TimeVelocity d) := ⋃ a : E, C a
    have hV : V = ⋃ a ∈ parabolicDyadicD1Entry Gamma xi,
        parabolicDyadicOpenCell a.2 := by
      change (⋃ a : {a : ParabolicDyadicAddress d //
        a ∈ parabolicDyadicD1Entry Gamma xi}, parabolicDyadicOpenCell a.1.2) = _
      rw [Set.iUnion_subtype]
    have hcover : U =ᵐ[volume] V := by
      rw [hV]
      simpa only [U, parabolicDyadicD1Entry] using
        (ae_eq_iUnion_parabolicDyadicFirstEntry_openCell d U
          (isOpen_inkSpotsD1 Gamma xi) hURoot hroot)
    have hdisjointC : Pairwise (Function.onFun Disjoint C) := by
      intro a b hab
      simp only [C]
      apply pairwiseDisjoint_parabolicDyadicFirstEntry_openCell U
      · exact a.2
      · exact b.2
      · exact Subtype.coe_ne_coe.mpr hab
    have hmeasC : ∀ a : E, MeasurableSet (C a) := by
      intro a
      exact measurableSet_parabolicDyadicOpenCell a.1.2
    have hdisjointGammaC : Pairwise (Function.onFun Disjoint fun a : E => Gamma ∩ C a) := by
      intro a b hab
      exact (hdisjointC hab).mono inter_subset_right inter_subset_right
    have hmeasGammaC : ∀ a : E, MeasurableSet (Gamma ∩ C a) := by
      intro a
      exact hGamma.inter (hmeasC a)
    have hunit_ne_top : volume (inkSpotsUnitBox d) ≠ ∞ :=
      volume_inkSpotsUnitBox_ne_top d
    have hU_ne_top : volume U ≠ ∞ :=
      measure_ne_top_of_subset hUUnit hunit_ne_top
    have hGamma_ne_top : volume Gamma ≠ ∞ :=
      measure_ne_top_of_subset hGammaUnit hunit_ne_top
    have hC_ne_top : ∀ a : E, volume (C a) ≠ ∞ := by
      intro a
      apply measure_ne_top_of_subset
      exact (parabolicDyadicD1Entry_openCell_subset Gamma xi a).trans hUUnit
      exact hunit_ne_top
    have hGammaC_ne_top : ∀ a : E, volume (Gamma ∩ C a) ≠ ∞ := by
      intro a
      exact measure_ne_top_of_subset inter_subset_right (hC_ne_top a)
    let xie : ℝ≥0∞ := ENNReal.ofReal xi
    have hlocal : ∀ a : E, volume (Gamma ∩ C a) ≤ xie * volume (C a) := by
      intro a
      apply (ENNReal.toReal_le_toReal (hGammaC_ne_top a)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hC_ne_top a))).mp
      simpa only [xie, ENNReal.toReal_mul, ENNReal.toReal_ofReal hxi.1.le] using
        (parabolicDyadicD1_entry_density_le Gamma xi a)
    have hGammaAEInter : Gamma =ᵐ[volume] (Gamma ∩ U : Set (TimeVelocity d)) := by
      filter_upwards [hGammaAE] with z hz
      apply propext
      constructor
      · intro hzGamma
        exact ⟨hzGamma, hz hzGamma⟩
      · exact fun hzGamma => hzGamma.1
    have hGammaInterCover : (Gamma ∩ U : Set (TimeVelocity d)) =ᵐ[volume]
        (Gamma ∩ V : Set (TimeVelocity d)) :=
      ae_eq_set_inter (EventuallyEq.rfl) hcover
    have hGammaV : Gamma ∩ V = ⋃ a : E, Gamma ∩ C a := by
      simp only [V, inter_iUnion]
    have hmeasure : volume Gamma ≤ xie * volume U := by
      calc
        volume Gamma = volume (Gamma ∩ U) := measure_congr hGammaAEInter
        _ = volume (Gamma ∩ V) := measure_congr hGammaInterCover
        _ = volume (⋃ a : E, Gamma ∩ C a) := by rw [hGammaV]
        _ = ∑' a : E, volume (Gamma ∩ C a) :=
          measure_iUnion hdisjointGammaC hmeasGammaC
        _ ≤ ∑' a : E, xie * volume (C a) := ENNReal.tsum_le_tsum hlocal
        _ = xie * ∑' a : E, volume (C a) := ENNReal.tsum_mul_left
        _ = xie * volume V := by rw [← measure_iUnion hdisjointC hmeasC]
        _ = xie * volume U := by rw [measure_congr hcover]
    have hxieU_ne_top : xie * volume U ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hU_ne_top
    have hreal := ENNReal.toReal_mono hxieU_ne_top hmeasure
    simpa only [U, xie, ENNReal.toReal_mul, ENNReal.toReal_ofReal hxi.1.le] using hreal

end

end HypoellipticAleksandrov.Parabolic

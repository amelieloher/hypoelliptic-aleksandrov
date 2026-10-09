module

public import HypoellipticAleksandrov.Measure.ParabolicDyadicAddress
public import HypoellipticAleksandrov.Measure.ParabolicDensity
public import HypoellipticAleksandrov.Measure.InkSpotsGeometry

/-!
# Dyadic source boxes for parabolic ink spots

This module identifies each open parabolic dyadic cell with a concrete
ink-spots source box.  It also records the ambient/subtype measure bridges
needed to pass the dyadic density theorem to the source family.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/-- The source box whose open interior is an addressed parabolic dyadic cell.
Its radius is the positive real expression `2⁻¹ ^ n`, its base time is the
lower endpoint of the time cell, and its centre is the coordinate midpoint. -/
def parabolicDyadicSourceBox {d n : Nat}
    (index : ParabolicDyadicIndex d n) : InkSpotsBox d where
  radius := ((2 : ℝ) ^ n)⁻¹
  baseTime := (parabolicDyadicTimeCode n index : ℝ) / (4 : ℝ) ^ n
  center := fun coordinate =>
    -1 + 2 * (parabolicDyadicVelocityCode n index coordinate : ℝ) /
      (2 : ℝ) ^ n + ((2 : ℝ) ^ n)⁻¹

private theorem parabolicDyadicSourceBox_radius_sq {d n : Nat}
    (index : ParabolicDyadicIndex d n) :
    (parabolicDyadicSourceBox index).radius ^ 2 = ((4 : ℝ) ^ n)⁻¹ := by
  change ((2 : ℝ) ^ n)⁻¹ ^ 2 = ((4 : ℝ) ^ n)⁻¹
  rw [inv_pow, ← pow_mul, Nat.mul_comm, pow_mul]
  norm_num

private theorem parabolicDyadicSourceBox_time_upper {d n : Nat}
    (index : ParabolicDyadicIndex d n) :
    (parabolicDyadicSourceBox index).baseTime +
        (parabolicDyadicSourceBox index).radius ^ 2 =
      (parabolicDyadicTimeCode n index + 1 : ℝ) / (4 : ℝ) ^ n := by
  rw [parabolicDyadicSourceBox_radius_sq]
  change (parabolicDyadicTimeCode n index : ℝ) / (4 : ℝ) ^ n +
      ((4 : ℝ) ^ n)⁻¹ = _
  field_simp

private theorem parabolicDyadicSourceBox_center_sub_radius {d n : Nat}
    (index : ParabolicDyadicIndex d n) (coordinate : Fin d) :
    (parabolicDyadicSourceBox index).center coordinate -
        (parabolicDyadicSourceBox index).radius =
      -1 + 2 * (parabolicDyadicVelocityCode n index coordinate : ℝ) /
        (2 : ℝ) ^ n := by
  change -1 + 2 * (parabolicDyadicVelocityCode n index coordinate : ℝ) /
      (2 : ℝ) ^ n + ((2 : ℝ) ^ n)⁻¹ - ((2 : ℝ) ^ n)⁻¹ = _
  ring

private theorem parabolicDyadicSourceBox_center_add_radius {d n : Nat}
    (index : ParabolicDyadicIndex d n) (coordinate : Fin d) :
    (parabolicDyadicSourceBox index).center coordinate +
        (parabolicDyadicSourceBox index).radius =
      -1 + 2 * (parabolicDyadicVelocityCode n index coordinate + 1 : ℝ) /
        (2 : ℝ) ^ n := by
  change -1 + 2 * (parabolicDyadicVelocityCode n index coordinate : ℝ) /
      (2 : ℝ) ^ n + ((2 : ℝ) ^ n)⁻¹ + ((2 : ℝ) ^ n)⁻¹ = _
  field_simp
  ring

/-- The source open box is exactly the addressed open dyadic cell. -/
theorem inkSpotsSourceBox_parabolicDyadicSourceBox {d n : Nat}
    (index : ParabolicDyadicIndex d n) :
    inkSpotsSourceBox (parabolicDyadicSourceBox index) = parabolicDyadicOpenCell index := by
  ext z
  rcases z with ⟨time, velocity⟩
  rw [mem_inkSpotsSourceBox_iff, mem_parabolicDyadicOpenCell_iff,
    mem_velocityCube_iff]
  rw [parabolicDyadicSourceBox_time_upper]
  constructor
  · rintro ⟨htlower, htupper, hvelocity⟩
    refine ⟨htlower, htupper, fun coordinate => ?_⟩
    have hcoordinate := hvelocity coordinate
    rw [abs_lt] at hcoordinate
    have hlow := parabolicDyadicSourceBox_center_sub_radius index coordinate
    have hupp := parabolicDyadicSourceBox_center_add_radius index coordinate
    constructor
    · nlinarith [hcoordinate.1, hlow]
    · nlinarith [hcoordinate.2, hupp]
  · rintro ⟨htlower, htupper, hvelocity⟩
    refine ⟨htlower, htupper, fun coordinate => ?_⟩
    rw [abs_lt]
    have hcoordinate := hvelocity coordinate
    have hlow := parabolicDyadicSourceBox_center_sub_radius index coordinate
    have hupp := parabolicDyadicSourceBox_center_add_radius index coordinate
    constructor
    · nlinarith [hcoordinate.1, hlow]
    · nlinarith [hcoordinate.2, hupp]

/-- Every dyadic source box has positive radius. -/
theorem parabolicDyadicSourceBox_radius_pos {d n : Nat}
    (index : ParabolicDyadicIndex d n) :
    0 < (parabolicDyadicSourceBox index).radius := by
  change 0 < ((2 : ℝ) ^ n)⁻¹
  positivity

private theorem parabolicDyadicOpenCell_subset_unit {d n : Nat}
    (index : ParabolicDyadicIndex d n) :
    parabolicDyadicOpenCell index ⊆ inkSpotsUnitBox d := by
  rintro ⟨time, velocity⟩ hcell
  rw [mem_parabolicDyadicOpenCell_iff] at hcell
  rw [inkSpotsUnitBox, mem_parabolicBox_iff]
  have hfour : 0 < (4 : ℝ) ^ n := pow_pos (by norm_num) _
  have htwo : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) _
  have htimeCode : (parabolicDyadicTimeCode n index : ℝ) < (4 : ℝ) ^ n := by
    exact_mod_cast parabolicDyadicTimeCode_lt_pow index
  refine ⟨?_, ?_, ?_⟩
  · have : 0 ≤ (parabolicDyadicTimeCode n index : ℝ) := by positivity
    nlinarith [div_nonneg this hfour.le]
  · have hupper :
        (parabolicDyadicTimeCode n index + 1 : ℝ) / (4 : ℝ) ^ n ≤ 1 := by
      have hcodeNat : parabolicDyadicTimeCode n index + 1 ≤ 4 ^ n :=
        Nat.succ_le_iff.mpr (parabolicDyadicTimeCode_lt_pow index)
      have hcodeReal : (parabolicDyadicTimeCode n index + 1 : ℝ) ≤
          (4 : ℝ) ^ n := by exact_mod_cast hcodeNat
      exact (div_le_one hfour).mpr hcodeReal
    nlinarith
  · intro coordinate
    have hvelocityCode :
        (parabolicDyadicVelocityCode n index coordinate : ℝ) < (2 : ℝ) ^ n := by
      exact_mod_cast parabolicDyadicVelocityCode_lt_pow index coordinate
    simp only [Pi.zero_apply, sub_zero]
    have hlower : -1 < velocity coordinate := by
      have : -1 ≤ -1 + 2 *
          (parabolicDyadicVelocityCode n index coordinate : ℝ) / (2 : ℝ) ^ n := by
        have : 0 ≤ 2 * (parabolicDyadicVelocityCode n index coordinate : ℝ) /
            (2 : ℝ) ^ n := by positivity
        linarith
      exact lt_of_le_of_lt this (hcell.2.2 coordinate).1
    have hupper : velocity coordinate < 1 := by
      have hcode : (parabolicDyadicVelocityCode n index coordinate + 1 : ℝ) ≤
          (2 : ℝ) ^ n := by
        have hcodeNat : parabolicDyadicVelocityCode n index coordinate + 1 ≤ 2 ^ n :=
          Nat.succ_le_iff.mpr (parabolicDyadicVelocityCode_lt_pow index coordinate)
        exact_mod_cast hcodeNat
      have hbound : -1 + 2 *
          (parabolicDyadicVelocityCode n index coordinate + 1 : ℝ) /
            (2 : ℝ) ^ n ≤ 1 := by
        have hfrac : (parabolicDyadicVelocityCode n index coordinate + 1 : ℝ) /
            (2 : ℝ) ^ n ≤ 1 := (div_le_one htwo).mpr hcode
        calc
          -1 + 2 * (parabolicDyadicVelocityCode n index coordinate + 1 : ℝ) /
              (2 : ℝ) ^ n =
              -1 + 2 * ((parabolicDyadicVelocityCode n index coordinate + 1 : ℝ) /
                (2 : ℝ) ^ n) := by ring
          _ ≤ 1 := by linarith
      exact lt_of_lt_of_le (hcell.2.2 coordinate).2 hbound
    exact abs_lt.mpr (by constructor <;> linarith)

/-- The source box of an addressed cell lies in the open unit source box. -/
theorem inkSpotsSourceBox_parabolicDyadicSourceBox_subset_unit {d n : Nat}
    (index : ParabolicDyadicIndex d n) :
    inkSpotsSourceBox (parabolicDyadicSourceBox index) ⊆ inkSpotsUnitBox d := by
  rw [inkSpotsSourceBox_parabolicDyadicSourceBox]
  exact parabolicDyadicOpenCell_subset_unit index

/-- The first enlargement of a child source box contains the entire open
parent cell.  The time computation uses the four child digits and the
velocity computation uses the two digits in each coordinate. -/
theorem parabolicDyadicOpenCell_parent_subset_inkSpotsQ1 {d n : Nat}
    (index : ParabolicDyadicIndex d (n + 1)) :
    parabolicDyadicOpenCell (parabolicDyadicParent index) ⊆
      inkSpotsQ1 (parabolicDyadicSourceBox index) := by
  rintro ⟨time, velocity⟩ hz
  rw [mem_parabolicDyadicOpenCell_iff] at hz
  rw [mem_inkSpotsQ1_iff]
  have htimeCode : parabolicDyadicTimeCode (n + 1) index =
      4 * parabolicDyadicTimeCode n (parabolicDyadicParent index) +
        (index (Fin.last n)).1.val := by
    simp only [parabolicDyadicTimeCode]
  have htimeBase : (parabolicDyadicSourceBox index).baseTime =
      (parabolicDyadicTimeCode n (parabolicDyadicParent index) : ℝ) / (4 : ℝ) ^ n +
        (index (Fin.last n)).1.val * (((4 : ℝ) ^ n)⁻¹ / 4) := by
    change (parabolicDyadicTimeCode (n + 1) index : ℝ) / (4 : ℝ) ^ (n + 1) = _
    rw [htimeCode]
    push_cast
    rw [pow_succ]
    field_simp
  have hradiusSq : (parabolicDyadicSourceBox index).radius ^ 2 =
      ((4 : ℝ) ^ n)⁻¹ / 4 := by
    rw [parabolicDyadicSourceBox_radius_sq]
    rw [pow_succ]
    field_simp
  have htimeDigitLower : 0 ≤ (index (Fin.last n)).1.val := Nat.zero_le _
  have htimeDigitUpper : (index (Fin.last n)).1.val ≤ 3 := by
    exact Nat.le_pred_of_lt (index (Fin.last n)).1.isLt
  have hfour : 0 < (4 : ℝ) ^ n := pow_pos (by norm_num) _
  have hinv : 0 < ((4 : ℝ) ^ n)⁻¹ := inv_pos.mpr hfour
  have hzUnit : (time, velocity) ∈ inkSpotsUnitBox d :=
    parabolicDyadicOpenCell_subset_unit (parabolicDyadicParent index)
      (mem_parabolicDyadicOpenCell_iff.mpr hz)
  refine ⟨?_, ?_, ?_, hzUnit⟩
  · have hstart :
        (parabolicDyadicSourceBox index).baseTime -
            3 * (parabolicDyadicSourceBox index).radius ^ 2 ≤
          (parabolicDyadicTimeCode n (parabolicDyadicParent index) : ℝ) /
            (4 : ℝ) ^ n := by
      rw [htimeBase, hradiusSq]
      simp only [div_eq_mul_inv]
      have hdigit : ((index (Fin.last n)).1.val : ℝ) ≤ 3 := by
        exact_mod_cast htimeDigitUpper
      have hmul := mul_le_mul_of_nonneg_right hdigit hinv.le
      nlinarith
    exact lt_of_le_of_lt hstart hz.1
  · have hupp :
        (parabolicDyadicTimeCode n (parabolicDyadicParent index) + 1 : ℝ) /
            (4 : ℝ) ^ n ≤
          (parabolicDyadicSourceBox index).baseTime -
              3 * (parabolicDyadicSourceBox index).radius ^ 2 +
            (7 / 9 : ℝ) * (3 * (parabolicDyadicSourceBox index).radius) ^ 2 := by
      rw [htimeBase]
      simp only [div_eq_mul_inv]
      have hdigit : 0 ≤ ((index (Fin.last n)).1.val : ℝ) := by positivity
      have hmul : 0 ≤ ((index (Fin.last n)).1.val : ℝ) * ((4 : ℝ) ^ n)⁻¹ :=
        mul_nonneg hdigit hinv.le
      have hradiusSq' := hradiusSq
      simp only [div_eq_mul_inv] at hradiusSq'
      nlinarith [hradiusSq']
    exact lt_of_lt_of_le hz.2.1 hupp
  · rw [mem_velocityCube_iff]
    intro coordinate
    have hvelocityCode : parabolicDyadicVelocityCode (n + 1) index coordinate =
        2 * parabolicDyadicVelocityCode n (parabolicDyadicParent index) coordinate +
          ((index (Fin.last n)).2 coordinate).val := by
      simp only [parabolicDyadicVelocityCode]
    have hcenterLower : (parabolicDyadicSourceBox index).center coordinate -
        3 * (parabolicDyadicSourceBox index).radius =
      -1 + 2 * (parabolicDyadicVelocityCode n (parabolicDyadicParent index) coordinate : ℝ) /
          (2 : ℝ) ^ n +
        (((index (Fin.last n)).2 coordinate).val - 1) / (2 : ℝ) ^ n := by
      change -1 + 2 * (parabolicDyadicVelocityCode (n + 1) index coordinate : ℝ) /
          (2 : ℝ) ^ (n + 1) + ((2 : ℝ) ^ (n + 1))⁻¹ -
          3 * ((2 : ℝ) ^ (n + 1))⁻¹ = _
      rw [hvelocityCode]
      push_cast
      rw [pow_succ]
      field_simp
      ring
    have hcenterUpper : (parabolicDyadicSourceBox index).center coordinate +
        3 * (parabolicDyadicSourceBox index).radius =
      -1 + 2 * (parabolicDyadicVelocityCode n (parabolicDyadicParent index) coordinate : ℝ) /
          (2 : ℝ) ^ n +
        (((index (Fin.last n)).2 coordinate).val + 2) / (2 : ℝ) ^ n := by
      change -1 + 2 * (parabolicDyadicVelocityCode (n + 1) index coordinate : ℝ) /
          (2 : ℝ) ^ (n + 1) + ((2 : ℝ) ^ (n + 1))⁻¹ +
          3 * ((2 : ℝ) ^ (n + 1))⁻¹ = _
      rw [hvelocityCode]
      push_cast
      rw [pow_succ]
      field_simp
      ring
    rw [abs_lt]
    have hvelocityDigitLower : 0 ≤ ((index (Fin.last n)).2 coordinate).val := Nat.zero_le _
    have hvelocityDigitUpper : ((index (Fin.last n)).2 coordinate).val ≤ 1 := by
      exact Nat.le_pred_of_lt ((index (Fin.last n)).2 coordinate).isLt
    have hdenom : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) _
    have hinv : 0 < ((2 : ℝ) ^ n)⁻¹ := inv_pos.mpr hdenom
    have hparent := hz.2.2 coordinate
    have hlower :
        (parabolicDyadicSourceBox index).center coordinate -
            3 * (parabolicDyadicSourceBox index).radius ≤
          -1 + 2 *
            (parabolicDyadicVelocityCode n (parabolicDyadicParent index) coordinate : ℝ) /
              (2 : ℝ) ^ n := by
      rw [hcenterLower]
      have hdigit : (((index (Fin.last n)).2 coordinate).val : ℝ) ≤ 1 := by
        exact_mod_cast hvelocityDigitUpper
      have hdelta := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hdigit) hdenom.le
      linarith
    have hupper :
        -1 + 2 *
            (parabolicDyadicVelocityCode n (parabolicDyadicParent index) coordinate + 1 : ℝ) /
              (2 : ℝ) ^ n ≤
          (parabolicDyadicSourceBox index).center coordinate +
            3 * (parabolicDyadicSourceBox index).radius := by
      have hdigit : 0 ≤ (((index (Fin.last n)).2 coordinate).val : ℝ) := by positivity
      have hfrac : 2 / (2 : ℝ) ^ n ≤
          ((((index (Fin.last n)).2 coordinate).val : ℝ) + 2) / (2 : ℝ) ^ n :=
        (div_le_div_iff_of_pos_right hdenom).mpr (by linarith)
      calc
        -1 + 2 *
            (parabolicDyadicVelocityCode n (parabolicDyadicParent index) coordinate + 1 : ℝ) /
              (2 : ℝ) ^ n =
            -1 + 2 *
                (parabolicDyadicVelocityCode n (parabolicDyadicParent index) coordinate : ℝ) /
                  (2 : ℝ) ^ n + 2 / (2 : ℝ) ^ n := by ring
        _ ≤ -1 + 2 *
                (parabolicDyadicVelocityCode n (parabolicDyadicParent index) coordinate : ℝ) /
                  (2 : ℝ) ^ n +
              ((((index (Fin.last n)).2 coordinate).val : ℝ) + 2) / (2 : ℝ) ^ n := by
            linarith
        _ = (parabolicDyadicSourceBox index).center coordinate +
              3 * (parabolicDyadicSourceBox index).radius := hcenterUpper.symm
    constructor
    · nlinarith [hparent.1, hlower]
    · nlinarith [hparent.2, hupper]

/-- Subtype reference measure of an ambient measurable preimage is ambient
volume intersected with the reference cell. -/
theorem parabolicDyadicReferenceMeasure_preimage_eq_volume_inter_reference
    (d : Nat) (s : Set (TimeVelocity d)) (_hs : MeasurableSet s) :
    parabolicDyadicReferenceMeasure d (Subtype.val ⁻¹' s) =
      volume (s ∩ parabolicDyadicReferenceCell d) := by
  rw [parabolicDyadicReferenceMeasure, comap_subtype_coe_apply
    (measurableSet_parabolicDyadicReferenceCell d)]
  change volume (Subtype.val '' (Subtype.val ⁻¹' s)) = _
  rw [Subtype.image_preimage_coe, inter_comm]

/-- On a set inside the reference cell, subtype reference measure is ambient volume. -/
theorem parabolicDyadicReferenceMeasure_preimage_eq_volume {d : Nat}
    (s : Set (TimeVelocity d)) (hs : MeasurableSet s)
    (hsub : s ⊆ parabolicDyadicReferenceCell d) :
    parabolicDyadicReferenceMeasure d (Subtype.val ⁻¹' s) = volume s := by
  rw [parabolicDyadicReferenceMeasure_preimage_eq_volume_inter_reference d s hs,
    inter_eq_left.mpr hsub]

/-- The open source unit box and the half-open dyadic reference cell agree
almost everywhere for ambient product Lebesgue volume. -/
theorem inkSpotsUnitBox_ae_eq_parabolicDyadicReferenceCell (d : Nat) :
    inkSpotsUnitBox d =ᵐ[volume] parabolicDyadicReferenceCell d := by
  unfold inkSpotsUnitBox parabolicBox parabolicDyadicReferenceCell
  simp only [zero_add, one_mul, one_pow]
  rw [velocityCube_eq_pi, volume_timeVelocity_eq_prod]
  apply Measure.set_prod_ae_eq Ioo_ae_eq_Ioc
  simpa only [Pi.zero_apply, zero_sub, zero_add, MeasureTheory.volume_pi] using
    (Measure.pi_Ioo_ae_eq_pi_Ioc
      (μ := fun _ : Fin d => (volume : Measure ℝ))
      (s := Set.univ) (f := fun _ => (-1 : ℝ)) (g := fun _ => (1 : ℝ)))

private def parabolicDyadicAllBoundary (d : Nat) : Set (TimeVelocity d) :=
  ⋃ address : ParabolicDyadicAddress d,
    parabolicDyadicHalfOpenCell address.2 \ parabolicDyadicOpenCell address.2

private theorem volume_parabolicDyadicAllBoundary_eq_zero (d : Nat) :
    volume (parabolicDyadicAllBoundary d) = 0 := by
  apply measure_iUnion_null
  intro address
  apply ae_le_set.mp
  exact (parabolicDyadicOpenCell_ae_eq_halfOpenCell address.2).symm.le

private theorem ae_not_mem_parabolicDyadicAllBoundary (d : Nat) :
    ∀ᵐ z ∂volume, z ∉ parabolicDyadicAllBoundary d := by
  rw [ae_iff]
  simpa only [Set.setOf_mem_eq, not_not] using
    volume_parabolicDyadicAllBoundary_eq_zero d

/-- A strict dyadic density on a restricted half-open cell gives a strict
ink-spots density for its actual open source box. -/
theorem inkSpotsStrictDense_of_restrictedCell_density_gt {d n : Nat}
    (Gamma : Set (TimeVelocity d)) (hGamma : MeasurableSet Gamma) (xi : Real)
    (index : ParabolicDyadicIndex d n)
    (h : xi * (parabolicDyadicReferenceMeasure d).real
        (parabolicDyadicRestrictedCell index) <
      (parabolicDyadicReferenceMeasure d).real
        (parabolicDyadicRestrictedCell index ∩ Subtype.val ⁻¹' Gamma)) :
    inkSpotsStrictDense Gamma xi (parabolicDyadicSourceBox index) := by
  have hrestrictedInter :
      parabolicDyadicRestrictedCell index ∩ Subtype.val ⁻¹' Gamma =
        Subtype.val ⁻¹' (parabolicDyadicHalfOpenCell index ∩ Gamma) := by
    ext z
    rfl
  have hhalf : xi * (volume (parabolicDyadicHalfOpenCell index)).toReal <
      (volume (parabolicDyadicHalfOpenCell index ∩ Gamma)).toReal := by
    simpa only [Measure.real, hrestrictedInter,
      parabolicDyadicReferenceMeasure_restrictedCell,
      parabolicDyadicReferenceMeasure_preimage_eq_volume
        _ ((measurableSet_parabolicDyadicHalfOpenCell index).inter hGamma)
        (inter_subset_left.trans (parabolicDyadicHalfOpenCell_subset_reference index))] using h
  have hcellAE : parabolicDyadicOpenCell index =ᵐ[volume]
      parabolicDyadicHalfOpenCell index :=
    parabolicDyadicOpenCell_ae_eq_halfOpenCell index
  have hinterAE : (parabolicDyadicOpenCell index ∩ Gamma : Set (TimeVelocity d)) =ᵐ[volume]
      (parabolicDyadicHalfOpenCell index ∩ Gamma : Set (TimeVelocity d)) :=
    ae_eq_set_inter hcellAE (EventuallyEq.rfl)
  have hvolume : volume (parabolicDyadicOpenCell index) =
      volume (parabolicDyadicHalfOpenCell index) := measure_congr hcellAE
  have hvolumeInter : volume (parabolicDyadicOpenCell index ∩ Gamma) =
      volume (parabolicDyadicHalfOpenCell index ∩ Gamma) := measure_congr hinterAE
  refine ⟨parabolicDyadicSourceBox_radius_pos index,
    inkSpotsSourceBox_parabolicDyadicSourceBox_subset_unit index, ?_⟩
  rw [inkSpotsSourceBox_parabolicDyadicSourceBox]
  calc
    xi * (volume (parabolicDyadicOpenCell index)).toReal =
        xi * (volume (parabolicDyadicHalfOpenCell index)).toReal := by rw [hvolume]
    _ < (volume (parabolicDyadicHalfOpenCell index ∩ Gamma)).toReal := hhalf
    _ = (volume (parabolicDyadicOpenCell index ∩ Gamma)).toReal := by rw [hvolumeInter]

/-- A strict ambient density on a child open dyadic cell puts its parent open
cell in the actual first ink-spots enlargement union. -/
theorem parabolicDyadicOpenCell_parent_subset_inkSpotsD1_of_density_gt
    {d n : Nat} (Gamma : Set (TimeVelocity d)) (xi : Real)
    (index : ParabolicDyadicIndex d (n + 1))
    (h : xi * (volume (parabolicDyadicOpenCell index)).toReal <
      (volume (Gamma ∩ parabolicDyadicOpenCell index)).toReal) :
    parabolicDyadicOpenCell (parabolicDyadicParent index) ⊆ inkSpotsD1 Gamma xi := by
  have hstrict : inkSpotsStrictDense Gamma xi (parabolicDyadicSourceBox index) := by
    refine ⟨parabolicDyadicSourceBox_radius_pos index,
      inkSpotsSourceBox_parabolicDyadicSourceBox_subset_unit index, ?_⟩
    rw [inkSpotsSourceBox_parabolicDyadicSourceBox]
    simpa only [inter_comm] using h
  intro z hz
  refine Set.mem_iUnion.mpr ⟨parabolicDyadicSourceBox index, ?_⟩
  refine Set.mem_iUnion.mpr ⟨hstrict, ?_⟩
  exact parabolicDyadicOpenCell_parent_subset_inkSpotsQ1 index hz

private theorem inkSpotsUnitBox_subset_parabolicDyadicReferenceCell (d : Nat) :
    inkSpotsUnitBox d ⊆ parabolicDyadicReferenceCell d := by
  rintro ⟨time, velocity⟩ hz
  rw [inkSpotsUnitBox, mem_parabolicBox_iff] at hz
  simp only [zero_add, one_mul, one_pow] at hz
  rw [parabolicDyadicReferenceCell]
  refine ⟨⟨hz.1, hz.2.1.le⟩, fun coordinate _ => ?_⟩
  have hcoordinate := hz.2.2 coordinate
  rw [abs_lt, Pi.zero_apply, sub_zero] at hcoordinate
  exact ⟨hcoordinate.1, hcoordinate.2.le⟩

/-- Almost every point of a measurable set in the unit source box belongs to
the first ink-spots enlargement union. -/
theorem ae_le_inkSpotsD1_of_parabolicDyadicDensity
    (d : Nat) (Gamma : Set (TimeVelocity d)) (xi : Real)
    (hGamma : MeasurableSet Gamma) (hGammaUnit : Gamma ⊆ inkSpotsUnitBox d)
    (hxi : xi ∈ Set.Ioo (0 : Real) 1) :
    Gamma ≤ᵐ[volume] inkSpotsD1 Gamma xi := by
  let GammaRef : Set (ParabolicDyadicReferenceSpace d) := Subtype.val ⁻¹' Gamma
  have hGammaRef : MeasurableSet GammaRef := hGamma.preimage continuous_subtype_val.measurable
  have hGammaReference : Gamma ⊆ parabolicDyadicReferenceCell d :=
    hGammaUnit.trans (inkSpotsUnitBox_subset_parabolicDyadicReferenceCell d)
  have hsubtype := ae_exists_parabolicDyadicRestrictedCell_density_gt
    d GammaRef hGammaRef xi hxi
  have hrestrict : ∀ᵐ z ∂volume.restrict (parabolicDyadicReferenceCell d),
      z ∈ Gamma → ∃ n, ∃ index : ParabolicDyadicIndex d n,
        z ∈ parabolicDyadicHalfOpenCell index ∧
          xi * (parabolicDyadicReferenceMeasure d).real
              (parabolicDyadicRestrictedCell index) <
            (parabolicDyadicReferenceMeasure d).real
              (parabolicDyadicRestrictedCell index ∩ Subtype.val ⁻¹' Gamma) := by
    rw [ae_restrict_iff_subtype (measurableSet_parabolicDyadicReferenceCell d)]
    simpa only [GammaRef, parabolicDyadicReferenceMeasure,
      parabolicDyadicRestrictedCell, Set.mem_preimage] using hsubtype
  have hambient : ∀ᵐ z ∂volume,
      z ∈ parabolicDyadicReferenceCell d → z ∈ Gamma →
        ∃ n, ∃ index : ParabolicDyadicIndex d n,
          z ∈ parabolicDyadicHalfOpenCell index ∧
            xi * (parabolicDyadicReferenceMeasure d).real
                (parabolicDyadicRestrictedCell index) <
              (parabolicDyadicReferenceMeasure d).real
                (parabolicDyadicRestrictedCell index ∩ Subtype.val ⁻¹' Gamma) := by
    exact (ae_restrict_iff' (measurableSet_parabolicDyadicReferenceCell d)).mp hrestrict
  filter_upwards [hambient, ae_not_mem_parabolicDyadicAllBoundary d] with z hz hzBoundary
  intro hzGamma
  obtain ⟨n, index, hzHalf, hdensity⟩ := hz (hGammaReference hzGamma) hzGamma
  have hzOpen : z ∈ parabolicDyadicOpenCell index := by
    by_contra hzOpen
    apply hzBoundary
    refine Set.mem_iUnion.mpr ⟨⟨n, index⟩, ?_⟩
    exact ⟨hzHalf, hzOpen⟩
  have hstrict := inkSpotsStrictDense_of_restrictedCell_density_gt
    Gamma hGamma xi index hdensity
  have hzSource : z ∈ inkSpotsSourceBox (parabolicDyadicSourceBox index) := by
    rw [inkSpotsSourceBox_parabolicDyadicSourceBox]
    exact hzOpen
  have hzQ1 := inkSpotsSourceBox_subset_Q1_of_strictDense hstrict hzSource
  exact Set.mem_iUnion.mpr ⟨parabolicDyadicSourceBox index,
    Set.mem_iUnion.mpr ⟨hstrict, hzQ1⟩⟩

end

end HypoellipticAleksandrov.Parabolic

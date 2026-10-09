module

public import HypoellipticAleksandrov.Measure.IntervalUnion
public import HypoellipticAleksandrov.Parabolic.Geometry
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Clipped centred coordinate enlargements

This file formalizes the two-sided, clipped interval enlargement used for a
single coordinate in the crawling-of-ink-spots argument.  It also provides a
Fubini lifting theorem from coordinate sections to product volume.

## Main definitions

- `centeredCoordinateContraction` contracts a real coordinate about a centre.
- `clippedCoordinateExpansion` expands a centred interval inside `(-1, 1)`.
- `coordinateSection` records a section with the remaining coordinates ordered
  by `Fin.succAbove`.

## Main results

- `volume_sUnion_clippedCoordinateExpansion` controls arbitrary, including
  uncountable, families of centred intervals.
- `volume_le_of_forall_volume_coordinateSection_le` is the one-coordinate
  Fubini lift.
-/

@[expose] public section

noncomputable section

open Function MeasureTheory Set
open scoped ENNReal Topology

namespace HypoellipticAleksandrov.Parabolic

/-- Contraction of a real coordinate about its prescribed centre. -/
def centeredCoordinateContraction (c zeta : Real) : Real -> Real :=
  fun x => c + zeta * (x - c)

/-- An open interval of the reference coordinate interval which contains the
prescribed contraction centre. -/
def IsClippedCoordinateInterval (c : Real) (I : Set Real) : Prop :=
  IsOpenSubinterval (Ioo (-1 : Real) 1) I /\ c ∈ I

/-- Expansion about `c`, clipped at both endpoints of `(-1, 1)`. -/
def clippedCoordinateExpansion (c kappa : Real) (I : Set Real) : Set Real :=
  Ioo (max (-1 : Real) (c + kappa * (sInf I - c)))
    (min 1 (c + kappa * (sSup I - c)))

private theorem isOpen_ordConnected_eq_Ioo_csInf_csSup (I : Set Real)
    (hIopen : IsOpen I) (hIord : I.OrdConnected) (hInonempty : I.Nonempty)
    (hIbelow : BddBelow I) (hIabove : BddAbove I) :
    I = Ioo (sInf I) (sSup I) := by
  apply Subset.antisymm
  · intro x hx
    have hinf : sInf I ≤ x := csInf_le hIbelow hx
    have hsup : x ≤ sSup I := le_csSup hIabove hx
    constructor
    · by_contra hnot
      have hxeq : x = sInf I := le_antisymm (le_of_not_gt hnot) hinf
      rcases Metric.mem_nhds_iff.1 (hIopen.mem_nhds hx) with ⟨eps, heps, hball⟩
      have hleft : x - eps / 2 ∈ I := hball (by
        rw [Metric.mem_ball, Real.dist_eq]
        have habs : |(x - eps / 2) - x| = eps / 2 := by
          rw [show (x - eps / 2) - x = -(eps / 2) by ring, abs_neg,
            abs_of_pos (by linarith)]
        rw [habs]
        linarith)
      have hle : sInf I ≤ x - eps / 2 := csInf_le hIbelow hleft
      rw [← hxeq] at hle
      linarith
    · by_contra hnot
      have hxeq : sSup I = x := le_antisymm (le_of_not_gt hnot) hsup
      rcases Metric.mem_nhds_iff.1 (hIopen.mem_nhds hx) with ⟨eps, heps, hball⟩
      have hright : x + eps / 2 ∈ I := hball (by
        rw [Metric.mem_ball, Real.dist_eq]
        have habs : |(x + eps / 2) - x| = eps / 2 := by
          rw [show (x + eps / 2) - x = eps / 2 by ring,
            abs_of_pos (by linarith)]
        rw [habs]
        linarith)
      have hle : x + eps / 2 ≤ sSup I := le_csSup hIabove hright
      rw [hxeq] at hle
      linarith
  · exact IsConnected.Ioo_csInf_csSup_subset
      ⟨hInonempty, hIord.isPreconnected⟩ hIbelow hIabove

private theorem clipped_coordinate_interval_data {c : Real} {I : Set Real}
    (hI : IsClippedCoordinateInterval c I) :
    BddBelow I ∧ BddAbove I ∧ I = Ioo (sInf I) (sSup I) ∧
      sInf I < c ∧ c < sSup I ∧ (-1 : Real) ≤ sInf I ∧ sSup I ≤ 1 := by
  have hIbelow : BddBelow I :=
    ⟨-1, fun x hx => (hI.1.2.2.2 hx).1.le⟩
  have hIabove : BddAbove I :=
    ⟨1, fun x hx => (hI.1.2.2.2 hx).2.le⟩
  have hIeq : I = Ioo (sInf I) (sSup I) :=
    isOpen_ordConnected_eq_Ioo_csInf_csSup I hI.1.2.1 hI.1.2.2.1 hI.1.1
      hIbelow hIabove
  have hc : sInf I < c ∧ c < sSup I := by
    have hc' := hI.2
    rw [hIeq] at hc'
    exact hc'
  have hlow : (-1 : Real) ≤ sInf I := by
    by_contra hnot
    have hlt : sInf I < -1 := lt_of_not_ge hnot
    obtain ⟨x, hx, hxc⟩ := exists_between hlt
    have hxI : x ∈ I := by
      rw [hIeq]
      have hminus : (-1 : Real) < c := (hI.1.2.2.2 hI.2).1
      exact ⟨hx, (hxc.trans hminus).trans hc.2⟩
    exact (not_lt_of_ge ((hI.1.2.2.2 hxI).1.le)) hxc
  have hupp : sSup I ≤ 1 := by
    by_contra hnot
    have hlt : 1 < sSup I := lt_of_not_ge hnot
    obtain ⟨x, hcx, hx⟩ := exists_between hlt
    have hxI : x ∈ I := by
      rw [hIeq]
      exact ⟨hc.1.trans ((hI.1.2.2.2 hI.2).2.trans hcx), hx⟩
    exact (not_lt_of_ge ((hI.1.2.2.2 hxI).2.le)) hcx
  exact ⟨hIbelow, hIabove, hIeq, hc.1, hc.2, hlow, hupp⟩

/-- Centered coordinate contraction preserves clipped coordinate intervals. -/
theorem isClippedCoordinateInterval_centeredCoordinateContraction_image
    (c zeta : Real) (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1)
    {I : Set Real} (hI : IsClippedCoordinateInterval c I) :
    IsClippedCoordinateInterval c
      (centeredCoordinateContraction c zeta '' I) := by
  rcases clipped_coordinate_interval_data hI with
    ⟨_, _, hIeq, hcinf, hcsup, hinf, hsup⟩
  rw [hIeq]
  unfold centeredCoordinateContraction
  have hone : 0 < 1 - zeta := sub_pos.mpr hzeta1
  have hleft : zeta * sInf I + (1 - zeta) * c < c := by
    nlinarith [mul_pos hzeta0 (sub_pos.mpr hcinf)]
  have hright : c < zeta * sSup I + (1 - zeta) * c := by
    nlinarith [mul_pos hzeta0 (sub_pos.mpr hcsup)]
  have hlow : -1 < zeta * sInf I + (1 - zeta) * c := by
    nlinarith [mul_nonneg hzeta0.le (sub_nonneg.mpr hinf),
      mul_pos hone (sub_pos.mpr ((hI.1.2.2.2 hI.2).1))]
  have hupp : zeta * sSup I + (1 - zeta) * c < 1 := by
    nlinarith [mul_nonneg hzeta0.le (sub_nonneg.mpr hsup),
      mul_pos hone (sub_pos.mpr ((hI.1.2.2.2 hI.2).2))]
  rw [show (fun x : Real => c + zeta * (x - c)) =
      fun x => zeta * x + (1 - zeta) * c by
        funext x
        ring, image_affine_Ioo hzeta0]
  refine ⟨?_, ?_⟩
  · refine ⟨?_, isOpen_Ioo, ordConnected_Ioo, ?_⟩
    · exact nonempty_Ioo.mpr (hleft.trans hright)
    · exact Ioo_subset_Ioo hlow.le hupp.le
  · exact ⟨hleft, hright⟩

/-- Clipped expansion preserves clipped coordinate intervals. -/
theorem isClippedCoordinateInterval_clippedCoordinateExpansion
    (c kappa : Real) (hkappa : 1 < kappa)
    {I : Set Real} (hI : IsClippedCoordinateInterval c I) :
    IsClippedCoordinateInterval c (clippedCoordinateExpansion c kappa I) := by
  rcases clipped_coordinate_interval_data hI with
    ⟨_, _, _, hcinf, hcsup, _, _⟩
  have hkappa0 : 0 < kappa := zero_lt_one.trans hkappa
  have hleft : max (-1 : Real) (c + kappa * (sInf I - c)) < c := by
    apply max_lt
    · exact (hI.1.2.2.2 hI.2).1
    · nlinarith [mul_neg_of_pos_of_neg hkappa0 (sub_neg.mpr hcinf)]
  have hright : c < min 1 (c + kappa * (sSup I - c)) := by
    apply lt_min
    · exact (hI.1.2.2.2 hI.2).2
    · nlinarith [mul_pos hkappa0 (sub_pos.mpr hcsup)]
  unfold clippedCoordinateExpansion
  refine ⟨?_, ⟨hleft, hright⟩⟩
  refine ⟨nonempty_Ioo.mpr (hleft.trans hright), isOpen_Ioo, ordConnected_Ioo, ?_⟩
  exact Ioo_subset_Ioo (le_max_left _ _) (min_le_left _ _)

/-- Clipped coordinate expansion is monotone under inclusion of eligible intervals. -/
theorem clippedCoordinateExpansion_mono_of_subset
    (c kappa : Real) (hkappa : 1 < kappa)
    {I1 I2 : Set Real} (hI1 : IsClippedCoordinateInterval c I1)
    (hI2 : IsClippedCoordinateInterval c I2) (hI : I1 ⊆ I2) :
    clippedCoordinateExpansion c kappa I1 ⊆
      clippedCoordinateExpansion c kappa I2 := by
  rcases clipped_coordinate_interval_data hI1 with
    ⟨_, hI1above, _, _, _, _, _⟩
  rcases clipped_coordinate_interval_data hI2 with ⟨hI2below, hI2above, _, _, _, _, _⟩
  have hinf : sInf I2 ≤ sInf I1 := by
    apply le_csInf hI1.1.1
    intro x hx
    exact csInf_le hI2below (hI hx)
  have hsup : sSup I1 ≤ sSup I2 := by
    apply (csSup_le_iff hI1above hI1.1.1).2
    intro x hx
    exact le_csSup hI2above (hI hx)
  have hkappa0 : 0 ≤ kappa := le_trans zero_le_one hkappa.le
  unfold clippedCoordinateExpansion
  apply Ioo_subset_Ioo
  · apply max_le_max_left
    have hmul : 0 ≤ kappa * (sInf I1 - sInf I2) :=
      mul_nonneg hkappa0 (sub_nonneg.mpr hinf)
    nlinarith
  · apply min_le_min_left
    have hmul : 0 ≤ kappa * (sSup I2 - sSup I1) :=
      mul_nonneg hkappa0 (sub_nonneg.mpr hsup)
    nlinarith

/-- The clipped expansion has at most the unclipped `kappa` volume factor. -/
theorem volume_clippedCoordinateExpansion_le
    (c kappa : Real) (hkappa : 1 < kappa)
    {I : Set Real} (hI : IsClippedCoordinateInterval c I) :
    volume (clippedCoordinateExpansion c kappa I) ≤
      ENNReal.ofReal kappa * volume I := by
  rcases clipped_coordinate_interval_data hI with
    ⟨_, _, hIeq, _, _, _, _⟩
  have hlt : sInf I < sSup I := (clipped_coordinate_interval_data hI).2.2.2.1.trans
    (clipped_coordinate_interval_data hI).2.2.2.2.1
  rw [hIeq, clippedCoordinateExpansion, csInf_Ioo hlt, csSup_Ioo hlt,
    Real.volume_Ioo, Real.volume_Ioo]
  rw [← ENNReal.ofReal_mul (le_trans zero_le_one hkappa.le)]
  apply ENNReal.ofReal_le_ofReal
  have hleft : c + kappa * (sInf I - c) ≤
      max (-1 : Real) (c + kappa * (sInf I - c)) := le_max_right _ _
  have hright : min 1 (c + kappa * (sSup I - c)) ≤
      c + kappa * (sSup I - c) := min_le_right _ _
  nlinarith

private theorem clippedCoordinateInterval_subset_clippedCoordinateExpansion
    {c kappa : Real} (hkappa : 1 < kappa) {I : Set Real}
    (hI : IsClippedCoordinateInterval c I) :
    I ⊆ clippedCoordinateExpansion c kappa I := by
  rcases clipped_coordinate_interval_data hI with
    ⟨_, _, hIeq, hcinf, hcsup, _, _⟩
  have hkappa0 : 0 < kappa := zero_lt_one.trans hkappa
  intro x hx
  rw [hIeq] at hx
  unfold clippedCoordinateExpansion
  constructor
  · apply max_lt
    · exact (hI.1.2.2.2 (by rw [hIeq]; exact hx)).1
    · have hmul : 0 < (kappa - 1) * (c - sInf I) :=
        mul_pos (sub_pos.mpr hkappa) (sub_pos.mpr hcinf)
      have hleft : c + kappa * (sInf I - c) < sInf I := by
        nlinarith [hmul]
      exact hleft.trans hx.1
  · apply lt_min
    · exact (hI.1.2.2.2 (by rw [hIeq]; exact hx)).2
    · have hmul : 0 < (kappa - 1) * (sSup I - c) :=
        mul_pos (sub_pos.mpr hkappa) (sub_pos.mpr hcsup)
      have hright : sSup I < c + kappa * (sSup I - c) := by
        nlinarith [hmul]
      exact hx.2.trans hright

private noncomputable def clippedCoordinateExpansionOrSelf (c kappa : Real)
    (I : Set Real) : Set Real := by
  classical
  exact if c ∈ I then clippedCoordinateExpansion c kappa I else I

private theorem isOpenSubinterval_clippedCoordinateExpansionOrSelf
    (c kappa : Real) (hkappa : 1 < kappa) {I : Set Real}
    (hI : IsOpenSubinterval (Ioo (-1 : Real) 1) I) :
    IsOpenSubinterval (Ioo (-1 : Real) 1)
      (clippedCoordinateExpansionOrSelf c kappa I) := by
  classical
  by_cases hc : c ∈ I
  · rw [clippedCoordinateExpansionOrSelf, if_pos hc]
    exact (isClippedCoordinateInterval_clippedCoordinateExpansion c kappa hkappa
      ⟨hI, hc⟩).1
  · rw [clippedCoordinateExpansionOrSelf, if_neg hc]
    exact hI

private theorem volume_clippedCoordinateExpansionOrSelf_le
    (c kappa : Real) (hkappa : 1 < kappa) {I : Set Real}
    (hI : IsOpenSubinterval (Ioo (-1 : Real) 1) I) :
    volume (clippedCoordinateExpansionOrSelf c kappa I) ≤
      ENNReal.ofReal kappa * volume I := by
  classical
  by_cases hc : c ∈ I
  · rw [clippedCoordinateExpansionOrSelf, if_pos hc]
    exact volume_clippedCoordinateExpansion_le c kappa hkappa ⟨hI, hc⟩
  · rw [clippedCoordinateExpansionOrSelf, if_neg hc]
    calc
      volume I = 1 * volume I := (one_mul _).symm
      _ ≤ ENNReal.ofReal kappa * volume I := by
        gcongr
        exact ENNReal.one_le_ofReal.mpr hkappa.le

private theorem clippedCoordinateExpansionOrSelf_mono_of_subset
    (c kappa : Real) (hkappa : 1 < kappa) {I1 I2 : Set Real}
    (hI1 : IsOpenSubinterval (Ioo (-1 : Real) 1) I1)
    (hI2 : IsOpenSubinterval (Ioo (-1 : Real) 1) I2) (hI : I1 ⊆ I2) :
    clippedCoordinateExpansionOrSelf c kappa I1 ⊆
      clippedCoordinateExpansionOrSelf c kappa I2 := by
  classical
  by_cases hc1 : c ∈ I1
  · have hc2 : c ∈ I2 := hI hc1
    change (if c ∈ I1 then clippedCoordinateExpansion c kappa I1 else I1) ⊆
      if c ∈ I2 then clippedCoordinateExpansion c kappa I2 else I2
    rw [if_pos hc1, if_pos hc2]
    exact clippedCoordinateExpansion_mono_of_subset c kappa hkappa ⟨hI1, hc1⟩
      ⟨hI2, hc2⟩ hI
  · by_cases hc2 : c ∈ I2
    · change (if c ∈ I1 then clippedCoordinateExpansion c kappa I1 else I1) ⊆
        if c ∈ I2 then clippedCoordinateExpansion c kappa I2 else I2
      rw [if_neg hc1, if_pos hc2]
      exact hI.trans
        (clippedCoordinateInterval_subset_clippedCoordinateExpansion hkappa ⟨hI2, hc2⟩)
    · change (if c ∈ I1 then clippedCoordinateExpansion c kappa I1 else I1) ⊆
        if c ∈ I2 then clippedCoordinateExpansion c kappa I2 else I2
      rw [if_neg hc1, if_neg hc2]
      exact hI

/-- Exact inverse identity for a contracted clipped interval. -/
theorem clippedCoordinateExpansion_centeredCoordinateContraction_image
    (c zeta : Real) (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1)
    {I : Set Real} (hI : IsClippedCoordinateInterval c I) :
    clippedCoordinateExpansion c zeta⁻¹
        (centeredCoordinateContraction c zeta '' I) = I := by
  rcases clipped_coordinate_interval_data hI with
    ⟨_, _, hIeq, hcinf, hcsup, hinf, hsup⟩
  have _hzeta1 : zeta < 1 := hzeta1
  rw [hIeq]
  unfold centeredCoordinateContraction clippedCoordinateExpansion
  have hcontracted : zeta * sInf I + (1 - zeta) * c <
      zeta * sSup I + (1 - zeta) * c := by
    nlinarith [mul_pos hzeta0 (sub_pos.mpr (hcinf.trans hcsup))]
  rw [show (fun x : Real => c + zeta * (x - c)) =
      fun x => zeta * x + (1 - zeta) * c by
        funext x
        ring, image_affine_Ioo hzeta0, csInf_Ioo hcontracted,
    csSup_Ioo hcontracted]
  have hleft : c + zeta⁻¹ *
      (zeta * sInf I + (1 - zeta) * c - c) = sInf I := by
    field_simp [ne_of_gt hzeta0]
    ring
  have hright : c + zeta⁻¹ *
      (zeta * sSup I + (1 - zeta) * c - c) = sSup I := by
    field_simp [ne_of_gt hzeta0]
    ring
  rw [hleft, hright, max_eq_right hinf, min_eq_right hsup]

/-- Sharp uncountable-family union estimate. -/
theorem volume_sUnion_clippedCoordinateExpansion
    (c kappa : Real) (hkappa : 1 < kappa) (B : Set (Set Real))
    (hB : ∀ I ∈ B, IsClippedCoordinateInterval c I) :
    volume (⋃₀ (clippedCoordinateExpansion c kappa '' B)) ≤
      ENNReal.ofReal kappa * volume (⋃₀ B) := by
  classical
  let g := clippedCoordinateExpansionOrSelf c kappa
  have himage : g '' B = clippedCoordinateExpansion c kappa '' B := by
    ext U
    constructor
    · rintro ⟨I, hIB, rfl⟩
      change (if c ∈ I then clippedCoordinateExpansion c kappa I else I) ∈
        clippedCoordinateExpansion c kappa '' B
      rw [if_pos (hB I hIB).2]
      exact ⟨I, hIB, rfl⟩
    · rintro ⟨I, hIB, rfl⟩
      refine ⟨I, hIB, ?_⟩
      change (if c ∈ I then clippedCoordinateExpansion c kappa I else I) =
        clippedCoordinateExpansion c kappa I
      rw [if_pos (hB I hIB).2]
  rw [← himage]
  apply volume_sUnion_monotone_interval_enlargement_Ioo_of_le kappa hkappa (-1) 1
    (by norm_num) B g
  · intro I hI
    exact (hB I hI).1
  · intro I hI
    exact isOpenSubinterval_clippedCoordinateExpansionOrSelf c kappa hkappa hI
  · intro I hI
    exact volume_clippedCoordinateExpansionOrSelf_le c kappa hkappa hI
  · intro I1 I2 hI1 hI2 hsubset
    exact clippedCoordinateExpansionOrSelf_mono_of_subset c kappa hkappa hI1 hI2 hsubset

/-- The section obtained by varying `i`; remaining coordinates use
`i.succAbove` order. -/
def coordinateSection {n : Nat} (i : Fin (n + 1))
    (S : Set (Fin (n + 1) -> Real)) (w : Fin n -> Real) : Set Real :=
  {x | (MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) => Real) i).symm (x, w) ∈ S}

private theorem coordinateSection_eq_preimage_image {n : Nat}
    (i : Fin (n + 1)) (S : Set (Fin (n + 1) -> Real)) (w : Fin n -> Real) :
    (fun x : Real => (x, w)) ⁻¹'
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Real) i '' S) =
      coordinateSection i S w := by
  ext x
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Real) i
  change (x : Real) ∈ (fun x : Real => (x, w)) ⁻¹' (e '' S) ↔
    e.symm (x, w) ∈ S
  constructor
  · rintro ⟨y, hy, hey⟩
    have hyeq : y = e.symm (x, w) := by
      apply e.injective
      simpa using hey
    rw [← hyeq]
    exact hy
  · intro hx
    exact ⟨e.symm (x, w), hx, e.apply_symm_apply (x, w)⟩

private theorem volume_eq_lintegral_coordinateSection {n : Nat}
    (i : Fin (n + 1)) (S : Set (Fin (n + 1) -> Real))
    (hS : MeasurableSet S) :
    volume S = ∫⁻ w, volume (coordinateSection i S w) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Real) i
  have he : MeasurePreserving e :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => Real) i
  have himage : volume (e '' S) = volume S := by
    rw [← he.map_eq, Measure.map_apply e.measurable (e.measurableSet_image.2 hS),
      e.preimage_image]
  calc
    volume S = volume (e '' S) := himage.symm
    _ = ∫⁻ w, volume (coordinateSection i S w) := by
      rw [Measure.volume_eq_prod, Measure.prod_apply_symm
        (e.measurableSet_image.2 hS)]
      exact lintegral_congr fun w =>
        congr_arg volume (coordinateSection_eq_preimage_image i S w)

/-- Fubini lift of pointwise one-coordinate section inequalities. -/
theorem volume_le_of_forall_volume_coordinateSection_le
    {n : Nat} (i : Fin (n + 1)) (S T : Set (Fin (n + 1) -> Real))
    (hS : MeasurableSet S) (hT : MeasurableSet T) (kappa : Real)
    (hsection : ∀ w : Fin n -> Real,
      volume (coordinateSection i S w) ≤
        ENNReal.ofReal kappa * volume (coordinateSection i T w)) :
    volume S ≤ ENNReal.ofReal kappa * volume T := by
  rw [volume_eq_lintegral_coordinateSection i S hS,
    volume_eq_lintegral_coordinateSection i T hT]
  calc
    (∫⁻ w, volume (coordinateSection i S w)) ≤
        ∫⁻ w, ENNReal.ofReal kappa * volume (coordinateSection i T w) :=
      lintegral_mono hsection
    _ = ENNReal.ofReal kappa *
        ∫⁻ w, volume (coordinateSection i T w) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Time is coordinate zero and velocity coordinate `j` is `Fin.succ j`. -/
def timeVelocityCoordinateEquiv (d : Nat) :
    TimeVelocity d ≃ᵐ (Fin (d + 1) -> Real) :=
  (MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (d + 1) => Real) 0).symm

/-- Coordinate section of a time--velocity set after the fixed coordinate
identification. -/
def timeVelocityCoordinateSection (d : Nat) (i : Fin (d + 1))
    (S : Set (TimeVelocity d)) (w : Fin d -> Real) : Set Real :=
  coordinateSection i (timeVelocityCoordinateEquiv d '' S) w

private theorem volume_timeVelocityCoordinateEquiv_image {d : Nat}
    (S : Set (TimeVelocity d)) (hS : MeasurableSet S) :
    volume (timeVelocityCoordinateEquiv d '' S) = volume S := by
  let e := timeVelocityCoordinateEquiv d
  have he : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => Real) 0).symm
  rw [← he.map_eq, Measure.map_apply e.measurable (e.measurableSet_image.2 hS),
    e.preimage_image]

/-- Fubini lift of coordinate-section bounds to time--velocity volume. -/
theorem volume_timeVelocity_le_of_forall_volume_coordinateSection_le
    {d : Nat} (i : Fin (d + 1)) (S T : Set (TimeVelocity d))
    (hS : MeasurableSet S) (hT : MeasurableSet T) (kappa : Real)
    (hsection : ∀ w : Fin d -> Real,
      volume (timeVelocityCoordinateSection d i S w) ≤
        ENNReal.ofReal kappa * volume (timeVelocityCoordinateSection d i T w)) :
    volume S ≤ ENNReal.ofReal kappa * volume T := by
  calc
    volume S = volume (timeVelocityCoordinateEquiv d '' S) :=
      (volume_timeVelocityCoordinateEquiv_image S hS).symm
    _ ≤ ENNReal.ofReal kappa * volume (timeVelocityCoordinateEquiv d '' T) :=
      volume_le_of_forall_volume_coordinateSection_le i
        (timeVelocityCoordinateEquiv d '' S) (timeVelocityCoordinateEquiv d '' T)
        ((timeVelocityCoordinateEquiv d).measurableSet_image.2 hS)
        ((timeVelocityCoordinateEquiv d).measurableSet_image.2 hT) kappa
        (by simpa only [timeVelocityCoordinateSection] using hsection)
    _ = ENNReal.ofReal kappa * volume T := by
      rw [volume_timeVelocityCoordinateEquiv_image T hT]

end HypoellipticAleksandrov.Parabolic

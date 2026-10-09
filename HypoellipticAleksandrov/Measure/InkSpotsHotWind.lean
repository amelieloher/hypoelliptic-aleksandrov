module

public import HypoellipticAleksandrov.Measure.InkSpotsWind
public import HypoellipticAleksandrov.Measure.ClippedCoordinateUnion
public import HypoellipticAleksandrov.Measure.VaryingCenterIntervalUnion

/-!
# Hot-wind scaffold for source ink spots

This module proves Lemma 2.4 of Krylov--Safonov, Section 2, by a
time contraction followed by one varying-centre/Fubini contraction for each
velocity coordinate.
-/

@[expose] public section

noncomputable section

open Function MeasureTheory Set
open scoped ENNReal Topology

namespace HypoellipticAleksandrov.Parabolic

private theorem strictDense_timeInterval_subset_unit {d : ℕ}
    {Gamma : Set (TimeVelocity d)} {xi : ℝ} {q : InkSpotsBox d}
    (hq : inkSpotsStrictDense Gamma xi q) :
    Ioo q.baseTime (q.baseTime + q.radius ^ 2) ⊆ Ioo 0 1 := by
  have hr : 0 < q.radius := hq.1
  intro t ht
  have htSource : (t, q.center) ∈ inkSpotsSourceBox q := by
    rw [mem_inkSpotsSourceBox_iff]
    refine ⟨ht.1, ht.2, ?_⟩
    · intro i
      simp only [sub_self, abs_zero]
      exact hr
  have htUnit : (t, q.center) ∈ inkSpotsUnitBox d := hq.2.1 htSource
  rw [inkSpotsUnitBox, mem_parabolicBox_iff] at htUnit
  constructor
  · exact htUnit.1
  · convert htUnit.2.1 using 1
    norm_num

private theorem strictDense_baseTime_nonneg {d : ℕ}
    {Gamma : Set (TimeVelocity d)} {xi : ℝ} {q : InkSpotsBox d}
    (hq : inkSpotsStrictDense Gamma xi q) :
    0 ≤ q.baseTime := by
  have htime := strictDense_timeInterval_subset_unit hq
  have hnonempty : q.baseTime < q.baseTime + q.radius ^ 2 := by
    nlinarith [sq_pos_of_pos hq.1]
  exact (Ioo_subset_Ioo_iff hnonempty).mp htime |>.1

private theorem strictDense_baseTime_add_sq_le_one {d : ℕ}
    {Gamma : Set (TimeVelocity d)} {xi : ℝ} {q : InkSpotsBox d}
    (hq : inkSpotsStrictDense Gamma xi q) :
    q.baseTime + q.radius ^ 2 ≤ 1 := by
  have htime := strictDense_timeInterval_subset_unit hq
  have hnonempty : q.baseTime < q.baseTime + q.radius ^ 2 := by
    nlinarith [sq_pos_of_pos hq.1]
  exact (Ioo_subset_Ioo_iff hnonempty).mp htime |>.2

private theorem strictDense_center_mem_unit_velocityCube {d : ℕ}
    {Gamma : Set (TimeVelocity d)} {xi : ℝ} {q : InkSpotsBox d}
    (hq : inkSpotsStrictDense Gamma xi q) :
    q.center ∈ velocityCube (0 : PDE.Vec d) 1 := by
  have hr : 0 < q.radius := hq.1
  let t : ℝ := q.baseTime + q.radius ^ 2 / 2
  have htSource : (t, q.center) ∈ inkSpotsSourceBox q := by
    rw [mem_inkSpotsSourceBox_iff]
    refine ⟨?_, ?_, ?_⟩
    · dsimp [t]
      nlinarith [sq_pos_of_pos hr]
    · dsimp [t]
      nlinarith [sq_pos_of_pos hr]
    · intro i
      simp only [sub_self, abs_zero]
      exact hr
  have htUnit : (t, q.center) ∈ inkSpotsUnitBox d := hq.2.1 htSource
  rw [inkSpotsUnitBox, mem_parabolicBox_iff] at htUnit
  exact htUnit.2.2

private theorem strictDense_center_coord_bounds {d : ℕ}
    {Gamma : Set (TimeVelocity d)} {xi : ℝ} {q : InkSpotsBox d}
    (hq : inkSpotsStrictDense Gamma xi q) (j : Fin d) :
    -1 < q.center j ∧ q.center j < 1 := by
  simpa only [Pi.zero_apply, sub_zero] using
    abs_lt.mp (strictDense_center_mem_unit_velocityCube hq j)


private def windAmbientTime (eta : ℝ) : Set ℝ :=
  Ioo 0 (1 + 4 / eta)

private def windAmbientVelocity (d : ℕ) : Set (PDE.Vec d) :=
  velocityCube (0 : PDE.Vec d) 1

private def windAmbient (d : ℕ) (eta : ℝ) : Set (TimeVelocity d) :=
  windAmbientTime eta ×ˢ windAmbientVelocity d

private theorem inkSpotsQ2_subset_windAmbient {d : ℕ} {eta : ℝ}
    {Gamma : Set (TimeVelocity d)} {xi : ℝ} {q : InkSpotsBox d}
    (heta : 0 < eta) (hq : inkSpotsStrictDense Gamma xi q) :
    inkSpotsQ2 eta q ⊆ windAmbient d eta := by
  intro z hz
  rcases z with ⟨t, v⟩
  rw [mem_inkSpotsQ2_iff] at hz
  refine ⟨?_, hz.2.2.2⟩
  constructor
  · have hbase : 0 ≤ q.baseTime := strictDense_baseTime_nonneg hq
    nlinarith [sq_pos_of_pos hq.1]
  · have htop : q.baseTime + q.radius ^ 2 ≤ 1 :=
      strictDense_baseTime_add_sq_le_one hq
    have hbase : 0 ≤ q.baseTime := strictDense_baseTime_nonneg hq
    have hsquare : q.radius ^ 2 ≤ 1 := by nlinarith [hbase]
    rw [inkSpotsTerminalTime_eq] at hz
    have hdiv : 4 * q.radius ^ 2 / eta ≤ 4 / eta := by
      rw [div_le_div_iff_of_pos_right heta]
      nlinarith
    exact hz.2.1.trans_le (by linarith)


/-- The time section of a forward source stack. -/
private def windForwardInterval {d : ℕ} (eta : ℝ) (q : InkSpotsBox d) : Set ℝ :=
  Ioo (q.baseTime + q.radius ^ 2) (inkSpotsTerminalTime eta q)


private theorem isOpen_ordConnected_eq_Ioo_csInf_csSup (I : Set ℝ)
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

/-- Right-end interval expansion, clipped only at the left endpoint of the
ambient interval.  This is the concrete map used for the time sections. -/
private def rightEndpointExpansion (a kappa : ℝ) (I : Set ℝ) : Set ℝ :=
  Ioo (max a (sSup I - kappa * (sSup I - sInf I))) (sSup I)

private theorem rightEndpointExpansion_forwardInterval {d : ℕ}
    {Gamma : Set (TimeVelocity d)} {xi eta : ℝ} (q : InkSpotsBox d)
    (heta : 0 < eta) (hq : inkSpotsStrictDense Gamma xi q) :
    rightEndpointExpansion 0 (1 + eta) (windForwardInterval eta q) =
      Ioo (max 0 (q.baseTime - 3 * q.radius ^ 2))
        (inkSpotsTerminalTime eta q) := by
  unfold rightEndpointExpansion windForwardInterval
  have hnonempty : q.baseTime + q.radius ^ 2 < inkSpotsTerminalTime eta q := by
    rw [inkSpotsTerminalTime_eq]
    have hsquare : 0 < q.radius ^ 2 := sq_pos_of_pos hq.1
    field_simp
    nlinarith
  rw [csInf_Ioo hnonempty, csSup_Ioo hnonempty]
  congr 2
  rw [inkSpotsTerminalTime_eq]
  field_simp
  ring

private theorem rightEndpointExpansion_mono_of_subset {a kappa : ℝ}
    {I₁ I₂ : Set ℝ} (hI₁nonempty : I₁.Nonempty) (hI₂below : BddBelow I₂)
    (hI₁above : BddAbove I₁) (hI₂above : BddAbove I₂)
    (hkappa : 1 ≤ kappa) (hsub : I₁ ⊆ I₂) :
    rightEndpointExpansion a kappa I₁ ⊆ rightEndpointExpansion a kappa I₂ := by
  have hinf : sInf I₂ ≤ sInf I₁ := by
    apply le_csInf hI₁nonempty
    intro x hx
    exact csInf_le hI₂below (hsub hx)
  have hsup : sSup I₁ ≤ sSup I₂ := by
    apply (csSup_le_iff hI₁above hI₁nonempty).2
    intro x hx
    exact le_csSup hI₂above (hsub hx)
  unfold rightEndpointExpansion
  apply Ioo_subset_Ioo
  · apply max_le_max_left
    nlinarith
  · exact hsup

private theorem rightEndpointExpansion_measure_le {a b kappa : ℝ} {I : Set ℝ}
    (hkappa : 1 ≤ kappa) (hI : IsOpenSubinterval (Ioo a b) I) :
    volume (rightEndpointExpansion a kappa I) ≤
      ENNReal.ofReal kappa * volume I := by
  have hIbelow : BddBelow I :=
    ⟨a, fun x hx => (hI.2.2.2 hx).1.le⟩
  have hIabove : BddAbove I :=
    ⟨b, fun x hx => (hI.2.2.2 hx).2.le⟩
  have hIeq := isOpen_ordConnected_eq_Ioo_csInf_csSup I hI.2.1 hI.2.2.1
    hI.1 hIbelow hIabove
  have hlt : sInf I < sSup I := by
    rw [hIeq] at hI
    exact nonempty_Ioo.mp hI.1
  rw [hIeq, rightEndpointExpansion, csInf_Ioo hlt, csSup_Ioo hlt,
    Real.volume_Ioo, Real.volume_Ioo]
  rw [← ENNReal.ofReal_mul (le_trans zero_le_one hkappa)]
  apply ENNReal.ofReal_le_ofReal
  have hleft : sSup I - kappa * (sSup I - sInf I) ≤
      max a (sSup I - kappa * (sSup I - sInf I)) := le_max_right _ _
  nlinarith

private theorem isOpenSubinterval_rightEndpointExpansion {a b kappa : ℝ}
    {I : Set ℝ} (hkappa : 1 < kappa) (hI : IsOpenSubinterval (Ioo a b) I) :
    IsOpenSubinterval (Ioo a b) (rightEndpointExpansion a kappa I) := by
  have hIbelow : BddBelow I :=
    ⟨a, fun x hx => (hI.2.2.2 hx).1.le⟩
  have hIabove : BddAbove I :=
    ⟨b, fun x hx => (hI.2.2.2 hx).2.le⟩
  have hIeq := isOpen_ordConnected_eq_Ioo_csInf_csSup I hI.2.1 hI.2.2.1
    hI.1 hIbelow hIabove
  have hlt : sInf I < sSup I := by
    rw [hIeq] at hI
    exact nonempty_Ioo.mp hI.1
  have hupper : sSup I ≤ b := by
    rcases hI.1 with ⟨x, hx⟩
    apply (csSup_le_iff hIabove ⟨x, hx⟩).2
    intro y hy
    exact (hI.2.2.2 hy).2.le
  have haUpper : a < sSup I := by
    rcases hI.1 with ⟨x, hx⟩
    exact (hI.2.2.2 hx).1.trans_le (le_csSup hIabove hx)
  unfold rightEndpointExpansion
  constructor
  · refine nonempty_Ioo.mpr (max_lt ?_ ?_)
    · exact haUpper
    · have hproduct : 0 < kappa * (sSup I - sInf I) :=
        mul_pos (zero_lt_one.trans hkappa) (sub_pos.mpr hlt)
      linarith
  constructor
  · exact isOpen_Ioo
  constructor
  · exact ordConnected_Ioo
  · exact Ioo_subset_Ioo (le_max_left _ _) hupper

private theorem volume_sUnion_rightEndpointExpansion {a b kappa : ℝ}
    (hkappa : 1 < kappa) (B : Set (Set ℝ))
    (hB : ∀ I ∈ B, IsOpenSubinterval (Ioo a b) I)
    (hbounded : Bornology.IsBounded (⋃₀ B)) :
    volume (⋃₀ (rightEndpointExpansion a kappa '' B)) ≤
      ENNReal.ofReal kappa * volume (⋃₀ B) := by
  apply volume_sUnion_monotone_interval_enlargement_of_le kappa hkappa (Ioo a b)
    isOpen_Ioo ordConnected_Ioo B (rightEndpointExpansion a kappa) hB hbounded
  · intro I hI
    exact isOpenSubinterval_rightEndpointExpansion hkappa hI
  · intro I hI _
    exact rightEndpointExpansion_measure_le hkappa.le hI
  · intro I₁ I₂ hI₁ hI₂ hsub
    have hI₂below : BddBelow I₂ :=
      ⟨a, fun x hx => (hI₂.2.2.2 hx).1.le⟩
    have hI₁above : BddAbove I₁ :=
      ⟨b, fun x hx => (hI₁.2.2.2 hx).2.le⟩
    have hI₂above : BddAbove I₂ :=
      ⟨b, fun x hx => (hI₂.2.2.2 hx).2.le⟩
    exact rightEndpointExpansion_mono_of_subset hI₁.1 hI₂below hI₁above hI₂above
      hkappa.le hsub

private def timeSection {d : ℕ} (S : Set (TimeVelocity d)) (v : PDE.Vec d) : Set ℝ :=
  {t | (t, v) ∈ S}


private theorem windForwardInterval_eligible {d : ℕ}
    {Gamma : Set (TimeVelocity d)} {xi eta : ℝ} {q : InkSpotsBox d}
    (heta : 0 < eta) (hq : inkSpotsStrictDense Gamma xi q) :
    IsOpenSubinterval (windAmbientTime eta) (windForwardInterval eta q) := by
  constructor
  · apply nonempty_Ioo.mpr
    rw [inkSpotsTerminalTime_eq]
    have hsquare : 0 < q.radius ^ 2 := sq_pos_of_pos hq.1
    field_simp
    nlinarith
  constructor
  · exact isOpen_Ioo
  constructor
  · exact ordConnected_Ioo
  · intro t ht
    have hbase : 0 ≤ q.baseTime := strictDense_baseTime_nonneg hq
    have htop : q.baseTime + q.radius ^ 2 ≤ 1 :=
      strictDense_baseTime_add_sq_le_one hq
    have hsquare : q.radius ^ 2 ≤ 1 := by nlinarith
    rw [windForwardInterval, mem_Ioo] at ht
    rw [windAmbientTime, mem_Ioo]
    constructor
    · nlinarith [sq_pos_of_pos hq.1]
    · rw [inkSpotsTerminalTime_eq] at ht
      have hdiv : 4 * q.radius ^ 2 / eta ≤ 4 / eta := by
        rw [div_le_div_iff_of_pos_right heta]
        nlinarith
      exact ht.2.trans_le (by linarith)


private theorem volume_eq_lintegral_timeSection {d : ℕ} (S : Set (TimeVelocity d))
    (hS : MeasurableSet S) :
    volume S = ∫⁻ v, volume (timeSection S v) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm hS]
  rfl


/-- The source terminal contraction restricted to its time coordinate. -/
private def inkSpotsTimeContraction {d : ℕ} (eta zeta : ℝ) (q : InkSpotsBox d) :
    ℝ → ℝ :=
  fun t => inkSpotsTerminalTime eta q - zeta ^ 2 *
    (inkSpotsTerminalTime eta q - t)

/-- The first, time-only stage of the terminal contraction. -/
private def inkSpotsQ2TimeContracted {d : ℕ} (eta zeta : ℝ) (q : InkSpotsBox d) :
    Set (TimeVelocity d) :=
  (inkSpotsTimeContraction eta zeta q '' windForwardInterval eta q) ×ˢ
    (velocityCube q.center (3 * q.radius) ∩ velocityCube 0 1)

private theorem inkSpotsTimeContraction_forwardInterval {d : ℕ} {eta zeta : ℝ}
    {q : InkSpotsBox d} (hzeta : 0 < zeta) :
    inkSpotsTimeContraction eta zeta q '' windForwardInterval eta q =
      Ioo (inkSpotsTerminalTime eta q - zeta ^ 2 *
        (inkSpotsTerminalTime eta q - (q.baseTime + q.radius ^ 2)))
        (inkSpotsTerminalTime eta q) := by
  unfold inkSpotsTimeContraction windForwardInterval
  let T := inkSpotsTerminalTime eta q
  have hsq : 0 < zeta ^ 2 := sq_pos_of_pos hzeta
  convert image_affine_Ioo hsq ((1 - zeta ^ 2) * T)
    (q.baseTime + q.radius ^ 2) T using 1 <;> ext <;> dsimp [T] <;> ring_nf

private def inkSpotsD2TimeContractedUnion {d : ℕ} (Gamma : Set (TimeVelocity d))
    (xi eta zeta : ℝ) : Set (TimeVelocity d) :=
  ⋃ q ∈ inkSpotsDenseBoxes Gamma xi, inkSpotsQ2TimeContracted eta zeta q

private theorem inkSpotsQ2TimeContracted_subset_Q2 {d : ℕ} {eta zeta : ℝ}
    {q : InkSpotsBox d} (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1) :
    inkSpotsQ2TimeContracted eta zeta q ⊆ inkSpotsQ2 eta q := by
  intro z hz
  rcases z with ⟨t, v⟩
  rcases hz.1 with ⟨s, hs, rfl⟩
  rw [mem_inkSpotsQ2_iff]
  refine ⟨?_, ?_, hz.2.1, hz.2.2⟩
  · change q.baseTime + q.radius ^ 2 <
      inkSpotsTerminalTime eta q - zeta ^ 2 *
        (inkSpotsTerminalTime eta q - s)
    have hsq1 : zeta ^ 2 < 1 := by
      nlinarith [mul_pos hzeta0 (sub_pos.mpr hzeta1)]
    rw [windForwardInterval, mem_Ioo] at hs
    have hT : q.baseTime + q.radius ^ 2 < inkSpotsTerminalTime eta q :=
      hs.1.trans hs.2
    have hdecomp :
        inkSpotsTerminalTime eta q - zeta ^ 2 *
            (inkSpotsTerminalTime eta q - s) - (q.baseTime + q.radius ^ 2) =
          (1 - zeta ^ 2) *
              (inkSpotsTerminalTime eta q - (q.baseTime + q.radius ^ 2)) +
            zeta ^ 2 * (s - (q.baseTime + q.radius ^ 2)) := by
      ring
    apply sub_pos.mp
    rw [hdecomp]
    exact add_pos
      (mul_pos (sub_pos.mpr hsq1) (sub_pos.mpr hT))
      (mul_pos (sq_pos_of_pos hzeta0) (sub_pos.mpr hs.1))
  · change inkSpotsTerminalTime eta q - zeta ^ 2 *
      (inkSpotsTerminalTime eta q - s) < inkSpotsTerminalTime eta q
    have hsq0 : 0 < zeta ^ 2 := sq_pos_of_pos hzeta0
    rw [windForwardInterval, mem_Ioo] at hs
    apply sub_pos.mp
    nlinarith [mul_pos hsq0 (sub_pos.mpr hs.2)]

private theorem inkSpotsD2TimeContractedUnion_subset_windAmbient {d : ℕ}
    (Gamma : Set (TimeVelocity d)) (xi eta zeta : ℝ) (heta : 0 < eta)
    (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1) :
    inkSpotsD2TimeContractedUnion Gamma xi eta zeta ⊆ windAmbient d eta := by
  intro z hz
  rw [inkSpotsD2TimeContractedUnion] at hz
  rcases mem_iUnion.1 hz with ⟨q, hz⟩
  rcases mem_iUnion.1 hz with ⟨hq, hz⟩
  exact inkSpotsQ2_subset_windAmbient heta hq
    (inkSpotsQ2TimeContracted_subset_Q2 hzeta0 hzeta1 hz)

private def hotTimeSectionFamily {d : ℕ} (Gamma : Set (TimeVelocity d))
    (xi eta zeta : ℝ) (v : PDE.Vec d) : Set (Set ℝ) :=
  {I | ∃ q, inkSpotsStrictDense Gamma xi q ∧
    v ∈ velocityCube q.center (3 * q.radius) ∧ v ∈ velocityCube 0 1 ∧
    I = inkSpotsTimeContraction eta zeta q '' windForwardInterval eta q}

private theorem timeSection_inkSpotsD2TimeContractedUnion_eq_sUnion_hotTimeSectionFamily
    {d : ℕ} (Gamma : Set (TimeVelocity d)) (xi eta zeta : ℝ) (v : PDE.Vec d) :
    timeSection (inkSpotsD2TimeContractedUnion Gamma xi eta zeta) v =
      ⋃₀ (hotTimeSectionFamily Gamma xi eta zeta v) := by
  ext t
  constructor
  · intro ht
    rw [timeSection, inkSpotsD2TimeContractedUnion] at ht
    rcases mem_iUnion.1 ht with ⟨q, ht⟩
    rcases mem_iUnion.1 ht with ⟨hq, ht⟩
    refine mem_sUnion.2 ⟨inkSpotsTimeContraction eta zeta q ''
      windForwardInterval eta q, ?_, ht.1⟩
    exact ⟨q, hq, ht.2.1, ht.2.2, rfl⟩
  · intro ht
    rcases mem_sUnion.1 ht with ⟨I, hI, ht⟩
    rcases hI with ⟨q, hq, hvCenter, hvUnit, rfl⟩
    rw [timeSection, inkSpotsD2TimeContractedUnion]
    exact mem_iUnion.2 ⟨q, mem_iUnion.2 ⟨hq, ⟨ht, hvCenter, hvUnit⟩⟩⟩

private theorem hotTimeInterval_eligible {d : ℕ} {Gamma : Set (TimeVelocity d)}
    {xi eta zeta : ℝ} {q : InkSpotsBox d} (heta : 0 < eta)
    (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1)
    (hq : inkSpotsStrictDense Gamma xi q) :
    IsOpenSubinterval (windAmbientTime eta)
      (inkSpotsTimeContraction eta zeta q '' windForwardInterval eta q) := by
  rw [inkSpotsTimeContraction_forwardInterval hzeta0]
  constructor
  · apply nonempty_Ioo.mpr
    have hsource : q.baseTime + q.radius ^ 2 < inkSpotsTerminalTime eta q := by
      rw [inkSpotsTerminalTime_eq]
      have hr : 0 < q.radius ^ 2 := sq_pos_of_pos hq.1
      field_simp
      nlinarith
    have hsq : zeta ^ 2 < 1 := by
      nlinarith [mul_pos hzeta0 (sub_pos.mpr hzeta1)]
    have hgap : 0 < inkSpotsTerminalTime eta q -
        (q.baseTime + q.radius ^ 2) := sub_pos.mpr hsource
    nlinarith [mul_pos (sq_pos_of_pos hzeta0) hgap]
  constructor
  · exact isOpen_Ioo
  constructor
  · exact ordConnected_Ioo
  · intro t ht
    have himage : t ∈ inkSpotsTimeContraction eta zeta q ''
        windForwardInterval eta q := by
      rw [inkSpotsTimeContraction_forwardInterval hzeta0]
      exact ht
    rcases himage with ⟨s, hs, rfl⟩
    have htime : (inkSpotsTimeContraction eta zeta q s, q.center) ∈
        inkSpotsQ2TimeContracted eta zeta q := by
      refine ⟨⟨s, hs, rfl⟩, ?_, ?_⟩
      · intro i
        simp only [sub_self, abs_zero]
        exact mul_pos (by norm_num) hq.1
      · exact strictDense_center_mem_unit_velocityCube hq
    have hq2 := inkSpotsQ2TimeContracted_subset_Q2 hzeta0 hzeta1 htime
    rw [mem_inkSpotsQ2_iff] at hq2
    rw [windAmbientTime, mem_Ioo]
    exact (windForwardInterval_eligible heta hq).2.2.2 ⟨hq2.1, hq2.2.1⟩

private theorem hotTimeExpansion_contractedInterval {d : ℕ}
    {Gamma : Set (TimeVelocity d)} {xi eta zeta : ℝ} {q : InkSpotsBox d}
    (heta : 0 < eta) (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1)
    (hq : inkSpotsStrictDense Gamma xi q) :
    rightEndpointExpansion 0 (zeta ^ 2)⁻¹
        (inkSpotsTimeContraction eta zeta q '' windForwardInterval eta q) =
      windForwardInterval eta q := by
  rw [inkSpotsTimeContraction_forwardInterval hzeta0]
  unfold rightEndpointExpansion windForwardInterval
  have hsource : q.baseTime + q.radius ^ 2 < inkSpotsTerminalTime eta q := by
    rw [inkSpotsTerminalTime_eq]
    have hr : 0 < q.radius ^ 2 := sq_pos_of_pos hq.1
    field_simp [ne_of_gt heta]
    nlinarith
  have hcontracted :
      inkSpotsTerminalTime eta q - zeta ^ 2 *
          (inkSpotsTerminalTime eta q - (q.baseTime + q.radius ^ 2)) <
        inkSpotsTerminalTime eta q := by
    have hgap : 0 < inkSpotsTerminalTime eta q -
        (q.baseTime + q.radius ^ 2) := sub_pos.mpr hsource
    nlinarith [mul_pos (sq_pos_of_pos hzeta0) hgap]
  rw [csInf_Ioo hcontracted, csSup_Ioo hcontracted]
  congr 1
  rw [max_eq_right]
  · field_simp
    ring
  · have hsq1 : zeta ^ 2 < 1 := by
      nlinarith [mul_pos hzeta0 (sub_pos.mpr hzeta1)]
    have hbase : 0 ≤ q.baseTime := strictDense_baseTime_nonneg hq
    have hidentity : inkSpotsTerminalTime eta q - (zeta ^ 2)⁻¹ *
        (inkSpotsTerminalTime eta q -
          (inkSpotsTerminalTime eta q - zeta ^ 2 *
            (inkSpotsTerminalTime eta q - (q.baseTime + q.radius ^ 2)))) =
        q.baseTime + q.radius ^ 2 := by
      field_simp [ne_of_gt (sq_pos_of_pos hzeta0)]
      ring
    rw [hidentity]
    exact add_nonneg hbase (sq_nonneg _)

private theorem timeSection_inkSpotsD2_subset_expanded_hotTimeSections {d : ℕ}
    (Gamma : Set (TimeVelocity d)) (xi eta zeta : ℝ) (heta : 0 < eta)
    (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1) (v : PDE.Vec d) :
    timeSection (inkSpotsD2 Gamma xi eta) v ⊆
      ⋃₀ (rightEndpointExpansion 0 (zeta ^ 2)⁻¹ ''
        hotTimeSectionFamily Gamma xi eta zeta v) := by
  intro t ht
  rw [timeSection, inkSpotsD2] at ht
  rcases mem_iUnion.1 ht with ⟨q, ht⟩
  rcases mem_iUnion.1 ht with ⟨hq, ht⟩
  rw [mem_inkSpotsQ2_iff] at ht
  refine mem_sUnion.2 ⟨rightEndpointExpansion 0 (zeta ^ 2)⁻¹
      (inkSpotsTimeContraction eta zeta q '' windForwardInterval eta q), ?_,
      ?_⟩
  exact ⟨inkSpotsTimeContraction eta zeta q '' windForwardInterval eta q,
    ⟨q, hq, ht.2.2.1, ht.2.2.2, rfl⟩, rfl⟩
  rw [hotTimeExpansion_contractedInterval heta hzeta0 hzeta1 hq]
  exact ⟨ht.1, ht.2.1⟩

private theorem sUnion_hotTimeSectionFamily_bounded {d : ℕ}
    (Gamma : Set (TimeVelocity d)) (xi eta zeta : ℝ) (heta : 0 < eta)
    (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1) (v : PDE.Vec d) :
    Bornology.IsBounded (⋃₀ hotTimeSectionFamily Gamma xi eta zeta v) := by
  apply (Metric.isBounded_Ioo 0 (1 + 4 / eta)).subset
  refine sUnion_subset fun I hI => ?_
  rcases hI with ⟨q, hq, _, _, rfl⟩
  exact (hotTimeInterval_eligible heta hzeta0 hzeta1 hq).2.2.2

private theorem volume_timeSection_inkSpotsD2_le_zeta_sq_inv_mul_timeContracted
    {d : ℕ} (Gamma : Set (TimeVelocity d)) (xi eta zeta : ℝ) (heta : 0 < eta)
    (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1) (v : PDE.Vec d) :
    volume (timeSection (inkSpotsD2 Gamma xi eta) v) ≤
      ENNReal.ofReal ((zeta ^ 2)⁻¹) *
        volume (timeSection (inkSpotsD2TimeContractedUnion Gamma xi eta zeta) v) := by
  have hsq0 : 0 < zeta ^ 2 := sq_pos_of_pos hzeta0
  have hsq1 : zeta ^ 2 < 1 := by
    nlinarith [mul_pos hzeta0 (sub_pos.mpr hzeta1)]
  calc
    volume (timeSection (inkSpotsD2 Gamma xi eta) v) ≤
        volume (⋃₀ (rightEndpointExpansion 0 (zeta ^ 2)⁻¹ ''
          hotTimeSectionFamily Gamma xi eta zeta v)) :=
      measure_mono (timeSection_inkSpotsD2_subset_expanded_hotTimeSections
        Gamma xi eta zeta heta hzeta0 hzeta1 v)
    _ ≤ ENNReal.ofReal ((zeta ^ 2)⁻¹) *
        volume (⋃₀ hotTimeSectionFamily Gamma xi eta zeta v) :=
      volume_sUnion_rightEndpointExpansion ((one_lt_inv₀ hsq0).2 hsq1) _
        (fun I hI => by
          rcases hI with ⟨q, hq, _, _, rfl⟩
          exact hotTimeInterval_eligible heta hzeta0 hzeta1 hq)
        (sUnion_hotTimeSectionFamily_bounded Gamma xi eta zeta heta hzeta0 hzeta1 v)
    _ = ENNReal.ofReal ((zeta ^ 2)⁻¹) *
        volume (timeSection (inkSpotsD2TimeContractedUnion Gamma xi eta zeta) v) := by
      rw [timeSection_inkSpotsD2TimeContractedUnion_eq_sUnion_hotTimeSectionFamily]

private theorem isOpen_inkSpotsQ2TimeContracted {d : ℕ} {eta zeta : ℝ}
    (q : InkSpotsBox d) (hzeta0 : 0 < zeta) :
    IsOpen (inkSpotsQ2TimeContracted eta zeta q) := by
  rw [inkSpotsQ2TimeContracted, inkSpotsTimeContraction_forwardInterval hzeta0]
  exact isOpen_Ioo.prod ((isOpen_velocityCube _ _).inter (isOpen_velocityCube _ _))

private theorem isOpen_inkSpotsD2TimeContractedUnion {d : ℕ}
    (Gamma : Set (TimeVelocity d)) (xi eta zeta : ℝ) (hzeta0 : 0 < zeta) :
    IsOpen (inkSpotsD2TimeContractedUnion Gamma xi eta zeta) := by
  rw [inkSpotsD2TimeContractedUnion]
  apply isOpen_iUnion
  intro q
  apply isOpen_iUnion
  intro _
  exact isOpen_inkSpotsQ2TimeContracted q hzeta0

private theorem volume_inkSpotsD2_le_zeta_sq_inv_mul_timeContracted {d : ℕ}
    (Gamma : Set (TimeVelocity d)) (xi eta zeta : ℝ) (heta : 0 < eta)
    (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1) :
    volume (inkSpotsD2 Gamma xi eta) ≤
      ENNReal.ofReal ((zeta ^ 2)⁻¹) *
        volume (inkSpotsD2TimeContractedUnion Gamma xi eta zeta) := by
  rw [volume_eq_lintegral_timeSection _ (measurableSet_inkSpotsD2 Gamma xi eta),
    volume_eq_lintegral_timeSection _
      (isOpen_inkSpotsD2TimeContractedUnion Gamma xi eta zeta hzeta0).measurableSet]
  calc
    (∫⁻ v, volume (timeSection (inkSpotsD2 Gamma xi eta) v)) ≤
        ∫⁻ v, ENNReal.ofReal ((zeta ^ 2)⁻¹) *
          volume (timeSection (inkSpotsD2TimeContractedUnion Gamma xi eta zeta) v) :=
      lintegral_mono fun v =>
        volume_timeSection_inkSpotsD2_le_zeta_sq_inv_mul_timeContracted
          Gamma xi eta zeta heta hzeta0 hzeta1 v
    _ = ENNReal.ofReal ((zeta ^ 2)⁻¹) *
        ∫⁻ v, volume (timeSection (inkSpotsD2TimeContractedUnion Gamma xi eta zeta) v) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-! The remaining contractions are deliberately staged by prefix.  Keeping
the family of boxes under the union at every stage is essential: different
boxes meeting the same section have different velocity centres. -/

private def inkSpotsVelocityPrefixContraction {d : Nat}
    (q : InkSpotsBox d) (zeta : Real) (k : Nat) (v : PDE.Vec d) : PDE.Vec d :=
  fun j => if j.1 < k then q.center j + zeta * (v j - q.center j) else v j

private def inkSpotsQ2PrefixContracted {d : Nat}
    (eta zeta : Real) (k : Nat) (q : InkSpotsBox d) : Set (TimeVelocity d) :=
  {z | ∃ y ∈ inkSpotsQ2 eta q,
    z.1 = inkSpotsTimeContraction eta zeta q y.1 ∧
      z.2 = inkSpotsVelocityPrefixContraction q zeta k y.2}

private def inkSpotsD2PrefixContractedUnion {d : Nat}
    (Gamma : Set (TimeVelocity d)) (xi eta zeta : Real) (k : Nat) :
    Set (TimeVelocity d) :=
  ⋃ q ∈ inkSpotsDenseBoxes Gamma xi, inkSpotsQ2PrefixContracted eta zeta k q

private theorem inkSpotsQ2PrefixContracted_zero_eq_timeContracted {d : Nat}
    (eta zeta : Real) (q : InkSpotsBox d) :
    inkSpotsQ2PrefixContracted eta zeta 0 q = inkSpotsQ2TimeContracted eta zeta q := by
  ext z
  constructor
  · rintro ⟨y, hy, ht, hv⟩
    rcases y with ⟨t, v⟩
    rw [mem_inkSpotsQ2_iff] at hy
    have hzv : z.2 = v := by
      funext j
      simpa only [inkSpotsVelocityPrefixContraction, Nat.not_lt_zero, if_false]
        using congrFun hv j
    refine ⟨⟨t, ⟨hy.1, hy.2.1⟩, ht.symm⟩, ?_, ?_⟩
    · rw [hzv]
      exact hy.2.2.1
    · rw [hzv]
      exact hy.2.2.2
  · rintro ⟨htime, hcenter, hunit⟩
    rcases htime with ⟨t, ht, htime⟩
    refine ⟨(t, z.2), ?_, htime.symm, ?_⟩
    · rw [mem_inkSpotsQ2_iff]
      exact ⟨ht.1, ht.2, hcenter, hunit⟩
    · funext j
      simp only [inkSpotsVelocityPrefixContraction, Nat.not_lt_zero, if_false]

private theorem inkSpotsD2PrefixContractedUnion_zero_eq_timeContracted {d : Nat}
    (Gamma : Set (TimeVelocity d)) (xi eta zeta : Real) :
    inkSpotsD2PrefixContractedUnion Gamma xi eta zeta 0 =
      inkSpotsD2TimeContractedUnion Gamma xi eta zeta := by
  simp only [inkSpotsD2PrefixContractedUnion, inkSpotsD2TimeContractedUnion,
    inkSpotsQ2PrefixContracted_zero_eq_timeContracted]

private theorem inkSpotsQ2PrefixContracted_eq_Q3 {d : Nat}
    (eta zeta : Real) (q : InkSpotsBox d) :
    inkSpotsQ2PrefixContracted eta zeta d q = inkSpotsQ3 eta zeta q := by
  ext z
  constructor
  · rintro ⟨y, hy, ht, hv⟩
    rw [mem_inkSpotsQ3_iff]
    refine ⟨y, hy, ?_⟩
    apply Prod.ext
    · exact ht.symm
    · funext j
      have hj : j.1 < d := j.isLt
      rw [hv]
      dsimp [inkSpotsContraction]
      rw [inkSpotsVelocityPrefixContraction, if_pos hj]
  · rw [mem_inkSpotsQ3_iff]
    rintro ⟨y, hy, hcontraction⟩
    refine ⟨y, hy, ?_, ?_⟩
    · simpa only [inkSpotsContraction, inkSpotsTimeContraction] using
        congrArg Prod.fst hcontraction.symm
    · have hv := congrArg Prod.snd hcontraction.symm
      funext j
      have hj : j.1 < d := j.isLt
      rw [hv]
      dsimp [inkSpotsContraction]
      rw [inkSpotsVelocityPrefixContraction, if_pos hj]

private theorem inkSpotsD2PrefixContractedUnion_eq_D3 {d : Nat}
    (Gamma : Set (TimeVelocity d)) (xi eta zeta : Real) :
    inkSpotsD2PrefixContractedUnion Gamma xi eta zeta d = inkSpotsD3 Gamma xi eta zeta := by
  simp only [inkSpotsD2PrefixContractedUnion, inkSpotsD3,
    inkSpotsQ2PrefixContracted_eq_Q3]

private def inkSpotsAffineHomeomorph (c zeta : Real) (hzeta : zeta ≠ 0) :
    Real ≃ₜ Real :=
  (Homeomorph.addLeft (-c)).trans
    ((Homeomorph.smulOfNeZero zeta hzeta).trans (Homeomorph.addLeft c))

private theorem inkSpotsAffineHomeomorph_apply (c zeta : Real) (hzeta : zeta ≠ 0)
    (x : Real) :
    inkSpotsAffineHomeomorph c zeta hzeta x = c + zeta * (x - c) := by
  simp [inkSpotsAffineHomeomorph, Homeomorph.addLeft, Homeomorph.smulOfNeZero]
  ring

private def inkSpotsPrefixHomeomorph {d : Nat} (eta zeta : Real) (k : Nat)
    (q : InkSpotsBox d) (hzeta : zeta ≠ 0) : TimeVelocity d ≃ₜ TimeVelocity d :=
  (inkSpotsAffineHomeomorph (inkSpotsTerminalTime eta q) (zeta ^ 2)
    (pow_ne_zero _ hzeta)).prodCongr
    (Homeomorph.piCongrRight fun j =>
      if _ : j.1 < k then inkSpotsAffineHomeomorph (q.center j) zeta hzeta
      else Homeomorph.refl Real)

private theorem inkSpotsPrefixHomeomorph_apply {d : Nat} (eta zeta : Real) (k : Nat)
    (q : InkSpotsBox d) (hzeta : zeta ≠ 0) (y : TimeVelocity d) :
    inkSpotsPrefixHomeomorph eta zeta k q hzeta y =
      (inkSpotsTimeContraction eta zeta q y.1,
        inkSpotsVelocityPrefixContraction q zeta k y.2) := by
  apply Prod.ext
  · change inkSpotsAffineHomeomorph (inkSpotsTerminalTime eta q) (zeta ^ 2)
      (pow_ne_zero _ hzeta) y.1 = _
    rw [show inkSpotsTimeContraction eta zeta q y.1 =
      inkSpotsTerminalTime eta q + zeta ^ 2 *
        (y.1 - inkSpotsTerminalTime eta q) by
      unfold inkSpotsTimeContraction
      ring]
    exact inkSpotsAffineHomeomorph_apply _ _ _ _
  · funext j
    change (Homeomorph.piCongrRight fun l =>
      if _ : l.1 < k then inkSpotsAffineHomeomorph (q.center l) zeta hzeta
      else Homeomorph.refl Real) y.2 j =
        inkSpotsVelocityPrefixContraction q zeta k y.2 j
    rw [Homeomorph.piCongrRight_apply]
    by_cases hj : j.1 < k
    · rw [dif_pos hj, inkSpotsAffineHomeomorph_apply]
      simp only [inkSpotsVelocityPrefixContraction, if_pos hj]
    · rw [dif_neg hj]
      simp only [Homeomorph.refl_apply, inkSpotsVelocityPrefixContraction, if_neg hj]
      rfl

private theorem inkSpotsQ2PrefixContracted_eq_homeomorph_image {d : Nat}
    (eta zeta : Real) (k : Nat) (q : InkSpotsBox d) (hzeta : zeta ≠ 0) :
    inkSpotsQ2PrefixContracted eta zeta k q =
      inkSpotsPrefixHomeomorph eta zeta k q hzeta '' inkSpotsQ2 eta q := by
  ext z
  constructor
  · rintro ⟨y, hy, ht, hv⟩
    refine ⟨y, hy, ?_⟩
    rw [inkSpotsPrefixHomeomorph_apply]
    exact Prod.ext ht.symm hv.symm
  · rintro ⟨y, hy, hzy⟩
    refine ⟨y, hy, ?_, ?_⟩
    have hcomponents := congrArg Prod.fst hzy
    rw [inkSpotsPrefixHomeomorph_apply] at hcomponents
    exact hcomponents.symm
    have hcomponents := congrArg Prod.snd hzy
    rw [inkSpotsPrefixHomeomorph_apply] at hcomponents
    exact hcomponents.symm

private theorem isOpen_inkSpotsQ2PrefixContracted {d : Nat} {eta zeta : Real}
    (k : Nat) (q : InkSpotsBox d) (hzeta0 : 0 < zeta) :
    IsOpen (inkSpotsQ2PrefixContracted eta zeta k q) := by
  rw [inkSpotsQ2PrefixContracted_eq_homeomorph_image eta zeta k q hzeta0.ne']
  exact (inkSpotsPrefixHomeomorph eta zeta k q hzeta0.ne').isOpenMap _
    (isOpen_inkSpotsQ2 eta q)

private theorem isOpen_inkSpotsD2PrefixContractedUnion {d : Nat}
    (Gamma : Set (TimeVelocity d)) (xi eta zeta : Real) (k : Nat)
    (hzeta0 : 0 < zeta) :
    IsOpen (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta k) := by
  rw [inkSpotsD2PrefixContractedUnion]
  apply isOpen_iUnion
  intro q
  apply isOpen_iUnion
  intro _
  exact isOpen_inkSpotsQ2PrefixContracted k q hzeta0

private def inkSpotsVelocitySectionPoint {d : Nat} (j : Fin d) (x : Real)
    (w : Fin d → Real) : TimeVelocity d :=
  (timeVelocityCoordinateEquiv d).symm
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => Real)
      (Fin.succ j)).symm (x, w))

private theorem mem_timeVelocityCoordinateSection_succ_iff {d : Nat} (j : Fin d)
    (S : Set (TimeVelocity d)) (w : Fin d → Real) (x : Real) :
    x ∈ timeVelocityCoordinateSection d (Fin.succ j) S w ↔
      inkSpotsVelocitySectionPoint j x w ∈ S := by
  let e := timeVelocityCoordinateEquiv d
  let ei := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => Real)
    (Fin.succ j)
  change ei.symm (x, w) ∈ e '' S ↔ _
  constructor
  · rintro ⟨z, hz, heq⟩
    have hz_eq : z = e.symm (ei.symm (x, w)) := by
      apply e.injective
      simpa using heq
    change e.symm (ei.symm (x, w)) ∈ S
    rw [← hz_eq]
    exact hz
  · intro hz
    refine ⟨e.symm (ei.symm (x, w)), hz, ?_⟩
    exact e.apply_symm_apply _

private theorem timeVelocityCoordinateEquiv_sectionPoint {d : Nat} (j : Fin d)
    (x : Real) (w : Fin d → Real) :
    timeVelocityCoordinateEquiv d (inkSpotsVelocitySectionPoint j x w) =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => Real)
        (Fin.succ j)).symm (x, w) := by
  simp [inkSpotsVelocitySectionPoint]

private theorem sectionPoint_velocity_eq {d : Nat} (j : Fin d) (x : Real)
    (w : Fin d → Real) : (inkSpotsVelocitySectionPoint j x w).2 j = x := by
  simp [inkSpotsVelocitySectionPoint, timeVelocityCoordinateEquiv, Fin.tail]

private theorem sectionPoint_velocity_eq_of_ne {d : Nat} (j l : Fin d) (x y : Real)
    (w : Fin d → Real) (h : l ≠ j) :
    (inkSpotsVelocitySectionPoint j x w).2 l =
      (inkSpotsVelocitySectionPoint j y w).2 l := by
  change (timeVelocityCoordinateEquiv d (inkSpotsVelocitySectionPoint j x w))
      (Fin.succ l) =
    (timeVelocityCoordinateEquiv d (inkSpotsVelocitySectionPoint j y w))
      (Fin.succ l)
  rw [timeVelocityCoordinateEquiv_sectionPoint,
    timeVelocityCoordinateEquiv_sectionPoint]
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk]
  obtain ⟨u, hu⟩ := Fin.exists_succAbove_eq
    (show Fin.succ l ≠ Fin.succ j by simpa)
  rw [← hu, Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]

private theorem sectionPoint_time_eq {d : Nat} (j : Fin d) (x y : Real)
    (w : Fin d → Real) :
    (inkSpotsVelocitySectionPoint j x w).1 =
      (inkSpotsVelocitySectionPoint j y w).1 := by
  change (timeVelocityCoordinateEquiv d (inkSpotsVelocitySectionPoint j x w)) 0 =
    (timeVelocityCoordinateEquiv d (inkSpotsVelocitySectionPoint j y w)) 0
  rw [timeVelocityCoordinateEquiv_sectionPoint,
    timeVelocityCoordinateEquiv_sectionPoint]
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk]
  rw [Fin.insertNth_apply_below (by simp), Fin.insertNth_apply_below (by simp)]

private def inkSpotsPrefixCoordinateSectionFamily {d : Nat}
    (Gamma : Set (TimeVelocity d)) (xi eta zeta : Real) (k : Nat) (j : Fin d)
    (w : Fin d → Real) : Set (Set Real) :=
  {I | ∃ q ∈ inkSpotsDenseBoxes Gamma xi,
    I = timeVelocityCoordinateSection d (Fin.succ j)
      (inkSpotsQ2PrefixContracted eta zeta k q) w ∧ I.Nonempty}

private theorem timeVelocityCoordinateSection_prefixUnion_eq_sUnion_family {d : Nat}
    (Gamma : Set (TimeVelocity d)) (xi eta zeta : Real) (k : Nat) (j : Fin d)
    (w : Fin d → Real) :
    timeVelocityCoordinateSection d (Fin.succ j)
        (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta k) w =
      ⋃₀ inkSpotsPrefixCoordinateSectionFamily Gamma xi eta zeta k j w := by
  ext x
  rw [mem_timeVelocityCoordinateSection_succ_iff]
  constructor
  · intro hx
    rw [inkSpotsD2PrefixContractedUnion] at hx
    rcases mem_iUnion.1 hx with ⟨q, hx⟩
    rcases mem_iUnion.1 hx with ⟨hq, hx⟩
    refine mem_sUnion.2 ⟨timeVelocityCoordinateSection d (Fin.succ j)
      (inkSpotsQ2PrefixContracted eta zeta k q) w, ?_, ?_⟩
    · refine ⟨q, hq, rfl, ⟨x, ?_⟩⟩
      rw [mem_timeVelocityCoordinateSection_succ_iff]
      exact hx
    · rw [mem_timeVelocityCoordinateSection_succ_iff]
      exact hx
  · rintro hx
    rcases mem_sUnion.1 hx with ⟨I, hI, hxI⟩
    rcases hI with ⟨q, hq, rfl, _⟩
    rw [mem_timeVelocityCoordinateSection_succ_iff] at hxI
    rw [inkSpotsD2PrefixContractedUnion]
    exact mem_iUnion.2 ⟨q, mem_iUnion.2 ⟨hq, hxI⟩⟩

private def inkSpotsHotCoordinateInterval {d : Nat} (q : InkSpotsBox d)
    (j : Fin d) : Set Real :=
  Ioo (q.center j - 3 * q.radius) (q.center j + 3 * q.radius) ∩ Ioo (-1) 1

private theorem inkSpotsHotCoordinateInterval_eligible {d : Nat}
    {Gamma : Set (TimeVelocity d)} {xi : Real} {q : InkSpotsBox d}
    (hq : q ∈ inkSpotsDenseBoxes Gamma xi) (j : Fin d) :
    IsOpenSubinterval (Ioo (-1 : Real) 1) (inkSpotsHotCoordinateInterval q j) := by
  have hc := strictDense_center_coord_bounds hq j
  have hr : 0 < q.radius := hq.1
  refine ⟨⟨q.center j, ⟨?_, hc⟩⟩, isOpen_Ioo.inter isOpen_Ioo,
    ordConnected_Ioo.inter ordConnected_Ioo, inter_subset_right⟩
  constructor <;> nlinarith

private theorem section_prefix_eq_hotInterval_of_nonempty {d : Nat}
    (eta zeta : Real) (q : InkSpotsBox d) (j : Fin d) (w : Fin d → Real)
    (hnonempty : (timeVelocityCoordinateSection d (Fin.succ j)
      (inkSpotsQ2PrefixContracted eta zeta j.1 q) w).Nonempty) :
    timeVelocityCoordinateSection d (Fin.succ j)
        (inkSpotsQ2PrefixContracted eta zeta j.1 q) w =
      inkSpotsHotCoordinateInterval q j := by
  obtain ⟨x₀, hx₀⟩ := hnonempty
  rw [mem_timeVelocityCoordinateSection_succ_iff] at hx₀
  rcases hx₀ with ⟨y₀, hy₀, ht₀, hv₀⟩
  have hy₀' := hy₀
  rw [mem_inkSpotsQ2_iff] at hy₀'
  ext x
  constructor
  · rw [mem_timeVelocityCoordinateSection_succ_iff]
    rintro ⟨y, hy, _, hv⟩
    rw [mem_inkSpotsQ2_iff] at hy
    have hcoord := congrFun hv j
    simp only [sectionPoint_velocity_eq, inkSpotsVelocityPrefixContraction,
      lt_self_iff_false, if_false] at hcoord
    rw [inkSpotsHotCoordinateInterval, hcoord]
    have hc := abs_lt.mp (mem_velocityCube_iff.mp hy.2.2.1 j)
    have hu : -1 < y.2 j ∧ y.2 j < 1 := by
      simpa only [Pi.zero_apply, sub_zero] using
        abs_lt.mp (mem_velocityCube_iff.mp hy.2.2.2 j)
    exact ⟨⟨by linarith [hc.1], by linarith [hc.2]⟩, hu⟩
  · intro hx
    rw [inkSpotsHotCoordinateInterval] at hx
    rw [mem_timeVelocityCoordinateSection_succ_iff]
    let v : PDE.Vec d := fun l => if l = j then x else y₀.2 l
    have hvcenter : v ∈ velocityCube q.center (3 * q.radius) := by
      rw [mem_velocityCube_iff]
      intro l
      by_cases hlj : l = j
      · subst l
        simp only [v, if_pos]
        exact abs_lt.mpr ⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩
      · simpa only [v, if_neg hlj] using mem_velocityCube_iff.mp hy₀'.2.2.1 l
    have hvunit : v ∈ velocityCube 0 1 := by
      rw [mem_velocityCube_iff]
      intro l
      by_cases hlj : l = j
      · subst l
        simpa only [v, if_pos, Pi.zero_apply, sub_zero] using abs_lt.mpr hx.2
      · simpa only [v, if_neg hlj] using mem_velocityCube_iff.mp hy₀'.2.2.2 l
    refine ⟨(y₀.1, v), ?_, ?_, ?_⟩
    · rw [mem_inkSpotsQ2_iff]
      exact ⟨hy₀'.1, hy₀'.2.1, hvcenter, hvunit⟩
    · calc
        (inkSpotsVelocitySectionPoint j x w).1 =
            (inkSpotsVelocitySectionPoint j x₀ w).1 := sectionPoint_time_eq _ _ _ _
        _ = inkSpotsTimeContraction eta zeta q y₀.1 := ht₀
    · funext l
      by_cases hlj : l = j
      · subst l
        simp only [sectionPoint_velocity_eq, inkSpotsVelocityPrefixContraction,
          lt_self_iff_false, if_false, v, if_pos]
      · calc
          (inkSpotsVelocitySectionPoint j x w).2 l =
              (inkSpotsVelocitySectionPoint j x₀ w).2 l :=
                sectionPoint_velocity_eq_of_ne _ _ _ _ _ hlj
          _ = inkSpotsVelocityPrefixContraction q zeta j.1 y₀.2 l := congrFun hv₀ l
          _ = inkSpotsVelocityPrefixContraction q zeta j.1 v l := by
            simp only [inkSpotsVelocityPrefixContraction, v, if_neg hlj]

private theorem section_prefix_succ_eq_contraction_image_of_nonempty {d : Nat}
    (eta zeta : Real) (q : InkSpotsBox d) (j : Fin d) (w : Fin d → Real)
    (hnonempty : (timeVelocityCoordinateSection d (Fin.succ j)
      (inkSpotsQ2PrefixContracted eta zeta j.1 q) w).Nonempty) :
    timeVelocityCoordinateSection d (Fin.succ j)
        (inkSpotsQ2PrefixContracted eta zeta (j.1 + 1) q) w =
      centeredCoordinateContraction (q.center j) zeta ''
        inkSpotsHotCoordinateInterval q j := by
  obtain ⟨x₀, hx₀⟩ := hnonempty
  rw [mem_timeVelocityCoordinateSection_succ_iff] at hx₀
  rcases hx₀ with ⟨y₀, hy₀, ht₀, hv₀⟩
  have hy₀' := hy₀
  rw [mem_inkSpotsQ2_iff] at hy₀'
  ext x
  constructor
  · rw [mem_timeVelocityCoordinateSection_succ_iff]
    rintro ⟨y, hy, _, hv⟩
    rw [mem_inkSpotsQ2_iff] at hy
    refine ⟨y.2 j, ?_, ?_⟩
    · rw [inkSpotsHotCoordinateInterval]
      have hc := abs_lt.mp (mem_velocityCube_iff.mp hy.2.2.1 j)
      have hu : -1 < y.2 j ∧ y.2 j < 1 := by
        simpa only [Pi.zero_apply, sub_zero] using
          abs_lt.mp (mem_velocityCube_iff.mp hy.2.2.2 j)
      exact ⟨⟨by linarith [hc.1], by linarith [hc.2]⟩, hu⟩
    · have hcoord := congrFun hv j
      simp only [sectionPoint_velocity_eq, inkSpotsVelocityPrefixContraction,
        Nat.lt_succ_self, if_true] at hcoord
      exact hcoord.symm
  · rintro ⟨u, hu, rfl⟩
    rw [inkSpotsHotCoordinateInterval] at hu
    rw [mem_timeVelocityCoordinateSection_succ_iff]
    let v : PDE.Vec d := fun l => if l = j then u else y₀.2 l
    have hvcenter : v ∈ velocityCube q.center (3 * q.radius) := by
      rw [mem_velocityCube_iff]
      intro l
      by_cases hlj : l = j
      · subst l
        simp only [v, if_pos]
        exact abs_lt.mpr ⟨by linarith [hu.1.1], by linarith [hu.1.2]⟩
      · simpa only [v, if_neg hlj] using mem_velocityCube_iff.mp hy₀'.2.2.1 l
    have hvunit : v ∈ velocityCube 0 1 := by
      rw [mem_velocityCube_iff]
      intro l
      by_cases hlj : l = j
      · subst l
        simpa only [v, if_pos, Pi.zero_apply, sub_zero] using abs_lt.mpr hu.2
      · simpa only [v, if_neg hlj] using mem_velocityCube_iff.mp hy₀'.2.2.2 l
    refine ⟨(y₀.1, v), ?_, ?_, ?_⟩
    · rw [mem_inkSpotsQ2_iff]
      exact ⟨hy₀'.1, hy₀'.2.1, hvcenter, hvunit⟩
    · calc
        (inkSpotsVelocitySectionPoint j
            (centeredCoordinateContraction (q.center j) zeta u) w).1 =
            (inkSpotsVelocitySectionPoint j x₀ w).1 := sectionPoint_time_eq _ _ _ _
        _ = inkSpotsTimeContraction eta zeta q y₀.1 := ht₀
    · funext l
      by_cases hlj : l = j
      · subst l
        simp only [sectionPoint_velocity_eq, inkSpotsVelocityPrefixContraction,
          Nat.lt_succ_self, v, if_pos, centeredCoordinateContraction]
      · calc
          (inkSpotsVelocitySectionPoint j
              (centeredCoordinateContraction (q.center j) zeta u) w).2 l =
              (inkSpotsVelocitySectionPoint j x₀ w).2 l :=
                sectionPoint_velocity_eq_of_ne _ _ _ _ _ hlj
          _ = inkSpotsVelocityPrefixContraction q zeta j.1 y₀.2 l := congrFun hv₀ l
          _ = inkSpotsVelocityPrefixContraction q zeta (j.1 + 1) v l := by
            by_cases hl : l.1 < j.1
            · have hls : l.1 < j.1 + 1 := hl.trans (Nat.lt_succ_self _)
              simp only [inkSpotsVelocityPrefixContraction, if_pos hl, if_pos hls,
                v, if_neg hlj]
            · have hls : ¬ l.1 < j.1 + 1 := by omega
              simp only [inkSpotsVelocityPrefixContraction, if_neg hl, if_neg hls,
                v, if_neg hlj]

private theorem section_prefix_nonempty_of_succ_nonempty {d : Nat}
    (eta zeta : Real) (q : InkSpotsBox d) (j : Fin d) (w : Fin d → Real)
    (h : (timeVelocityCoordinateSection d (Fin.succ j)
      (inkSpotsQ2PrefixContracted eta zeta (j.1 + 1) q) w).Nonempty) :
    (timeVelocityCoordinateSection d (Fin.succ j)
      (inkSpotsQ2PrefixContracted eta zeta j.1 q) w).Nonempty := by
  obtain ⟨x, hx⟩ := h
  rw [mem_timeVelocityCoordinateSection_succ_iff] at hx
  rcases hx with ⟨y, hy, ht, hv⟩
  refine ⟨y.2 j, ?_⟩
  rw [mem_timeVelocityCoordinateSection_succ_iff]
  refine ⟨y, hy, ?_, ?_⟩
  · exact (sectionPoint_time_eq j (y.2 j) x w).trans ht
  · funext l
    by_cases hlj : l = j
    · subst l
      simp only [sectionPoint_velocity_eq, inkSpotsVelocityPrefixContraction,
        lt_self_iff_false, if_false]
    · calc
        (inkSpotsVelocitySectionPoint j (y.2 j) w).2 l =
            (inkSpotsVelocitySectionPoint j x w).2 l :=
              sectionPoint_velocity_eq_of_ne _ _ _ _ _ hlj
        _ = inkSpotsVelocityPrefixContraction q zeta (j.1 + 1) y.2 l := congrFun hv l
        _ = inkSpotsVelocityPrefixContraction q zeta j.1 y.2 l := by
          by_cases hl : l.1 < j.1
          · have hls : l.1 < j.1 + 1 := hl.trans (Nat.lt_succ_self _)
            simp only [inkSpotsVelocityPrefixContraction, if_pos hl, if_pos hls]
          · have hls : ¬ l.1 < j.1 + 1 := by omega
            simp only [inkSpotsVelocityPrefixContraction, if_neg hl, if_neg hls]

private def hotVelocitySectionFamily {d : Nat}
    (Gamma : Set (TimeVelocity d)) (xi eta zeta : Real) (j : Fin d)
    (w : Fin d → Real) : Set (Set Real) :=
  {I | ∃ q ∈ inkSpotsDenseBoxes Gamma xi,
    (timeVelocityCoordinateSection d (Fin.succ j)
      (inkSpotsQ2PrefixContracted eta zeta j.1 q) w).Nonempty ∧
    I = centeredCoordinateContraction (q.center j) zeta ''
      inkSpotsHotCoordinateInterval q j}

private theorem section_prefix_succ_union_eq_sUnion_hotVelocityFamily {d : Nat}
    (Gamma : Set (TimeVelocity d)) (xi eta zeta : Real) (j : Fin d)
    (w : Fin d → Real) :
    timeVelocityCoordinateSection d (Fin.succ j)
        (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta (j.1 + 1)) w =
      ⋃₀ hotVelocitySectionFamily Gamma xi eta zeta j w := by
  rw [timeVelocityCoordinateSection_prefixUnion_eq_sUnion_family]
  ext x
  constructor
  · rintro hx
    rcases mem_sUnion.1 hx with ⟨I, ⟨q, hq, rfl, hne⟩, hxI⟩
    have hpre := section_prefix_nonempty_of_succ_nonempty eta zeta q j w hne
    rw [section_prefix_succ_eq_contraction_image_of_nonempty eta zeta q j w hpre] at hxI
    exact mem_sUnion.2 ⟨_, ⟨q, hq, hpre, rfl⟩, hxI⟩
  · rintro hx
    rcases mem_sUnion.1 hx with ⟨I, ⟨q, hq, hpre, rfl⟩, hxI⟩
    rw [← section_prefix_succ_eq_contraction_image_of_nonempty eta zeta q j w hpre]
      at hxI
    exact mem_sUnion.2 ⟨_, ⟨q, hq, rfl, ⟨x, hxI⟩⟩, hxI⟩

private theorem section_prefix_union_eq_sUnion_expanded_hotVelocityFamily {d : Nat}
    (Gamma : Set (TimeVelocity d)) (xi eta zeta : Real) (j : Fin d)
    (w : Fin d → Real) (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1) :
    timeVelocityCoordinateSection d (Fin.succ j)
        (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta j.1) w =
      ⋃₀ (boundaryShiftedMidpointExpansion zeta⁻¹ ''
        hotVelocitySectionFamily Gamma xi eta zeta j w) := by
  rw [timeVelocityCoordinateSection_prefixUnion_eq_sUnion_family]
  ext x
  constructor
  · rintro hx
    rcases mem_sUnion.1 hx with ⟨I, ⟨q, hq, rfl, hpre⟩, hxI⟩
    rw [section_prefix_eq_hotInterval_of_nonempty eta zeta q j w hpre] at hxI
    let K := centeredCoordinateContraction (q.center j) zeta ''
      inkSpotsHotCoordinateInterval q j
    have hrecover : boundaryShiftedMidpointExpansion zeta⁻¹ K =
        inkSpotsHotCoordinateInterval q j := by
      exact boundaryShiftedMidpointExpansion_image_centeredInterval_inter
        (q.center j) (3 * q.radius) zeta hzeta0 hzeta1
          (strictDense_center_coord_bounds hq j) (mul_pos (by norm_num) hq.1)
    exact mem_sUnion.2 ⟨boundaryShiftedMidpointExpansion zeta⁻¹ K,
      ⟨K, ⟨q, hq, hpre, rfl⟩, rfl⟩, by rw [hrecover]; exact hxI⟩
  · rintro hx
    rcases mem_sUnion.1 hx with ⟨E, ⟨K, ⟨q, hq, hpre, rfl⟩, rfl⟩, hxE⟩
    change x ∈ boundaryShiftedMidpointExpansion zeta⁻¹
      ((fun u : Real => q.center j + zeta * (u - q.center j)) ''
        (Ioo (q.center j - 3 * q.radius) (q.center j + 3 * q.radius) ∩ Ioo (-1) 1))
      at hxE
    rw [boundaryShiftedMidpointExpansion_image_centeredInterval_inter
      (q.center j) (3 * q.radius) zeta hzeta0 hzeta1
        (strictDense_center_coord_bounds hq j) (mul_pos (by norm_num) hq.1)] at hxE
    have hxJ : x ∈ inkSpotsHotCoordinateInterval q j := hxE
    rw [← section_prefix_eq_hotInterval_of_nonempty eta zeta q j w hpre] at hxJ
    exact mem_sUnion.2 ⟨_, ⟨q, hq, rfl, hpre⟩, hxJ⟩

private theorem hotVelocitySectionFamily_eligible {d : Nat}
    (Gamma : Set (TimeVelocity d)) (xi eta zeta : Real) (j : Fin d)
    (w : Fin d → Real) (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1) :
    ∀ I ∈ hotVelocitySectionFamily Gamma xi eta zeta j w,
      IsOpenSubinterval (Ioo (-1 : Real) 1) I := by
  rintro I ⟨q, hq, _, rfl⟩
  have hc := strictDense_center_coord_bounds hq j
  have hr : 0 < q.radius := hq.1
  exact (isClippedCoordinateInterval_centeredCoordinateContraction_image
    (q.center j) zeta hzeta0 hzeta1
      ⟨inkSpotsHotCoordinateInterval_eligible hq j,
        ⟨⟨by nlinarith, by nlinarith⟩, hc⟩⟩).1

private theorem volume_prefix_spatial_step {d : Nat}
    (Gamma : Set (TimeVelocity d)) (xi eta zeta : Real)
    (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1) {k : Nat} (hk : k < d) :
    volume (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta k) ≤
      ENNReal.ofReal zeta⁻¹ *
        volume (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta (k + 1)) := by
  let j : Fin d := ⟨k, hk⟩
  apply volume_timeVelocity_le_of_forall_volume_coordinateSection_le
    (Fin.succ j) _ _
    (isOpen_inkSpotsD2PrefixContractedUnion Gamma xi eta zeta k hzeta0).measurableSet
    (isOpen_inkSpotsD2PrefixContractedUnion Gamma xi eta zeta (k + 1)
      hzeta0).measurableSet zeta⁻¹
  intro w
  have hleft := section_prefix_union_eq_sUnion_expanded_hotVelocityFamily
    Gamma xi eta zeta j w hzeta0 hzeta1
  have hright := section_prefix_succ_union_eq_sUnion_hotVelocityFamily
    Gamma xi eta zeta j w
  have hvary := volume_sUnion_boundaryShiftedMidpointExpansion zeta⁻¹
    ((one_lt_inv₀ hzeta0).2 hzeta1)
    (hotVelocitySectionFamily Gamma xi eta zeta j w)
    (hotVelocitySectionFamily_eligible Gamma xi eta zeta j w hzeta0 hzeta1)
  change volume (timeVelocityCoordinateSection d (Fin.succ j)
      (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta j.1) w) ≤
    ENNReal.ofReal zeta⁻¹ * volume (timeVelocityCoordinateSection d (Fin.succ j)
      (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta (j.1 + 1)) w)
  rw [hleft, hright]
  exact hvary

private theorem volume_prefix_spatial_contraction {d : Nat}
    (Gamma : Set (TimeVelocity d)) (xi eta zeta : Real)
    (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1) (k : Nat) (hk : k ≤ d) :
    volume (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta 0) ≤
      (ENNReal.ofReal zeta⁻¹) ^ k *
        volume (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hklt : k < d := Nat.lt_of_succ_le hk
      calc
        volume (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta 0) ≤
            (ENNReal.ofReal zeta⁻¹) ^ k *
              volume (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta k) :=
          ih (Nat.le_of_succ_le hk)
        _ ≤ (ENNReal.ofReal zeta⁻¹) ^ k *
              (ENNReal.ofReal zeta⁻¹ *
                volume (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta (k + 1))) :=
          mul_le_mul_right (volume_prefix_spatial_step Gamma xi eta zeta
            hzeta0 hzeta1 hklt) _
        _ = (ENNReal.ofReal zeta⁻¹) ^ (k + 1) *
              volume (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta (k + 1)) := by
          rw [pow_succ]
          ac_rfl

private theorem inkSpotsQ2PrefixContracted_subset_Q2 {d : Nat}
    {Gamma : Set (TimeVelocity d)} {xi eta zeta : Real} {q : InkSpotsBox d}
    (hq : q ∈ inkSpotsDenseBoxes Gamma xi) (hzeta0 : 0 < zeta)
    (hzeta1 : zeta < 1) (k : Nat) :
    inkSpotsQ2PrefixContracted eta zeta k q ⊆ inkSpotsQ2 eta q := by
  rintro z ⟨y, hy, ht, hv⟩
  have hy' := hy
  rw [mem_inkSpotsQ2_iff] at hy'
  have htime : (z.1, y.2) ∈ inkSpotsQ2 eta q :=
    inkSpotsQ2TimeContracted_subset_Q2 hzeta0 hzeta1
      ⟨⟨y.1, ⟨hy'.1, hy'.2.1⟩, ht.symm⟩, hy'.2.2.1, hy'.2.2.2⟩
  rw [mem_inkSpotsQ2_iff] at htime ⊢
  refine ⟨htime.1, htime.2.1, ?_, ?_⟩
  · rw [mem_velocityCube_iff]
    intro l
    rw [hv, inkSpotsVelocityPrefixContraction]
    by_cases hl : l.1 < k
    · rw [if_pos hl]
      have hyc := mem_velocityCube_iff.mp hy'.2.2.1 l
      rw [show q.center l + zeta * (y.2 l - q.center l) - q.center l =
        zeta * (y.2 l - q.center l) by ring, abs_mul, abs_of_pos hzeta0]
      nlinarith [abs_nonneg (y.2 l - q.center l)]
    · rw [if_neg hl]
      exact mem_velocityCube_iff.mp hy'.2.2.1 l
  · rw [mem_velocityCube_iff]
    intro l
    rw [hv, inkSpotsVelocityPrefixContraction]
    by_cases hl : l.1 < k
    · rw [if_pos hl]
      have hc := strictDense_center_coord_bounds hq l
      have hyv : -1 < y.2 l ∧ y.2 l < 1 := by
        simpa only [Pi.zero_apply, sub_zero] using
          abs_lt.mp (mem_velocityCube_iff.mp hy'.2.2.2 l)
      rw [Pi.zero_apply, sub_zero, abs_lt]
      constructor <;> nlinarith
    · rw [if_neg hl]
      exact mem_velocityCube_iff.mp hy'.2.2.2 l

private theorem inkSpotsD3_subset_D2 {d : Nat}
    (Gamma : Set (TimeVelocity d)) (xi eta zeta : Real)
    (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1) :
    inkSpotsD3 Gamma xi eta zeta ⊆ inkSpotsD2 Gamma xi eta := by
  rw [← inkSpotsD2PrefixContractedUnion_eq_D3]
  intro z hz
  rw [inkSpotsD2PrefixContractedUnion] at hz
  rcases mem_iUnion.1 hz with ⟨q, hz⟩
  rcases mem_iUnion.1 hz with ⟨hq, hz⟩
  rw [inkSpotsD2]
  exact mem_iUnion.2 ⟨q, mem_iUnion.2 ⟨hq,
    inkSpotsQ2PrefixContracted_subset_Q2 hq hzeta0 hzeta1 d hz⟩⟩

private theorem isBounded_velocityCube {d : Nat} (v₀ : PDE.Vec d) (r : Real) :
    Bornology.IsBounded (velocityCube v₀ r) := by
  exact (isCompact_velocityClosedCube v₀ r).isBounded.subset
    (fun _ hv i => le_of_lt (hv i))

private theorem volume_inkSpotsD2_ne_top {d : Nat}
    (Gamma : Set (TimeVelocity d)) (xi eta : Real) (heta : 0 < eta) :
    volume (inkSpotsD2 Gamma xi eta) ≠ ∞ := by
  have hsubset : inkSpotsD2 Gamma xi eta ⊆ windAmbient d eta := by
    intro z hz
    rw [inkSpotsD2] at hz
    rcases mem_iUnion.1 hz with ⟨q, hz⟩
    rcases mem_iUnion.1 hz with ⟨hq, hz⟩
    exact inkSpotsQ2_subset_windAmbient heta hq hz
  apply ne_of_lt
  apply lt_of_le_of_lt (measure_mono hsubset)
  apply Bornology.IsBounded.measure_lt_top
  exact (Metric.isBounded_Ioo 0 (1 + 4 / eta)).prod
    (isBounded_velocityCube (0 : PDE.Vec d) 1)

private theorem hotWind_scalar_identity (zeta : Real) (hzeta : zeta ≠ 0) (d : Nat) :
    ((zeta ^ 2)⁻¹) * (zeta⁻¹) ^ d = zeta ^ (-((d : Int) + 2)) := by
  have htime : (zeta ^ 2)⁻¹ = zeta ^ (-2 : Int) :=
    (zpow_neg zeta (2 : Int)).symm
  have hspace : (zeta⁻¹) ^ d = zeta ^ (-(d : Int)) := by
    rw [inv_pow, ← zpow_natCast]
    exact (zpow_neg zeta (d : Int)).symm
  rw [htime, hspace, ← zpow_add₀ hzeta]
  congr 1
  omega

/-- Krylov--Safonov, Lemma 2.4 (hot wind): the forward source union is controlled by
its terminal contraction in time and every velocity coordinate. -/
theorem volume_inkSpotsD2_toReal_le_zeta_zpow_mul_D3
    {d : ℕ} (Gamma : Set (TimeVelocity d)) (xi eta zeta : ℝ)
    (heta : 0 < eta) (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1) :
    (volume (inkSpotsD2 Gamma xi eta)).toReal ≤
      zeta ^ (-((d : ℤ) + 2)) *
        (volume (inkSpotsD3 Gamma xi eta zeta)).toReal := by
  have htime := volume_inkSpotsD2_le_zeta_sq_inv_mul_timeContracted
    Gamma xi eta zeta heta hzeta0 hzeta1
  have hspace := volume_prefix_spatial_contraction
    Gamma xi eta zeta hzeta0 hzeta1 d le_rfl
  rw [inkSpotsD2PrefixContractedUnion_zero_eq_timeContracted,
    inkSpotsD2PrefixContractedUnion_eq_D3] at hspace
  have hmeasure : volume (inkSpotsD2 Gamma xi eta) ≤
      ENNReal.ofReal ((zeta ^ 2)⁻¹) *
        ((ENNReal.ofReal zeta⁻¹) ^ d *
          volume (inkSpotsD3 Gamma xi eta zeta)) := by
    calc
      volume (inkSpotsD2 Gamma xi eta) ≤
          ENNReal.ofReal ((zeta ^ 2)⁻¹) *
            volume (inkSpotsD2TimeContractedUnion Gamma xi eta zeta) := htime
      _ ≤ ENNReal.ofReal ((zeta ^ 2)⁻¹) *
          ((ENNReal.ofReal zeta⁻¹) ^ d *
            volume (inkSpotsD3 Gamma xi eta zeta)) :=
        mul_le_mul_right hspace _
  have hD3finite : volume (inkSpotsD3 Gamma xi eta zeta) ≠ ∞ :=
    ne_top_of_le_ne_top (volume_inkSpotsD2_ne_top Gamma xi eta heta)
      (measure_mono (inkSpotsD3_subset_D2 Gamma xi eta zeta hzeta0 hzeta1))
  have hfinite : ENNReal.ofReal ((zeta ^ 2)⁻¹) *
      ((ENNReal.ofReal zeta⁻¹) ^ d *
        volume (inkSpotsD3 Gamma xi eta zeta)) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hD3finite)
  have hreal := ENNReal.toReal_mono hfinite hmeasure
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (zeta ^ 2)⁻¹),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ zeta⁻¹), ← mul_assoc,
    hotWind_scalar_identity zeta hzeta0.ne' d] at hreal
  exact hreal

end HypoellipticAleksandrov.Parabolic

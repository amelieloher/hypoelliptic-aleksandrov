module

public import HypoellipticAleksandrov.Parabolic.PeakSelection
public import HypoellipticAleksandrov.Parabolic.ForwardPropagationGeometry

/-!
# Pure geometry for the local parabolic Harnack box

This module contains the fixed-box geometry used by the direct one-box
Krylov--Safonov Harnack argument.  In particular, the propagation corridors
end strictly before the terminal face of the open work box.
-/

@[expose] public section

open Filter Set

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/-- Times below the terminal face used to approach the normalized terminal value. -/
def localHarnackTerminalApprox (j : ℕ) : ℝ :=
  8 - (((j : ℝ) + 1)⁻¹)

/-- The elapsed time from a selected peak to an interior terminal approximation. -/
def selectedLocalHarnackForwardTime (t1 : ℝ) (j : ℕ) : ℝ :=
  localHarnackTerminalApprox j - t1

/-- Lower coordinate faces for the target-dependent propagation corridor. -/
def localHarnackCorridorLower {d : ℕ} (v1 v : PDE.Vec d) : PDE.Vec d :=
  fun i => (min (v1 i) (v i) - 3) / 2

/-- Upper coordinate faces for the target-dependent propagation corridor. -/
def localHarnackCorridorUpper {d : ℕ} (v1 v : PDE.Vec d) : PDE.Vec d :=
  fun i => (max (v1 i) (v i) + 3) / 2

/-- The open normalized work box pulled back by translation from a peak time. -/
def localHarnackCorridorNeighborhood {d : ℕ} (t1 : ℝ) : Set (TimeVelocity d) :=
  parabolicAffine t1 (0 : PDE.Vec d) 1 ⁻¹' parabolicBox 2 2 0 0

/-- A backward open box is the corresponding forward box based at its lower time face. -/
theorem backwardParabolicBox_eq_parabolicBox {d : ℕ}
    (s terminalTime : ℝ) (v0 : PDE.Vec d) :
    backwardParabolicBox s terminalTime v0 =
      parabolicBox 1 s (terminalTime - s ^ 2) v0 := by
  ext z
  rcases z with ⟨t, v⟩
  rw [mem_backwardParabolicBox_iff, mem_parabolicBox_iff]
  constructor <;> rintro ⟨hlower, hupper, hv⟩ <;>
    refine ⟨?_, ?_, hv⟩ <;> nlinarith

/-- A terminal-inclusive backward box is the corresponding closed forward box. -/
theorem backwardParabolicClosedBox_eq_parabolicClosedBox {d : ℕ}
    (s terminalTime : ℝ) (v0 : PDE.Vec d) :
    backwardParabolicClosedBox s terminalTime v0 =
      parabolicClosedBox 1 s (terminalTime - s ^ 2) v0 := by
  ext z
  rcases z with ⟨t, v⟩
  rw [mem_backwardParabolicClosedBox_iff, mem_parabolicClosedBox_iff]
  constructor <;> rintro ⟨hlower, hupper, hv⟩ <;>
    refine ⟨?_, ?_, hv⟩ <;> nlinarith

/-- The unit peak-selection box lies strictly inside the normalized open work box. -/
theorem backwardParabolicClosedBox_one_four_subset_normalizedOpenBox {d : ℕ} :
    backwardParabolicClosedBox 1 4 (0 : PDE.Vec d) ⊆
      parabolicBox 2 2 0 0 := by
  intro z hz
  rcases z with ⟨t, v⟩
  rw [mem_backwardParabolicClosedBox_iff] at hz
  rw [mem_parabolicBox_iff]
  refine ⟨?_, ?_, ?_⟩
  · linarith [hz.1]
  · norm_num
    linarith [hz.2.1]
  · intro i
    have hvi := hz.2.2 i
    simpa only [Pi.zero_apply, sub_zero] using hvi.trans_lt (by norm_num : (1 : ℝ) < 2)

/-- The unit peak-selection box lies in the normalized closed work box. -/
theorem backwardParabolicClosedBox_one_four_subset_normalizedClosedBox {d : ℕ} :
    backwardParabolicClosedBox 1 4 (0 : PDE.Vec d) ⊆
      parabolicClosedBox 2 2 0 0 := by
  intro z hz
  rcases z with ⟨t, v⟩
  rw [mem_backwardParabolicClosedBox_iff] at hz
  rw [mem_parabolicClosedBox_iff]
  refine ⟨?_, ?_, ?_⟩
  · linarith [hz.1]
  · norm_num
    linarith [hz.2.1]
  · intro i
    have hvi := hz.2.2 i
    simpa only [Pi.zero_apply, sub_zero] using hvi.trans (by norm_num : (1 : ℝ) ≤ 2)

private theorem selected_peak_radius_nonneg {d : ℕ} {t1 r0 : ℝ} {v1 : PDE.Vec d}
    (hr0 : r0 = backwardParabolicRadius 4 (0 : PDE.Vec d) (t1, v1)) :
    0 ≤ r0 := by
  rw [hr0, backwardParabolicRadius]
  exact le_max_of_le_left (by
    rw [show velocitySupNorm (v1 - 0) = ‖v1‖ by
      simp only [velocitySupNorm_eq_norm, sub_zero]]
    exact norm_nonneg _)

private theorem selected_peak_time_bounds {d : ℕ} {t1 : ℝ} {v1 : PDE.Vec d}
    (hpoint : (t1, v1) ∈ backwardParabolicClosedBox 1 4 (0 : PDE.Vec d)) :
    3 ≤ t1 ∧ t1 ≤ 4 := by
  rw [mem_backwardParabolicClosedBox_iff] at hpoint
  norm_num at hpoint
  exact ⟨hpoint.1, hpoint.2.1⟩

/-- The selected peak velocity has strict normalized-cube margin. -/
theorem selected_peak_velocity_mem_velocityCube_one {d : ℕ}
    {t1 r0 : ℝ} {v1 : PDE.Vec d}
    (_hpoint : (t1, v1) ∈ backwardParabolicClosedBox 1 4 (0 : PDE.Vec d))
    (hr0 : r0 = backwardParabolicRadius 4 (0 : PDE.Vec d) (t1, v1))
    (hr0lt : r0 < 1) :
    v1 ∈ velocityCube (0 : PDE.Vec d) 1 := by
  have hr0nonneg := selected_peak_radius_nonneg hr0
  have hnorm : velocitySupNorm v1 ≤ r0 := by
    rw [hr0, backwardParabolicRadius]
    simpa only [sub_zero] using
      (le_max_left (velocitySupNorm v1) (Real.sqrt (4 - t1)))
  have hnorm' : ‖v1‖ ≤ r0 := by
    simpa only [velocitySupNorm_eq_norm] using hnorm
  intro i
  have hcoord := (pi_norm_le_iff_of_nonneg hr0nonneg).mp hnorm' i
  simpa only [Pi.zero_apply, sub_zero, Real.norm_eq_abs] using hcoord.trans_lt hr0lt

/-- The selected half-gap radius is positive. -/
theorem selected_backward_radius_pos {r0 : ℝ} (hr0lt : r0 < 1) :
    0 < (1 - r0) / 2 := by
  linarith

private theorem selected_backward_radius_le_half {d : ℕ} {t1 r0 : ℝ}
    {v1 : PDE.Vec d}
    (hr0 : r0 = backwardParabolicRadius 4 (0 : PDE.Vec d) (t1, v1)) :
    (1 - r0) / 2 ≤ 1 / 2 := by
  have hr0nonneg := selected_peak_radius_nonneg hr0
  linarith

private theorem selected_backwardParabolicClosedBox_subset_normalizedOpenBox_aux {d : ℕ}
    {t1 r0 : ℝ} {v1 : PDE.Vec d}
    (hpoint : (t1, v1) ∈ backwardParabolicClosedBox 1 4 (0 : PDE.Vec d))
    (hr0 : r0 = backwardParabolicRadius 4 (0 : PDE.Vec d) (t1, v1))
    (hr0lt : r0 < 1) :
    backwardParabolicClosedBox ((1 - r0) / 2) t1 v1 ⊆
      parabolicBox 2 2 0 0 := by
  let s : ℝ := (1 - r0) / 2
  have hspos : 0 < s := by
    dsimp [s]
    exact selected_backward_radius_pos hr0lt
  have hsnonneg : 0 ≤ s := hspos.le
  have hsle : s ≤ 1 / 2 := by
    dsimp [s]
    exact selected_backward_radius_le_half hr0
  have hsq : s ^ 2 ≤ 1 / 4 := by
    have hprod : 0 ≤ s * (1 / 2 - s) :=
      mul_nonneg hsnonneg (sub_nonneg.mpr hsle)
    nlinarith
  have ht1 := selected_peak_time_bounds hpoint
  have hv1 := selected_peak_velocity_mem_velocityCube_one hpoint hr0 hr0lt
  intro z hz
  rcases z with ⟨t, v⟩
  rw [mem_backwardParabolicClosedBox_iff] at hz
  rw [mem_parabolicBox_iff]
  refine ⟨?_, ?_, ?_⟩
  · have htLower : t1 - s ^ 2 ≤ t := by simpa only [s] using hz.1
    nlinarith [htLower]
  · norm_num
    linarith [hz.2.1, ht1.2]
  · intro i
    have hzv := hz.2.2 i
    have hv1i : |v1 i| < 1 := by simpa only [Pi.zero_apply, sub_zero] using hv1 i
    have habs : |v i| ≤ |v i - v1 i| + |v1 i| := by
      calc
        |v i| = |(v i - v1 i) + v1 i| := by
          apply congrArg abs
          ring
        _ ≤ |v i - v1 i| + |v1 i| := abs_add_le _ _
    have hzv' : |v i - v1 i| ≤ s := by simpa only [s] using hzv
    have hbound : |v i| ≤ s + |v1 i| := by
      calc
        |v i| ≤ |v i - v1 i| + |v1 i| := habs
        _ ≤ s + |v1 i| := by
          simpa only [add_comm] using add_le_add_right hzv' |v1 i|
    have hlt : |v i| < 2 := by
      calc
        |v i| ≤ s + |v1 i| := hbound
        _ < 1 / 2 + 1 := add_lt_add_of_le_of_lt hsle hv1i
        _ < 2 := by norm_num
    simpa only [Pi.zero_apply, sub_zero] using hlt

/-- The selected nested closed backward box lies strictly inside the open work box. -/
theorem selected_backwardParabolicClosedBox_subset_normalizedOpenBox {d : ℕ}
    {t1 r0 : ℝ} {v1 : PDE.Vec d}
    (hpoint : (t1, v1) ∈ backwardParabolicClosedBox 1 4 (0 : PDE.Vec d))
    (hr0 : r0 = backwardParabolicRadius 4 (0 : PDE.Vec d) (t1, v1))
    (hr0lt : r0 < 1) :
    backwardParabolicClosedBox ((1 - r0) / 2) t1 v1 ⊆
      parabolicBox 2 2 0 0 :=
  selected_backwardParabolicClosedBox_subset_normalizedOpenBox_aux hpoint hr0 hr0lt

/-- The selected nested closed backward box lies in the closed normalized work box. -/
theorem selected_backwardParabolicClosedBox_subset_normalizedClosedBox {d : ℕ}
    {t1 r0 : ℝ} {v1 : PDE.Vec d}
    (hpoint : (t1, v1) ∈ backwardParabolicClosedBox 1 4 (0 : PDE.Vec d))
    (hr0 : r0 = backwardParabolicRadius 4 (0 : PDE.Vec d) (t1, v1))
    (hr0lt : r0 < 1) :
    backwardParabolicClosedBox ((1 - r0) / 2) t1 v1 ⊆
      parabolicClosedBox 2 2 0 0 := by
  intro z hz
  have hopen := selected_backwardParabolicClosedBox_subset_normalizedOpenBox hpoint hr0 hr0lt hz
  rcases z with ⟨t, v⟩
  rw [mem_parabolicBox_iff] at hopen
  rw [mem_parabolicClosedBox_iff]
  exact ⟨hopen.1.le, hopen.2.1.le, fun i => (hopen.2.2 i).le⟩

/-- The selected nested open backward box lies in the normalized open work box. -/
theorem selected_backwardParabolicBox_subset_normalizedOpenBox {d : ℕ}
    {t1 r0 : ℝ} {v1 : PDE.Vec d}
    (hpoint : (t1, v1) ∈ backwardParabolicClosedBox 1 4 (0 : PDE.Vec d))
    (hr0 : r0 = backwardParabolicRadius 4 (0 : PDE.Vec d) (t1, v1))
    (hr0lt : r0 < 1) :
    backwardParabolicBox ((1 - r0) / 2) t1 v1 ⊆
      parabolicBox 2 2 0 0 := by
  intro z hz
  apply selected_backwardParabolicClosedBox_subset_normalizedOpenBox hpoint hr0 hr0lt
  rcases z with ⟨t, v⟩
  rw [mem_backwardParabolicBox_iff] at hz
  rw [mem_backwardParabolicClosedBox_iff]
  exact ⟨hz.1.le, hz.2.1.le, fun i => (hz.2.2 i).le⟩

/-- Every interior terminal approximation is at least seven. -/
theorem localHarnackTerminalApprox_seven_le (j : ℕ) :
    7 ≤ localHarnackTerminalApprox j := by
  unfold localHarnackTerminalApprox
  have hpos : 0 < (j : ℝ) + 1 := by positivity
  have hle : ((j : ℝ) + 1)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hpos]
    linarith
  linarith

/-- Every interior terminal approximation is strictly below the terminal face. -/
theorem localHarnackTerminalApprox_lt_eight (j : ℕ) :
    localHarnackTerminalApprox j < 8 := by
  unfold localHarnackTerminalApprox
  have hpos : 0 < ((j : ℝ) + 1)⁻¹ := by positivity
  linarith

/-- The interior terminal approximations converge to the terminal time. -/
theorem tendsto_localHarnackTerminalApprox :
    Tendsto localHarnackTerminalApprox atTop (nhds 8) := by
  have h := (tendsto_const_nhds (x := (8 : ℝ))).sub
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  change Tendsto (fun j : ℕ => 8 - ((j : ℝ) + 1)⁻¹) atTop (nhds 8)
  simpa only [one_div, sub_zero] using h

/-- An interior terminal approximation at an open target velocity lies in the work box. -/
theorem localHarnackTerminalApprox_mem_normalizedOpenBox {d : ℕ}
    {v : PDE.Vec d} (j : ℕ) (hv : v ∈ velocityCube (0 : PDE.Vec d) 1) :
    (localHarnackTerminalApprox j, v) ∈ parabolicBox 2 2 0 0 := by
  rw [mem_parabolicBox_iff]
  refine ⟨?_, ?_, ?_⟩
  · linarith [localHarnackTerminalApprox_seven_le j]
  · norm_num
    exact localHarnackTerminalApprox_lt_eight j
  · intro i
    have hvi := hv i
    simpa only [Pi.zero_apply, sub_zero] using hvi.trans (by norm_num : (1 : ℝ) < 2)

/-- The final open target lies on the terminal face of the normalized closed box. -/
theorem normalized_terminal_target_mem_normalizedClosedBox {d : ℕ}
    {v : PDE.Vec d} (hv : v ∈ velocityCube (0 : PDE.Vec d) 1) :
    (8, v) ∈ parabolicClosedBox 2 2 0 0 := by
  rw [mem_parabolicClosedBox_iff]
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro i
  have hvi := hv i
  simpa only [Pi.zero_apply, sub_zero] using hvi.le.trans (by norm_num : (1 : ℝ) ≤ 2)

/-- Translating the selected elapsed time recovers the terminal approximation. -/
theorem selectedLocalHarnackForwardTime_eq {t1 : ℝ} (j : ℕ) :
    t1 + selectedLocalHarnackForwardTime t1 j = localHarnackTerminalApprox j := by
  unfold selectedLocalHarnackForwardTime
  ring

private theorem selected_localHarnack_corridor_faces {d : ℕ}
    {t1 r0 : ℝ} {v1 v : PDE.Vec d}
    (hpoint : (t1, v1) ∈ backwardParabolicClosedBox 1 4 (0 : PDE.Vec d))
    (hr0 : r0 = backwardParabolicRadius 4 (0 : PDE.Vec d) (t1, v1))
    (hr0lt : r0 < 1) (hv : v ∈ velocityCube (0 : PDE.Vec d) 1) :
    (∀ i, 2 < localHarnackCorridorUpper v1 v i - localHarnackCorridorLower v1 v i ∧
      localHarnackCorridorUpper v1 v i - localHarnackCorridorLower v1 v i ≤ 4) ∧
    (∀ i, localHarnackCorridorLower v1 v i + 1 ≤ v1 i ∧
      v1 i < localHarnackCorridorUpper v1 v i - 1) ∧
    (∀ i, localHarnackCorridorLower v1 v i + 1 < v i ∧
      v i < localHarnackCorridorUpper v1 v i - 1) ∧
    (∀ i, -2 < localHarnackCorridorLower v1 v i ∧
      localHarnackCorridorUpper v1 v i < 2) := by
  have hv1 := selected_peak_velocity_mem_velocityCube_one hpoint hr0 hr0lt
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    have hv1i := by simpa only [Pi.zero_apply, sub_zero] using hv1 i
    have hvi := by simpa only [Pi.zero_apply, sub_zero] using hv i
    dsimp only [localHarnackCorridorLower, localHarnackCorridorUpper]
    have hmin : min (v1 i) (v i) ≤ max (v1 i) (v i) := min_le_max
    have hspan : max (v1 i) (v i) - min (v1 i) (v i) < 2 := by
      have hv1bounds := abs_lt.mp hv1i
      have hvbounds := abs_lt.mp hvi
      have hmin_lower : -1 < min (v1 i) (v i) := lt_min hv1bounds.1 hvbounds.1
      have hmax_upper : max (v1 i) (v i) < 1 := max_lt hv1bounds.2 hvbounds.2
      linarith
    constructor <;> linarith
  · intro i
    have hv1i := by simpa only [Pi.zero_apply, sub_zero] using hv1 i
    have hvi := by simpa only [Pi.zero_apply, sub_zero] using hv i
    have hv1bounds := abs_lt.mp hv1i
    have hvbounds := abs_lt.mp hvi
    dsimp only [localHarnackCorridorLower, localHarnackCorridorUpper]
    have hmin : min (v1 i) (v i) ≤ v1 i := min_le_left _ _
    have hmax : v1 i ≤ max (v1 i) (v i) := le_max_left _ _
    constructor <;> linarith [hv1bounds.1, hv1bounds.2, hvbounds.1, hvbounds.2]
  · intro i
    have hv1i := by simpa only [Pi.zero_apply, sub_zero] using hv1 i
    have hvi := by simpa only [Pi.zero_apply, sub_zero] using hv i
    have hv1bounds := abs_lt.mp hv1i
    have hvbounds := abs_lt.mp hvi
    dsimp only [localHarnackCorridorLower, localHarnackCorridorUpper]
    have hmin : min (v1 i) (v i) ≤ v i := min_le_right _ _
    have hmax : v i ≤ max (v1 i) (v i) := le_max_right _ _
    constructor <;> linarith [hv1bounds.1, hv1bounds.2, hvbounds.1, hvbounds.2]
  · intro i
    have hv1i := by simpa only [Pi.zero_apply, sub_zero] using hv1 i
    have hvi := by simpa only [Pi.zero_apply, sub_zero] using hv i
    have hv1bounds := abs_lt.mp hv1i
    have hvbounds := abs_lt.mp hvi
    dsimp only [localHarnackCorridorLower, localHarnackCorridorUpper]
    have hmin_lower : -1 < min (v1 i) (v i) := lt_min hv1bounds.1 hvbounds.1
    have hmax_upper : max (v1 i) (v i) < 1 := max_lt hv1bounds.2 hvbounds.2
    constructor <;> linarith

/-- The selected peak and an open target determine a closed propagation corridor. -/
theorem selected_localHarnack_corridor {d : ℕ}
    {t1 r0 : ℝ} {v1 v : PDE.Vec d} {j : ℕ}
    (hpoint : (t1, v1) ∈ backwardParabolicClosedBox 1 4 (0 : PDE.Vec d))
    (hr0 : r0 = backwardParabolicRadius 4 (0 : PDE.Vec d) (t1, v1))
    (hr0lt : r0 < 1)
    (hv : v ∈ velocityCube (0 : PDE.Vec d) 1) :
    let tau := selectedLocalHarnackForwardTime t1 j
    let lower := localHarnackCorridorLower v1 v
    let upper := localHarnackCorridorUpper v1 v
    2 < tau ∧ tau ≤ 8 ∧
      (∀ i, 2 < upper i - lower i ∧ upper i - lower i ≤ 4) ∧
      (∀ i, lower i + 1 ≤ v1 i ∧ v1 i < upper i - 1) ∧
      (∀ i, lower i + 1 < v i ∧ v i < upper i - 1) ∧
      parabolicClosedRectangle tau lower upper ⊆
        localHarnackCorridorNeighborhood t1 := by
  dsimp only
  have ht1 := selected_peak_time_bounds hpoint
  have hseven := localHarnackTerminalApprox_seven_le j
  have height := localHarnackTerminalApprox_lt_eight j
  have hfaces := selected_localHarnack_corridor_faces hpoint hr0 hr0lt hv
  refine ⟨?_, ?_, hfaces.1, hfaces.2.1, hfaces.2.2.1, ?_⟩
  · unfold selectedLocalHarnackForwardTime
    linarith
  · unfold selectedLocalHarnackForwardTime
    linarith
  · intro z hz
    rcases z with ⟨t, w⟩
    rw [mem_parabolicClosedRectangle_iff] at hz
    change parabolicAffine t1 (0 : PDE.Vec d) 1 (t, w) ∈ parabolicBox 2 2 0 0
    rw [mem_parabolicBox_iff]
    refine ⟨?_, ?_, ?_⟩
    · dsimp [parabolicAffine]
      linarith [ht1.1, hz.1]
    · dsimp [parabolicAffine]
      have htUpper : t ≤ selectedLocalHarnackForwardTime t1 j := hz.2.1
      have hsum : t1 + selectedLocalHarnackForwardTime t1 j =
          localHarnackTerminalApprox j := selectedLocalHarnackForwardTime_eq j
      norm_num
      linarith
    · intro i
      have hwi := hz.2.2 i
      have hface := hfaces.2.2.2 i
      dsimp [parabolicAffine]
      have hleft : -2 < w i := hface.1.trans_le hwi.1
      have hright : w i < 2 := hwi.2.trans_lt hface.2
      simpa only [Pi.zero_apply, zero_add, one_mul, sub_zero] using
        (abs_lt.mpr ⟨hleft, hright⟩)

private theorem parabolicAffine_surjective_of_pos {d : ℕ} {t0 r : ℝ}
    {v0 : PDE.Vec d} (hr : 0 < r) : Function.Surjective (parabolicAffine t0 v0 r) := by
  intro z
  refine ⟨((z.1 - t0) / r ^ 2, r⁻¹ • (z.2 - v0)), ?_⟩
  ext
  · dsimp [parabolicAffine]
    field_simp [hr.ne']
    ring
  · dsimp [parabolicAffine]
    rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
    ring

private theorem mem_parabolicAffine_localHarnackBox_iff {d : ℕ}
    {t0 r t : ℝ} {v0 w : PDE.Vec d} (hr : 0 < r) :
    parabolicAffine (t0 - r ^ 2) v0 (r / 2) (t, w) ∈
        parabolicBox 2 r (t0 - r ^ 2) v0 ↔
      (t, w) ∈ parabolicBox 2 2 0 0 := by
  have hscale : 0 < r / 2 := by linarith
  rw [mem_parabolicBox_iff, mem_parabolicBox_iff]
  dsimp [parabolicAffine]
  constructor
  · rintro ⟨htlower, htupper, hw⟩
    refine ⟨?_, ?_, ?_⟩
    · nlinarith [sq_pos_of_pos hscale]
    · norm_num at htupper ⊢
      nlinarith [sq_pos_of_pos hscale]
    · intro i
      have hwi := hw i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hwi ⊢
      rw [add_sub_cancel_left, abs_mul, abs_of_pos hscale] at hwi
      have : |w i| < 2 := by
        have hrscale : r / 2 * 2 = r := by ring
        exact lt_of_mul_lt_mul_left (by rw [hrscale]; exact hwi) hscale.le
      simpa only [sub_zero] using this
  · rintro ⟨htlower, htupper, hw⟩
    refine ⟨?_, ?_, ?_⟩
    · nlinarith [sq_pos_of_pos hscale]
    · norm_num at htupper ⊢
      nlinarith [sq_pos_of_pos hscale]
    · intro i
      have hwi := hw i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hwi ⊢
      rw [add_sub_cancel_left, abs_mul, abs_of_pos hscale]
      have : |w i| * (r / 2) < 2 * (r / 2) :=
        mul_lt_mul_of_pos_right (by simpa only [sub_zero] using hwi) hscale
      nlinarith

private theorem mem_parabolicAffine_localHarnackClosedBox_iff {d : ℕ}
    {t0 r t : ℝ} {v0 w : PDE.Vec d} (hr : 0 < r) :
    parabolicAffine (t0 - r ^ 2) v0 (r / 2) (t, w) ∈
        parabolicClosedBox 2 r (t0 - r ^ 2) v0 ↔
      (t, w) ∈ parabolicClosedBox 2 2 0 0 := by
  have hscale : 0 < r / 2 := by linarith
  rw [mem_parabolicClosedBox_iff, mem_parabolicClosedBox_iff]
  dsimp [parabolicAffine]
  constructor
  · rintro ⟨htlower, htupper, hw⟩
    refine ⟨?_, ?_, ?_⟩
    · nlinarith [sq_pos_of_pos hscale]
    · norm_num at htupper ⊢
      nlinarith [sq_pos_of_pos hscale]
    · intro i
      have hwi := hw i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hwi ⊢
      rw [add_sub_cancel_left, abs_mul, abs_of_pos hscale] at hwi
      have : |w i| ≤ 2 := by
        have hrscale : r / 2 * 2 = r := by ring
        exact le_of_mul_le_mul_left (by rw [hrscale]; exact hwi) hscale
      simpa only [sub_zero] using this
  · rintro ⟨htlower, htupper, hw⟩
    refine ⟨?_, ?_, ?_⟩
    · nlinarith [sq_pos_of_pos hscale]
    · norm_num at htupper ⊢
      nlinarith [sq_pos_of_pos hscale]
    · intro i
      have hwi := hw i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hwi ⊢
      rw [add_sub_cancel_left, abs_mul, abs_of_pos hscale]
      have : |w i| * (r / 2) ≤ 2 * (r / 2) :=
        mul_le_mul_of_nonneg_right (by simpa only [sub_zero] using hwi) hscale.le
      nlinarith

/-- The public radius-two open Harnack box has the exact normalized affine preimage. -/
theorem parabolicAffine_preimage_localHarnackBox {d : ℕ}
    {t0 r : ℝ} {v0 : PDE.Vec d} (hr : 0 < r) :
    parabolicAffine (t0 - r ^ 2) v0 (r / 2) ⁻¹'
        parabolicBox 2 r (t0 - r ^ 2) v0 =
      parabolicBox 2 2 0 0 := by
  ext z
  rcases z with ⟨t, w⟩
  exact mem_parabolicAffine_localHarnackBox_iff hr

/-- The public radius-two closed Harnack box has the exact normalized affine preimage. -/
theorem parabolicAffine_preimage_localHarnackClosedBox {d : ℕ}
    {t0 r : ℝ} {v0 : PDE.Vec d} (hr : 0 < r) :
    parabolicAffine (t0 - r ^ 2) v0 (r / 2) ⁻¹'
        parabolicClosedBox 2 r (t0 - r ^ 2) v0 =
      parabolicClosedBox 2 2 0 0 := by
  ext z
  rcases z with ⟨t, w⟩
  exact mem_parabolicAffine_localHarnackClosedBox_iff hr

/-- The normalized open Harnack box has the exact public affine image. -/
theorem parabolicAffine_image_localHarnackBox {d : ℕ}
    {t0 r : ℝ} {v0 : PDE.Vec d} (hr : 0 < r) :
    parabolicAffine (t0 - r ^ 2) v0 (r / 2) ''
        parabolicBox 2 2 0 0 =
      parabolicBox 2 r (t0 - r ^ 2) v0 := by
  rw [← parabolicAffine_preimage_localHarnackBox hr]
  exact Set.image_preimage_eq _ (parabolicAffine_surjective_of_pos (by linarith))

/-- The normalized closed Harnack box has the exact public affine image. -/
theorem parabolicAffine_image_localHarnackClosedBox {d : ℕ}
    {t0 r : ℝ} {v0 : PDE.Vec d} (hr : 0 < r) :
    parabolicAffine (t0 - r ^ 2) v0 (r / 2) ''
        parabolicClosedBox 2 2 0 0 =
      parabolicClosedBox 2 r (t0 - r ^ 2) v0 := by
  rw [← parabolicAffine_preimage_localHarnackClosedBox hr]
  exact Set.image_preimage_eq _ (parabolicAffine_surjective_of_pos (by linarith))

/-- The normalized Harnack source maps to the public source point. -/
@[simp] theorem parabolicAffine_localHarnack_source {d : ℕ}
    (t0 r : ℝ) (v0 : PDE.Vec d) :
    parabolicAffine (t0 - r ^ 2) v0 (r / 2) (4, 0) = (t0, v0) := by
  ext
  · simp [parabolicAffine]
    ring
  · simp [parabolicAffine]

/-- The normalized terminal slice maps to the public terminal slice. -/
@[simp] theorem parabolicAffine_localHarnack_terminal {d : ℕ}
    (t0 r : ℝ) (v0 w : PDE.Vec d) :
    parabolicAffine (t0 - r ^ 2) v0 (r / 2) (8, w) =
      (t0 + r ^ 2, v0 + (r / 2) • w) := by
  ext
  · simp [parabolicAffine]
    ring
  · simp [parabolicAffine]

/-- Positive affine scaling maps the normalized open target cube into the public one. -/
theorem mapsTo_parabolicAffine_localHarnack_targetCube {d : ℕ}
    {r : ℝ} {v0 : PDE.Vec d} (hr : 0 < r) :
    MapsTo (fun w : PDE.Vec d => v0 + (r / 2) • w)
      (velocityCube (0 : PDE.Vec d) 1) (velocityCube v0 (r / 2)) := by
  have hscale : 0 < r / 2 := by linarith
  intro w hw i
  have hwi := hw i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hwi ⊢
  rw [add_sub_cancel_left, abs_mul, abs_of_pos hscale]
  have : |w i| * (r / 2) < 1 * (r / 2) :=
    mul_lt_mul_of_pos_right (by simpa only [sub_zero] using hwi) hscale
  simpa only [one_mul, mul_comm] using this

end

end HypoellipticAleksandrov.Parabolic

module

public import HypoellipticAleksandrov.Parabolic.HarnackGeometry

/-!
# Fixed finite-chain geometry for parabolic Harnack

This module contains only the geometry of the square-root-free finite chain
from `(1, 0)` to `(4, z)`.  The velocity work boxes remain coordinate cubes,
while their containment is proved in the explicit Euclidean ball geometry.
-/

@[expose] public section

open Set

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/-- The time coordinate of the `k`th center in the fixed Harnack chain. -/
def harnackChainTime (d k : ℕ) : ℝ :=
  1 + (k : ℝ) * harnackChainRadius d ^ 2

/-- The velocity coordinate of the `k`th center in the fixed Harnack chain. -/
def harnackChainVelocity {d : ℕ} (z : PDE.Vec d) (k : ℕ) : PDE.Vec d :=
  ((k : ℝ) / (harnackChainLength d : ℝ)) • z

/-- The open one-box work region at the `k`th fixed-chain center. -/
def harnackChainLinkBox {d : ℕ} (z : PDE.Vec d) (k : ℕ) :
    Set (TimeVelocity d) :=
  parabolicBox 2 (harnackChainRadius d)
    (harnackChainTime d k - harnackChainRadius d ^ 2)
    (harnackChainVelocity z k)

/-- The compact closed one-box work region at the `k`th fixed-chain center. -/
def harnackChainClosedLinkBox {d : ℕ} (z : PDE.Vec d) (k : ℕ) :
    Set (TimeVelocity d) :=
  parabolicClosedBox 2 (harnackChainRadius d)
    (harnackChainTime d k - harnackChainRadius d ^ 2)
    (harnackChainVelocity z k)

/-- The fixed positive chain length in every positive dimension. -/
theorem harnackChainLength_pos {d : ℕ} (hd : 1 ≤ d) :
    0 < harnackChainLength d := by
  unfold harnackChainLength
  have hd0 : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hd
  positivity

/-- The first chain center has time coordinate one. -/
theorem harnackChainTime_zero {d : ℕ} : harnackChainTime d 0 = 1 := by
  simp [harnackChainTime]

/-- The first chain center has zero velocity. -/
theorem harnackChainVelocity_zero {d : ℕ} (z : PDE.Vec d) :
    harnackChainVelocity z 0 = 0 := by
  simp [harnackChainVelocity]

/-- Consecutive chain centers are separated by one squared chain radius in time. -/
theorem harnackChainTime_succ {d k : ℕ} :
    harnackChainTime d (k + 1) =
      harnackChainTime d k + harnackChainRadius d ^ 2 := by
  unfold harnackChainTime
  push_cast
  ring

/-- Consecutive chain centers have the fixed velocity increment `z / n_d`. -/
theorem harnackChainVelocity_succ_sub {d k : ℕ} (hd : 1 ≤ d)
    (z : PDE.Vec d) :
    harnackChainVelocity z (k + 1) - harnackChainVelocity z k =
      (1 / (harnackChainLength d : ℝ)) • z := by
  have hn : (harnackChainLength d : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (harnackChainLength_pos hd)
  unfold harnackChainVelocity
  rw [← sub_smul]
  congr 1
  push_cast
  field_simp
  ring

/-- The terminal chain center has time coordinate four. -/
theorem harnackChainTime_terminal {d : ℕ} (hd : 1 ≤ d) :
    harnackChainTime d (harnackChainLength d) = 4 := by
  unfold harnackChainTime
  rw [harnackChainLength_mul_radius_sq hd]
  norm_num

/-- The terminal chain center has velocity `z`. -/
theorem harnackChainVelocity_terminal {d : ℕ} (hd : 1 ≤ d)
    (z : PDE.Vec d) :
    harnackChainVelocity z (harnackChainLength d) = z := by
  have hn : (harnackChainLength d : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (harnackChainLength_pos hd)
  unfold harnackChainVelocity
  rw [div_self hn, one_smul]

/-- A closed coordinate cube controls the explicit squared Euclidean distance. -/
theorem vecNormSq_sub_le_natCast_mul_sq_of_mem_velocityClosedCube
    {d : ℕ} {v v0 : PDE.Vec d} {r : ℝ}
    (hv : v ∈ velocityClosedCube v0 r) :
    PDE.vecNormSq (v - v0) ≤ (d : ℝ) * r ^ 2 := by
  rw [PDE.vecNormSq_eq_sum_sq]
  calc
    ∑ i, (v - v0) i ^ 2 ≤ ∑ _i : Fin d, r ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      have hr : 0 ≤ r := le_trans (abs_nonneg (v i - v0 i)) (hv i)
      have hi := (sq_le_sq₀ (abs_nonneg (v i - v0 i)) hr).mpr (hv i)
      simpa only [Pi.sub_apply, sq_abs] using hi
    _ = (d : ℝ) * r ^ 2 := by simp [nsmul_eq_mul]

/-- The next center lies in the terminal half cube of its preceding link. -/
theorem harnackChain_next_mem_terminalHalfCube {d : ℕ} (hd : 1 ≤ d)
    {z : PDE.Vec d} (hz : z ∈ PDE.euclideanBall (0 : PDE.Vec d) 1)
    {k : ℕ} (hk : k < harnackChainLength d) :
    harnackChainVelocity z (k + 1) ∈
      velocityCube (harnackChainVelocity z k) (harnackChainRadius d / 2) := by
  have hn : 0 < (harnackChainLength d : ℝ) := by
    exact_mod_cast harnackChainLength_pos hd
  have hk' : k + 1 ≤ harnackChainLength d := Nat.succ_le_of_lt hk
  have hstep := harnackChainVelocity_succ_sub (k := k) hd z
  intro i
  have hzsquare : z i ^ 2 < 1 ^ 2 := by
    have hz' : PDE.vecNormSq z < 1 := by
      simpa [PDE.euclideanBall, PDE.euclideanSqDist] using hz
    simpa using (PDE.sq_apply_le_vecNormSq z i).trans_lt hz'
  have hzcoord : |z i| < 1 := abs_lt_of_sq_lt_sq hzsquare zero_le_one
  have hrecip := harnackChain_reciprocal_length_lt_half_radius hd
  have hstepi := congrFun hstep i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hstepi
  rw [hstepi, abs_mul, abs_of_pos (one_div_pos.mpr hn)]
  calc
    (1 / (harnackChainLength d : ℝ)) * |z i| <
        (1 / (harnackChainLength d : ℝ)) * 1 :=
      mul_lt_mul_of_pos_left hzcoord (one_div_pos.mpr hn)
    _ = 1 / (harnackChainLength d : ℝ) := mul_one _
    _ < harnackChainRadius d / 2 := hrecip

/-- Every closed fixed-chain link box is compact. -/
theorem harnackChainClosedLinkBox_compact {d : ℕ} (z : PDE.Vec d) (k : ℕ) :
    IsCompact (harnackChainClosedLinkBox z k) := by
  unfold harnackChainClosedLinkBox
  exact isCompact_parabolicClosedBox 2 (harnackChainRadius d)
    (harnackChainTime d k - harnackChainRadius d ^ 2)
    (harnackChainVelocity z k)

private theorem harnackChain_natCast_mul_radius_sq_le_one_sixteenth {d : ℕ}
    (hd : 1 ≤ d) :
    (d : ℝ) * harnackChainRadius d ^ 2 ≤ 1 / 16 := by
  have hdreal : 1 ≤ (d : ℝ) := by exact_mod_cast hd
  unfold harnackChainRadius
  have hdne : (d : ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith

private theorem harnackChain_radius_sq_le_one_sixteenth {d : ℕ} (hd : 1 ≤ d) :
    harnackChainRadius d ^ 2 ≤ 1 / 16 := by
  have hprod := harnackChain_natCast_mul_radius_sq_le_one_sixteenth hd
  have hdreal : 1 ≤ (d : ℝ) := by exact_mod_cast hd
  have hsquare : 0 ≤ harnackChainRadius d ^ 2 := sq_nonneg _
  nlinarith

private theorem harnackChain_center_time_le_four {d k : ℕ} (hd : 1 ≤ d)
    (hk : k ≤ harnackChainLength d) : harnackChainTime d k ≤ 4 := by
  have hk' : (k : ℝ) ≤ (harnackChainLength d : ℝ) := by exact_mod_cast hk
  have hmul := mul_le_mul_of_nonneg_right hk' (sq_nonneg (harnackChainRadius d))
  rw [← harnackChainTime_terminal hd]
  unfold harnackChainTime
  simpa [add_comm] using add_le_add_left hmul 1

private theorem harnackChain_center_velocity_norm_lt_one {d : ℕ}
    (hd : 1 ≤ d) {z : PDE.Vec d}
    (hz : z ∈ PDE.euclideanBall (0 : PDE.Vec d) 1)
    {k : ℕ} (hk : k ≤ harnackChainLength d) :
    PDE.vecNormSq (harnackChainVelocity z k) < 1 := by
  have hn : 0 < (harnackChainLength d : ℝ) := by
    exact_mod_cast harnackChainLength_pos hd
  have hk' : (k : ℝ) ≤ (harnackChainLength d : ℝ) := by exact_mod_cast hk
  have ha0 : 0 ≤ (k : ℝ) / (harnackChainLength d : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) hn.le
  have ha1 : (k : ℝ) / (harnackChainLength d : ℝ) ≤ 1 :=
    (div_le_one₀ hn).mpr hk'
  have hasq : ((k : ℝ) / (harnackChainLength d : ℝ)) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg ((k : ℝ) / (harnackChainLength d : ℝ) - 1)]
  have hz' : PDE.vecNormSq z < 1 := by
    simpa [PDE.euclideanBall, PDE.euclideanSqDist] using hz
  unfold harnackChainVelocity
  rw [PDE.vecNormSq_smul]
  calc
    ((k : ℝ) / (harnackChainLength d : ℝ)) ^ 2 * PDE.vecNormSq z ≤
        1 * PDE.vecNormSq z :=
      mul_le_mul_of_nonneg_right hasq (PDE.vecNormSq_nonneg z)
    _ < 1 * 1 := by nlinarith
    _ = 1 := by norm_num

/-- Each closed fixed-chain link box lies in the normalized Harnack work domain. -/
theorem harnackChainClosedLinkBox_subset_workDomain {d : ℕ} (hd : 1 ≤ d)
    {z : PDE.Vec d} (hz : z ∈ PDE.euclideanBall (0 : PDE.Vec d) 1)
    {k : ℕ} (hk : k ≤ harnackChainLength d) :
    harnackChainClosedLinkBox z k ⊆ harnackWorkDomain := by
  intro w hw
  rcases w with ⟨t, v⟩
  rw [mem_harnackWorkDomain_iff]
  rw [harnackChainClosedLinkBox, mem_parabolicClosedBox_iff] at hw
  have hR2 : harnackChainRadius d ^ 2 ≤ 1 / 16 :=
    harnackChain_radius_sq_le_one_sixteenth hd
  have htime0 : 1 ≤ harnackChainTime d k := by
    unfold harnackChainTime
    nlinarith [mul_nonneg (Nat.cast_nonneg k) (sq_nonneg (harnackChainRadius d))]
  have htime4 : harnackChainTime d k ≤ 4 :=
    harnackChain_center_time_le_four hd hk
  have hcenterNorm : PDE.vecNormSq (harnackChainVelocity z k) < 1 :=
    harnackChain_center_velocity_norm_lt_one hd hz hk
  have hdisp : PDE.vecNormSq (v - harnackChainVelocity z k) ≤
      (d : ℝ) * harnackChainRadius d ^ 2 :=
    vecNormSq_sub_le_natCast_mul_sq_of_mem_velocityClosedCube hw.2.2
  have hdreal : 1 ≤ (d : ℝ) := by exact_mod_cast hd
  have hdispSmall : PDE.vecNormSq (v - harnackChainVelocity z k) ≤ 1 / 16 := by
    have hprod := harnackChain_natCast_mul_radius_sq_le_one_sixteenth hd
    exact hdisp.trans hprod
  have hsum := PDE.vecNormSq_add_le (harnackChainVelocity z k)
    (v - harnackChainVelocity z k)
  have hrewrite : harnackChainVelocity z k +
      (v - harnackChainVelocity z k) = v := by
    ext i
    simp
  rw [hrewrite] at hsum
  constructor
  · nlinarith [hw.1, htime0]
  constructor
  · nlinarith [hw.2.1, htime4]
  · change PDE.euclideanSqDist v (0 : PDE.Vec d) < 2 ^ 2
    simp only [PDE.euclideanSqDist, sub_zero, pow_two]
    nlinarith

/-- A closed fixed-chain link box is compactly contained in the work domain. -/
theorem harnackChainClosedLinkBox_isCompactlyContained {d : ℕ}
    (hd : 1 ≤ d) {z : PDE.Vec d}
    (hz : z ∈ PDE.euclideanBall (0 : PDE.Vec d) 1)
    {k : ℕ} (hk : k ≤ harnackChainLength d) :
    IsCompact (harnackChainClosedLinkBox z k) ∧
      harnackChainClosedLinkBox z k ⊆ harnackWorkDomain :=
  ⟨harnackChainClosedLinkBox_compact z k,
    harnackChainClosedLinkBox_subset_workDomain hd hz hk⟩

/-- One compact literal Euclidean carrier contains every closed normalized
fixed-chain link for every target in the open unit velocity ball. -/
theorem exists_harnackChain_commonCompactCarrier
    (d : Nat) (hd : 1 ≤ d) :
    ∃ K : Set (TimeVelocity d),
      IsCompact K ∧ K ⊆ harnackWorkDomain ∧
      ∀ z ∈ PDE.euclideanBall (0 : PDE.Vec d) 1,
        ∀ k ≤ harnackChainLength d,
          harnackChainClosedLinkBox z k ⊆ K := by
  let K : Set (TimeVelocity d) :=
    Icc (3 / 4 : ℝ) (17 / 4 : ℝ) ×ˢ
      PDE.euclideanClosedBall (0 : PDE.Vec d) (3 / 2 : ℝ)
  refine ⟨K, ?_, ?_, ?_⟩
  · exact isCompact_Icc.prod
      (PDE.isCompact_euclideanClosedBall 0 (by norm_num))
  · rintro ⟨t, v⟩ ⟨ht, hv⟩
    rw [mem_harnackWorkDomain_iff]
    refine ⟨by nlinarith [ht.1], by nlinarith [ht.2], ?_⟩
    exact PDE.euclideanClosedBall_subset_euclideanBall (x₀ := 0)
      (by norm_num) (by norm_num) hv
  · intro z hz k hk
    rintro ⟨t, v⟩ hw
    rw [harnackChainClosedLinkBox, mem_parabolicClosedBox_iff] at hw
    change t ∈ Icc (3 / 4 : ℝ) (17 / 4 : ℝ) ∧
      v ∈ PDE.euclideanClosedBall (0 : PDE.Vec d) (3 / 2 : ℝ)
    have hR2 : harnackChainRadius d ^ 2 ≤ 1 / 16 :=
      harnackChain_radius_sq_le_one_sixteenth hd
    have htime0 : 1 ≤ harnackChainTime d k := by
      unfold harnackChainTime
      nlinarith [mul_nonneg (Nat.cast_nonneg k) (sq_nonneg (harnackChainRadius d))]
    have htime4 : harnackChainTime d k ≤ 4 :=
      harnackChain_center_time_le_four hd hk
    have hcenter : PDE.vecNormSq (harnackChainVelocity z k) < 1 :=
      harnackChain_center_velocity_norm_lt_one hd hz hk
    have hdisp : PDE.vecNormSq (v - harnackChainVelocity z k) ≤
        (d : ℝ) * harnackChainRadius d ^ 2 :=
      vecNormSq_sub_le_natCast_mul_sq_of_mem_velocityClosedCube hw.2.2
    have hdispSmall : PDE.vecNormSq (v - harnackChainVelocity z k) ≤ 1 / 16 :=
      hdisp.trans (harnackChain_natCast_mul_radius_sq_le_one_sixteenth hd)
    have hadd := PDE.vecNormSq_add_le (harnackChainVelocity z k)
      (v - harnackChainVelocity z k)
    have hrewrite : harnackChainVelocity z k +
        (v - harnackChainVelocity z k) = v := by
      ext i
      simp
    rw [hrewrite] at hadd
    constructor
    · constructor <;> nlinarith [hw.1, hw.2.1, hR2, htime0, htime4]
    · change PDE.euclideanSqDist v (0 : PDE.Vec d) ≤ (3 / 2 : ℝ) ^ 2
      simp only [PDE.euclideanSqDist, sub_zero]
      nlinarith [hadd, hcenter, hdispSmall]

end

end HypoellipticAleksandrov.Parabolic

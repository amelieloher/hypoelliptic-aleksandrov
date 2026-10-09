module

public import HypoellipticAleksandrov.Parabolic.HarnackChainGeometry

/-! # Equal-time Harnack links inside the open unit cylinder -/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open Set

private theorem normSq_lt_quarter_of_mem_halfBall {d : ℕ} {w : PDE.Vec d}
    (hw : w ∈ PDE.euclideanBall (0 : PDE.Vec d) (1 / 2 : ℝ)) :
    PDE.vecNormSq w < 1 / 4 := by
  norm_num [PDE.euclideanBall, PDE.euclideanSqDist] at hw ⊢
  exact hw

private theorem coordinate_lt_half_of_mem_halfBall {d : ℕ} {w : PDE.Vec d}
    (hw : w ∈ PDE.euclideanBall (0 : PDE.Vec d) (1 / 2 : ℝ)) (i : Fin d) :
    |w i| < 1 / 2 := by
  have hs := (PDE.sq_apply_le_vecNormSq w i).trans_lt
    (normSq_lt_quarter_of_mem_halfBall hw)
  apply abs_lt_of_sq_lt_sq (by nlinarith [hs]) (by norm_num)

/-- A fixed number of links reaches every upper point without crossing the terminal time. -/
theorem unitCylinder_harnack_link_geometry
    (d : ℕ) (hd : 1 ≤ d) (P P' : TimeVelocity d)
    (hP : P ∈ Ioo (1 / 4 : ℝ) (1 / 2 : ℝ) ×ˢ
      PDE.euclideanBall (0 : PDE.Vec d) (1 / 2 : ℝ))
    (hP' : P' ∈ Ioo (3 / 4 : ℝ) 1 ×ˢ
      PDE.euclideanBall (0 : PDE.Vec d) (1 / 2 : ℝ)) :
    let m : ℕ := 256 * d
    let dt : ℝ := (P'.1 - P.1) / (m : ℝ)
    let r : ℝ := Real.sqrt dt
    let t : ℕ → ℝ := fun k => P.1 + (k : ℝ) * dt
    let v : ℕ → PDE.Vec d := fun k =>
      P.2 + ((k : ℝ) / (m : ℝ)) • (P'.2 - P.2)
    0 < m ∧ 0 < r ∧ (t 0, v 0) = P ∧ (t m, v m) = P' ∧
    (∀ k < m, t (k + 1) = t k + r ^ 2) ∧
    (∀ k < m, parabolicClosedBox 2 r (t k - r ^ 2) (v k) ⊆
      Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec d) 1) ∧
    (∀ k < m, v (k + 1) ∈ velocityCube (v k) (r / 2)) := by
  let m : ℕ := 256 * d
  let dt : ℝ := (P'.1 - P.1) / (m : ℝ)
  let r : ℝ := Real.sqrt dt
  let t : ℕ → ℝ := fun k => P.1 + (k : ℝ) * dt
  let v : ℕ → PDE.Vec d := fun k =>
    P.2 + ((k : ℝ) / (m : ℝ)) • (P'.2 - P.2)
  change 0 < m ∧ 0 < r ∧ (t 0, v 0) = P ∧ (t m, v m) = P' ∧ _
  have hdreal : 1 ≤ (d : ℝ) := by exact_mod_cast hd
  have hm : 256 ≤ m := by dsimp [m]; omega
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 256) hm
  have hmreal : (256 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmd : (m : ℝ) = 256 * (d : ℝ) := by simp [m]
  have hgap0 : 1 / 4 < P'.1 - P.1 := by linarith [hP.1.2, hP'.1.1]
  have hgap1 : P'.1 - P.1 < 1 := by linarith [hP.1.1, hP'.1.2]
  have hdt : 0 < dt := div_pos (by linarith) hmpos
  have hmul : (m : ℝ) * dt = P'.1 - P.1 := by
    dsimp [dt]
    field_simp
  have hrsq : r ^ 2 = dt := Real.sq_sqrt hdt.le
  have hr : 0 < r := Real.sqrt_pos.mpr hdt
  have hdtSmall : dt < 1 / 256 := by nlinarith
  have hdSmall : (d : ℝ) * dt < 1 / 256 := by rw [hmd] at hmul; nlinarith
  have htstep : ∀ k : ℕ, t (k + 1) = t k + r ^ 2 := by
    intro k
    simp only [t, Nat.cast_add, Nat.cast_one, hrsq]
    ring
  have hvstep : ∀ k : ℕ, v (k + 1) - v k = (1 / (m : ℝ)) • (P'.2 - P.2) := by
    intro k
    ext i
    simp only [v, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Nat.cast_add, Nat.cast_one]
    ring
  have hcenter : ∀ k ≤ m,
      v k ∈ PDE.euclideanBall (0 : PDE.Vec d) (1 / 2 : ℝ) := by
    intro k hk
    have hkreal : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hk
    have ha : 0 ≤ (k : ℝ) / (m : ℝ) := div_nonneg (Nat.cast_nonneg _) hmpos.le
    have hb : (k : ℝ) / (m : ℝ) ≤ 1 := (div_le_one₀ hmpos).mpr hkreal
    have hconv := (PDE.convex_euclideanBall (0 : PDE.Vec d) (1 / 2 : ℝ))
      hP.2 hP'.2 (by linarith : 0 ≤ 1 - (k : ℝ) / (m : ℝ)) ha
      (by ring : (1 - (k : ℝ) / (m : ℝ)) + (k : ℝ) / (m : ℝ) = 1)
    convert hconv using 1
    ext i
    simp only [v, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hrecip : 1 / (m : ℝ) < r / 2 := by
    have hsquare : ((m : ℝ) * r) ^ 2 = (m : ℝ) * (P'.1 - P.1) := by
      calc
        ((m : ℝ) * r) ^ 2 = (m : ℝ) * ((m : ℝ) * dt) := by rw [mul_pow, hrsq]; ring
        _ = _ := by rw [hmul]
    have hlarge : 2 < (m : ℝ) * r := by
      have hpos := mul_pos hmpos hr
      have hprod := mul_lt_mul_of_pos_left hgap0 hmpos
      nlinarith
    apply (div_lt_iff₀ hmpos).mpr
    nlinarith
  refine ⟨by omega, hr, ?_, ?_, fun k _ => htstep k, ?_, ?_⟩
  · simp [t, v]
  · apply Prod.ext
    · dsimp [t]
      linarith
    · simp [v, div_self hmpos.ne', one_smul]
  · intro k hk w hw
    rcases w with ⟨s, w⟩
    rw [mem_parabolicClosedBox_iff] at hw
    have hkreal : (k : ℝ) ≤ (m : ℝ) - 1 := by
      have hs : ((k + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hk
      push_cast at hs
      linarith
    have htk0 : P.1 ≤ t k := by
      dsimp [t]
      exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hdt.le)
    have htk1 : t k + dt ≤ P'.1 := by
      have hle := mul_le_mul_of_nonneg_right hkreal hdt.le
      dsimp [t]
      nlinarith
    have hnorm := normSq_lt_quarter_of_mem_halfBall (hcenter k (Nat.le_of_lt hk))
    have hdisp := vecNormSq_sub_le_natCast_mul_sq_of_mem_velocityClosedCube hw.2.2
    rw [hrsq] at hdisp
    have hsum := PDE.vecNormSq_add_le (v k) (w - v k)
    rw [add_sub_cancel] at hsum
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hrsq] at hw
      linarith [hP.1.1, hw.1]
    · rw [hrsq] at hw
      linarith [hP'.1.2, hw.2.1]
    · change PDE.euclideanSqDist w 0 < 1 ^ 2
      simpa [PDE.euclideanSqDist] using (show PDE.vecNormSq w < 1 by nlinarith)
  · intro k _ i
    have hcoord0 := coordinate_lt_half_of_mem_halfBall hP.2 i
    have hcoord1 := coordinate_lt_half_of_mem_halfBall hP'.2 i
    have hcoord : |P'.2 i - P.2 i| < 1 := by
      have hab := abs_sub_le (P'.2 i) 0 (P.2 i)
      simp only [sub_zero, zero_sub, abs_neg] at hab
      linarith
    have hstepi := congrFun (hvstep k) i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hstepi
    rw [hstepi, abs_mul, abs_of_pos (one_div_pos.mpr hmpos)]
    calc
      (1 / (m : ℝ)) * |P'.2 i - P.2 i| < (1 / (m : ℝ)) * 1 :=
        mul_lt_mul_of_pos_left hcoord (one_div_pos.mpr hmpos)
      _ = 1 / (m : ℝ) := mul_one _
      _ < r / 2 := hrecip

end HypoellipticAleksandrov.Parabolic

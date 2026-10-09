module

public import HypoellipticAleksandrov.Parabolic.HarnackGeometry
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Order.Compact

/-!
# Compact weighted peak selection

This file records the terminal-inclusive compact selection used in the
parabolic Krylov--Safonov peak argument.  Its boxes are coordinate cubes.
-/

@[expose] public section

open Set

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/-- The coordinate sup norm on a velocity vector. -/
def velocitySupNorm {d : Nat} (v : PDE.Vec d) : Real :=
  ↑(Finset.univ.sup fun i : Fin d => ‖v i‖₊)

/-- The terminal-inclusive closed backward parabolic coordinate box. -/
def backwardParabolicClosedBox {d : Nat} (r terminalTime : Real)
    (v0 : PDE.Vec d) : Set (TimeVelocity d) :=
  Set.Icc (terminalTime - r ^ 2) terminalTime ×ˢ velocityClosedCube v0 r

/-- The backward parabolic radius relative to a terminal time and velocity. -/
def backwardParabolicRadius {d : Nat} (terminalTime : Real) (v0 : PDE.Vec d)
    (z : TimeVelocity d) : Real :=
  max (velocitySupNorm (z.2 - v0)) (Real.sqrt (terminalTime - z.1))

/-- The compact-selection weight used by the backward peak argument. -/
def weightedBackwardPeak {d : Nat} (m : Nat) (terminalTime : Real)
    (v0 : PDE.Vec d) (u : TimeVelocity d → Real) (z : TimeVelocity d) : Real :=
  (1 - backwardParabolicRadius terminalTime v0 z) ^ m * u z

/-- The coordinate sup norm agrees with the native finite-product norm. -/
theorem velocitySupNorm_eq_norm {d : Nat} (v : PDE.Vec d) :
    velocitySupNorm v = ‖v‖ := by
  rfl

/-- Membership in a coordinate cube is precisely a coordinate-sup bound. -/
theorem mem_velocityClosedCube_iff_velocitySupNorm_sub_le {d : Nat}
    {v v0 : PDE.Vec d} {r : Real} (hr : 0 ≤ r) :
    v ∈ velocityClosedCube v0 r ↔ velocitySupNorm (v - v0) ≤ r := by
  constructor
  · intro hv
    rw [velocitySupNorm_eq_norm, pi_norm_le_iff_of_nonneg hr]
    intro i
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using hv i
  · intro hv i
    have hnorm : ‖v - v0‖ ≤ r := by
      simpa only [velocitySupNorm_eq_norm] using hv
    have hcoord := (pi_norm_le_iff_of_nonneg hr).mp hnorm i
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using hcoord

/-- Membership in a terminal-inclusive backward box. -/
theorem mem_backwardParabolicClosedBox_iff {d : Nat} {r terminalTime t : Real}
    {v0 v : PDE.Vec d} :
    (t, v) ∈ backwardParabolicClosedBox r terminalTime v0 ↔
      terminalTime - r ^ 2 ≤ t ∧ t ≤ terminalTime ∧ v ∈ velocityClosedCube v0 r := by
  constructor
  · rintro ⟨⟨ht0, ht⟩, hv⟩
    exact ⟨ht0, ht, hv⟩
  · rintro ⟨ht0, ht, hv⟩
    exact ⟨⟨ht0, ht⟩, hv⟩

/-- Terminal-inclusive backward coordinate boxes are compact. -/
theorem isCompact_backwardParabolicClosedBox {d : Nat} (r terminalTime : Real)
    (v0 : PDE.Vec d) :
    IsCompact (backwardParabolicClosedBox r terminalTime v0) :=
  isCompact_Icc.prod (isCompact_velocityClosedCube v0 r)

/-- The coordinate sup norm is continuous. -/
theorem continuous_velocitySupNorm {d : Nat} :
    Continuous (velocitySupNorm : PDE.Vec d → Real) := by
  rw [show velocitySupNorm = fun v : PDE.Vec d => ‖v‖ from funext velocitySupNorm_eq_norm]
  exact continuous_norm

/-- The backward parabolic radius is continuous. -/
theorem continuous_backwardParabolicRadius {d : Nat} (terminalTime : Real)
    (v0 : PDE.Vec d) :
    Continuous (backwardParabolicRadius terminalTime v0) := by
  unfold backwardParabolicRadius
  exact (continuous_velocitySupNorm.comp (continuous_snd.sub continuous_const)).max
    (Real.continuous_sqrt.comp (continuous_const.sub continuous_fst))

/-- The backward radius is at most one on the normalized closed unit box. -/
theorem backwardParabolicRadius_le_one_of_mem_unitClosedBox {d : Nat}
    {z : TimeVelocity d} (hz : z ∈ backwardParabolicClosedBox 1 4 (0 : PDE.Vec d)) :
    backwardParabolicRadius 4 (0 : PDE.Vec d) z ≤ 1 := by
  rcases (mem_backwardParabolicClosedBox_iff.mp hz) with ⟨htlower, htupper, hv⟩
  apply max_le
  · rw [← mem_velocityClosedCube_iff_velocitySupNorm_sub_le zero_le_one]
    simpa using hv
  · apply Real.sqrt_le_one.mpr
    norm_num at htlower ⊢
    linarith

/-- A point in the half-gap box around a radius-`r0` point has radius at most
`(1 + r0) / 2`. -/
theorem backwardParabolicRadius_nested_le {d : Nat} {t1 r0 : Real}
    {v1 : PDE.Vec d} (hpoint : (t1, v1) ∈ backwardParabolicClosedBox 1 4 0)
    (hr0 : r0 = backwardParabolicRadius 4 0 (t1, v1)) (hr0lt : r0 < 1)
    {z : TimeVelocity d}
    (hz : z ∈ backwardParabolicClosedBox ((1 - r0) / 2) t1 v1) :
    backwardParabolicRadius 4 0 z ≤ (1 + r0) / 2 := by
  let s : Real := (1 - r0) / 2
  have hs : 0 ≤ s := by
    dsimp [s]
    linarith
  have hr0nonneg : 0 ≤ r0 := by
    rw [hr0, backwardParabolicRadius]
    calc
      0 ≤ velocitySupNorm ((t1, v1).2 - 0) := by
        rw [velocitySupNorm_eq_norm]
        exact norm_nonneg _
      _ ≤ max (velocitySupNorm ((t1, v1).2 - 0)) (Real.sqrt (4 - (t1, v1).1)) :=
        le_max_left _ _
  have hv1 : velocitySupNorm v1 ≤ r0 := by
    rw [hr0, backwardParabolicRadius]
    convert le_max_left (velocitySupNorm v1) (Real.sqrt (4 - t1)) using 1
    all_goals simp
  have ht1 : t1 ≤ 4 := (mem_backwardParabolicClosedBox_iff.mp hpoint).2.1
  have htime : Real.sqrt (4 - t1) ≤ r0 := by
    rw [hr0, backwardParabolicRadius]
    convert le_max_right (velocitySupNorm v1) (Real.sqrt (4 - t1)) using 1
    all_goals simp
  have htime_sq : 4 - t1 ≤ r0 ^ 2 := by
    have hnonneg : 0 ≤ 4 - t1 := sub_nonneg.mpr ht1
    calc
      4 - t1 = Real.sqrt (4 - t1) ^ 2 := (Real.sq_sqrt hnonneg).symm
      _ ≤ r0 ^ 2 := (sq_le_sq₀ (Real.sqrt_nonneg _) hr0nonneg).mpr htime
  rcases (mem_backwardParabolicClosedBox_iff.mp hz) with ⟨hztime, _, hzvel⟩
  have hzvel' : velocitySupNorm (z.2 - v1) ≤ s := by
    rw [← mem_velocityClosedCube_iff_velocitySupNorm_sub_le hs]
    simpa [s] using hzvel
  have hspace : velocitySupNorm z.2 ≤ (1 + r0) / 2 := by
    calc
      velocitySupNorm z.2 = ‖z.2‖ := velocitySupNorm_eq_norm _
      _ = ‖(z.2 - v1) + v1‖ := by rw [sub_add_cancel]
      _ ≤ ‖z.2 - v1‖ + ‖v1‖ := norm_add_le _ _
      _ = velocitySupNorm (z.2 - v1) + velocitySupNorm v1 := by
        rw [velocitySupNorm_eq_norm, velocitySupNorm_eq_norm]
      _ ≤ s + r0 := add_le_add hzvel' hv1
      _ = (1 + r0) / 2 := by dsimp [s]; ring
  have htime_arg : 4 - z.1 ≤ r0 ^ 2 + s ^ 2 := by
    change t1 - s ^ 2 ≤ z.1 at hztime
    nlinarith
  have htime' : Real.sqrt (4 - z.1) ≤ (1 + r0) / 2 := by
    have hsum : 0 ≤ r0 + s := add_nonneg hr0nonneg hs
    have hsq : 4 - z.1 ≤ (r0 + s) ^ 2 := by
      nlinarith [sq_nonneg (r0 - s)]
    have hsqrt : Real.sqrt (4 - z.1) ≤ r0 + s :=
      (Real.sqrt_le_iff.mpr ⟨hsum, hsq⟩)
    calc
      Real.sqrt (4 - z.1) ≤ r0 + s := hsqrt
      _ = (1 + r0) / 2 := by dsimp [s]; ring
  change max (velocitySupNorm (z.2 - 0)) (Real.sqrt (4 - z.1)) ≤ (1 + r0) / 2
  simpa using max_le hspace htime'

private theorem terminal_zero_mem_unitClosedBox {d : Nat} :
    (4, (0 : PDE.Vec d)) ∈ backwardParabolicClosedBox 1 4 0 := by
  rw [mem_backwardParabolicClosedBox_iff]
  constructor
  · norm_num
  constructor
  · norm_num
  · intro i
    simp

private theorem backwardParabolicRadius_terminal_zero {d : Nat} :
    backwardParabolicRadius 4 (0 : PDE.Vec d) (4, 0) = 0 := by
  simp [backwardParabolicRadius, velocitySupNorm_eq_norm]

/-- A continuous function which is positive at the terminal center has a
strictly interior weighted maximizer, together with the exact nested-box bound. -/
theorem exists_weighted_backward_peak
    {d : Nat} (m : Nat) (hm : 0 < m) (u : TimeVelocity d → Real)
    (hu : ContinuousOn u
      (backwardParabolicClosedBox 1 4 (0 : PDE.Vec d)))
    (hu0 : 0 < u (4, (0 : PDE.Vec d))) :
    ∃ (t1 : Real) (v1 : PDE.Vec d) (r0 : Real),
      (t1, v1) ∈ backwardParabolicClosedBox 1 4 (0 : PDE.Vec d) ∧
      r0 = backwardParabolicRadius 4 (0 : PDE.Vec d) (t1, v1) ∧
      (∀ z ∈ backwardParabolicClosedBox 1 4 (0 : PDE.Vec d),
        weightedBackwardPeak m 4 (0 : PDE.Vec d) u z ≤
          weightedBackwardPeak m 4 (0 : PDE.Vec d) u (t1, v1)) ∧
      r0 < 1 ∧
      u (4, (0 : PDE.Vec d)) ≤ (1 - r0) ^ m * u (t1, v1) ∧
      0 < u (t1, v1) ∧
      ∀ z ∈ backwardParabolicClosedBox ((1 - r0) / 2) t1 v1,
        u z ≤ (2 : Real) ^ m * u (t1, v1) := by
  let K : Set (TimeVelocity d) := backwardParabolicClosedBox 1 4 0
  let W : TimeVelocity d → Real := weightedBackwardPeak m 4 0 u
  have hKcompact : IsCompact K := isCompact_backwardParabolicClosedBox 1 4 0
  have hterminal : (4, (0 : PDE.Vec d)) ∈ K := terminal_zero_mem_unitClosedBox
  have hW : ContinuousOn W K := by
    dsimp [W]
    exact
      ((continuous_const.sub (continuous_backwardParabolicRadius 4 0)).pow m).continuousOn.mul hu
  obtain ⟨z1, hz1, hmax⟩ := hKcompact.exists_isMaxOn ⟨_, hterminal⟩ hW
  let t1 : Real := z1.1
  let v1 : PDE.Vec d := z1.2
  let r0 : Real := backwardParabolicRadius 4 0 z1
  have hr0le : r0 ≤ 1 := by
    dsimp [r0]
    exact backwardParabolicRadius_le_one_of_mem_unitClosedBox (by simpa [K] using hz1)
  have hterminal_value : W (4, (0 : PDE.Vec d)) = u (4, (0 : PDE.Vec d)) := by
    simp [W, weightedBackwardPeak, backwardParabolicRadius_terminal_zero]
  have hmax_terminal : u (4, (0 : PDE.Vec d)) ≤ W z1 := by
    rw [← hterminal_value]
    exact hmax (by simpa [K] using hterminal)
  have hr0lt : r0 < 1 := by
    apply lt_of_le_of_ne hr0le
    intro heq
    have hzero : W z1 = 0 := by
      change r0 = 1 at heq
      simp [W, weightedBackwardPeak, r0, heq, hm.ne']
    rw [hzero] at hmax_terminal
    exact (not_lt_of_ge hmax_terminal) hu0
  have hweighted : u (4, (0 : PDE.Vec d)) ≤ (1 - r0) ^ m * u z1 := by
    simpa only [W, weightedBackwardPeak, r0] using hmax_terminal
  have hfactor_pos : 0 < (1 - r0) ^ m := pow_pos (by linarith) _
  have hu1 : 0 < u z1 :=
    pos_of_mul_pos_right (hu0.trans_le hweighted) hfactor_pos.le
  refine ⟨t1, v1, r0, ?_, ?_, ?_, hr0lt, ?_, ?_, ?_⟩
  · simpa [t1, v1, K] using hz1
  · rfl
  · intro z hz
    exact hmax (by simpa [K] using hz)
  · simpa [t1, v1] using hweighted
  · simpa [t1, v1] using hu1
  · intro z hz
    have hradius := backwardParabolicRadius_nested_le (d := d)
      (by simpa [t1, v1, K] using hz1) (by rfl) hr0lt hz
    let s : Real := (1 - r0) / 2
    have hspos : 0 < s := by
      dsimp [s]
      linarith
    have hfactor : s ≤ 1 - backwardParabolicRadius 4 0 z := by
      dsimp [s]
      linarith
    have hfactor_nonneg : 0 ≤ 1 - backwardParabolicRadius 4 0 z :=
      hspos.le.trans hfactor
    have hsub : backwardParabolicClosedBox s t1 v1 ⊆ K := by
      intro y hy
      have hy_radius := backwardParabolicRadius_nested_le (d := d)
        (by simpa [t1, v1, K] using hz1) (by rfl) hr0lt hy
      have hyvel : velocitySupNorm y.2 ≤ 1 := by
        calc
          velocitySupNorm y.2 ≤ backwardParabolicRadius 4 0 y := by
            rw [backwardParabolicRadius]
            convert le_max_left (velocitySupNorm y.2) (Real.sqrt (4 - y.1)) using 1
            all_goals simp
          _ ≤ (1 + r0) / 2 := hy_radius
          _ ≤ 1 := by linarith
      have hytime : Real.sqrt (4 - y.1) ≤ 1 := by
        calc
          Real.sqrt (4 - y.1) ≤ backwardParabolicRadius 4 0 y := by
            rw [backwardParabolicRadius]
            exact le_max_right _ _
          _ ≤ (1 + r0) / 2 := hy_radius
          _ ≤ 1 := by linarith
      rcases (mem_backwardParabolicClosedBox_iff.mp hy) with ⟨_, hyupper, _⟩
      have ht1upper : t1 ≤ 4 := (mem_backwardParabolicClosedBox_iff.mp
        (by simpa [t1, v1, K] using hz1)).2.1
      rw [mem_backwardParabolicClosedBox_iff]
      refine ⟨?_, hyupper.trans ht1upper, ?_⟩
      · have hsq : 4 - y.1 ≤ 1 := Real.sqrt_le_one.mp hytime
        norm_num at hsq ⊢
        linarith
      · exact (mem_velocityClosedCube_iff_velocitySupNorm_sub_le zero_le_one).mpr (by
          simpa using hyvel)
    by_cases huz : 0 < u z
    · have hpow : s ^ m ≤ (1 - backwardParabolicRadius 4 0 z) ^ m :=
        pow_le_pow_left₀ hspos.le hfactor _
      have hleft : s ^ m * u z ≤ (1 - backwardParabolicRadius 4 0 z) ^ m * u z :=
        mul_le_mul_of_nonneg_right hpow huz.le
      have hpeak : weightedBackwardPeak m 4 0 u z ≤ weightedBackwardPeak m 4 0 u z1 :=
        hmax (hsub (by simpa [s] using hz))
      have hmiddle : s ^ m * u z ≤ (1 - r0) ^ m * u z1 := by
        calc
          s ^ m * u z ≤ (1 - backwardParabolicRadius 4 0 z) ^ m * u z := hleft
          _ = weightedBackwardPeak m 4 0 u z := rfl
          _ ≤ weightedBackwardPeak m 4 0 u z1 := hpeak
          _ = (1 - r0) ^ m * u z1 := by rfl
      apply le_of_mul_le_mul_left (a0 := pow_pos hspos m)
      calc
        s ^ m * u z ≤ (1 - r0) ^ m * u z1 := hmiddle
        _ = s ^ m * ((2 : Real) ^ m * u z1) := by
          dsimp [s]
          rw [show 1 - r0 = 2 * ((1 - r0) / 2) by ring, mul_pow]
          ring
    · have huzle : u z ≤ 0 := le_of_not_gt huz
      have hrightpos : 0 < (2 : Real) ^ m * u z1 :=
        mul_pos (pow_pos (by norm_num) _) hu1
      linarith

end

end HypoellipticAleksandrov.Parabolic

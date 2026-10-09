module

public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyDyadicPointSelector

/-!
# Two-centre parabolic dyadic geometry

This module gives the scale selection and literal two-box enclosure used by
the dyadic Morrey argument.  It makes no common-address, shifted-grid, or
analytic assertion: the enclosing box is an ordinary (non-dyadic) forward
parabolic box.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/-- Two distinct points in the reference carrier have a least dyadic scale
whose source-box radius is no greater than their coordinate distance. -/
theorem exists_parabolicDyadicGeneration_radius_le_coordinateDist_lt_two_mul_radius
    (d : Nat) (z : TimeVelocity d)
    (hz : z ∈ parabolicDyadicReferenceCell d)
    (w : TimeVelocity d)
    (hw : w ∈ parabolicDyadicReferenceCell d)
    (hzw : z ≠ w) :
    ∃ n : Nat,
      (parabolicDyadicSourceBox
        (parabolicDyadicAddressContaining d z hz n).2).radius ≤
          parabolicCoordinateDist z w ∧
      parabolicCoordinateDist z w <
        2 * (parabolicDyadicSourceBox
          (parabolicDyadicAddressContaining d z hz n).2).radius := by
  let rho : Real := parabolicCoordinateDist z w
  let radius : Nat → Real := fun n =>
    (parabolicDyadicSourceBox
      (parabolicDyadicAddressContaining d z hz n).2).radius
  have hrhoPos : 0 < rho := by
    apply lt_of_le_of_ne (parabolicCoordinateDist_nonneg z w)
    intro hzero
    apply hzw
    exact (parabolicCoordinateDist_eq_zero_iff z w).mp hzero.symm
  have htime : Real.sqrt |z.1 - w.1| < 1 := by
    change z.1 ∈ Ioc (0 : Real) 1 ∧
      z.2 ∈ Set.univ.pi (fun _ : Fin d => Ioc (-1 : Real) 1) at hz
    change w.1 ∈ Ioc (0 : Real) 1 ∧
      w.2 ∈ Set.univ.pi (fun _ : Fin d => Ioc (-1 : Real) 1) at hw
    apply (Real.sqrt_lt' (by norm_num : (0 : Real) < 1)).mpr
    rw [abs_lt]
    constructor <;> linarith [hz.1.1, hz.1.2, hw.1.1, hw.1.2]
  have hvelocity : ‖z.2 - w.2‖ < 2 := by
    rw [pi_norm_lt_iff (by norm_num : (0 : Real) < 2)]
    intro coordinate
    simp only [Pi.sub_apply, Real.norm_eq_abs]
    obtain ⟨hzLower, hzUpper⟩ := hz.2 coordinate (Set.mem_univ coordinate)
    obtain ⟨hwLower, hwUpper⟩ := hw.2 coordinate (Set.mem_univ coordinate)
    rw [abs_lt]
    constructor <;> linarith
  have hrhoLtTwo : rho < 2 := by
    dsimp only [rho, parabolicCoordinateDist]
    apply max_lt
    · linarith
    · exact hvelocity
  let P : Nat → Prop := fun n => radius n ≤ rho
  have hP : ∃ n, P n := by
    have heventually : ∀ᶠ n in atTop, 2 * radius n < 2 * rho := by
      have hlimit := tendsto_two_mul_parabolicDyadicIndexContaining_radius_atTop d z hz
      exact hlimit.eventually_lt_const (by linarith)
    obtain ⟨n, hn⟩ := eventually_atTop.mp heventually
    refine ⟨n, ?_⟩
    exact le_of_lt (by linarith [hn n le_rfl])
  refine ⟨Nat.find hP, Nat.find_spec hP, ?_⟩
  have hfindZeroOrSucc : Nat.find hP = 0 ∨ ∃ m, Nat.find hP = m + 1 := by
    by_cases hzero : Nat.find hP = 0
    · exact Or.inl hzero
    · exact Or.inr (Nat.exists_eq_succ_of_ne_zero hzero)
  rcases hfindZeroOrSucc with hzero | ⟨m, hm⟩
  · rw [hzero]
    change rho < 2 * ((2 : Real) ^ 0)⁻¹
    norm_num
    exact hrhoLtTwo
  · have hnot : ¬ P m := by
      intro hmP
      have hmin := Nat.find_min' hP hmP
      rw [hm] at hmin
      omega
    have hltPrevious : rho < radius m := lt_of_not_ge hnot
    rw [hm]
    change rho < 2 * ((2 : Real) ^ (m + 1))⁻¹
    calc
      rho < ((2 : Real) ^ m)⁻¹ := hltPrevious
      _ = 2 * ((2 : Real) ^ (m + 1))⁻¹ := by
        rw [pow_succ]
        field_simp

/-- The two selected source boxes at a fixed generation lie in one literal
nearby forward box of radius three times the coordinate separation. -/
theorem parabolicDyadicSelectedForwardBoxes_subset_nearbyCommonBox
    (d : Nat) (z : TimeVelocity d)
    (hz : z ∈ parabolicDyadicReferenceCell d)
    (w : TimeVelocity d)
    (hw : w ∈ parabolicDyadicReferenceCell d)
    (n : Nat)
    (hr :
      (parabolicDyadicSourceBox
        (parabolicDyadicAddressContaining d z hz n).2).radius ≤
        parabolicCoordinateDist z w) :
    parabolicBox 1
        (parabolicDyadicSourceBox
          (parabolicDyadicAddressContaining d z hz n).2).radius
        (parabolicDyadicSourceBox
          (parabolicDyadicAddressContaining d z hz n).2).baseTime
        (parabolicDyadicSourceBox
          (parabolicDyadicAddressContaining d z hz n).2).center ⊆
      parabolicBox 1 (3 * parabolicCoordinateDist z w)
        (min
          (parabolicDyadicSourceBox
            (parabolicDyadicAddressContaining d z hz n).2).baseTime
          (parabolicDyadicSourceBox
            (parabolicDyadicAddressContaining d w hw n).2).baseTime)
        ((z.2 + w.2) / 2) ∧
    parabolicBox 1
        (parabolicDyadicSourceBox
          (parabolicDyadicAddressContaining d w hw n).2).radius
        (parabolicDyadicSourceBox
          (parabolicDyadicAddressContaining d w hw n).2).baseTime
        (parabolicDyadicSourceBox
          (parabolicDyadicAddressContaining d w hw n).2).center ⊆
      parabolicBox 1 (3 * parabolicCoordinateDist z w)
        (min
          (parabolicDyadicSourceBox
            (parabolicDyadicAddressContaining d z hz n).2).baseTime
          (parabolicDyadicSourceBox
            (parabolicDyadicAddressContaining d w hw n).2).baseTime)
        ((z.2 + w.2) / 2) ∧
    parabolicClosedBox 1
        (parabolicDyadicSourceBox
          (parabolicDyadicAddressContaining d z hz n).2).radius
        (parabolicDyadicSourceBox
          (parabolicDyadicAddressContaining d z hz n).2).baseTime
        (parabolicDyadicSourceBox
          (parabolicDyadicAddressContaining d z hz n).2).center ⊆
      parabolicClosedBox 1 (3 * parabolicCoordinateDist z w)
        (min
          (parabolicDyadicSourceBox
            (parabolicDyadicAddressContaining d z hz n).2).baseTime
          (parabolicDyadicSourceBox
            (parabolicDyadicAddressContaining d w hw n).2).baseTime)
        ((z.2 + w.2) / 2) ∧
    parabolicClosedBox 1
        (parabolicDyadicSourceBox
          (parabolicDyadicAddressContaining d w hw n).2).radius
        (parabolicDyadicSourceBox
          (parabolicDyadicAddressContaining d w hw n).2).baseTime
        (parabolicDyadicSourceBox
          (parabolicDyadicAddressContaining d w hw n).2).center ⊆
      parabolicClosedBox 1 (3 * parabolicCoordinateDist z w)
        (min
          (parabolicDyadicSourceBox
            (parabolicDyadicAddressContaining d z hz n).2).baseTime
          (parabolicDyadicSourceBox
            (parabolicDyadicAddressContaining d w hw n).2).baseTime)
        ((z.2 + w.2) / 2) := by
  let rho : Real := parabolicCoordinateDist z w
  let qz := parabolicDyadicSourceBox
    (parabolicDyadicAddressContaining d z hz n).2
  let qw := parabolicDyadicSourceBox
    (parabolicDyadicAddressContaining d w hw n).2
  let tMin : Real := min qz.baseTime qw.baseTime
  have hqzRadiusPos : 0 < qz.radius := by
    change 0 < (parabolicDyadicSourceBox
      (parabolicDyadicAddressContaining d z hz n).2).radius
    exact parabolicDyadicSourceBox_radius_pos _
  have hrhoPos : 0 < rho := lt_of_lt_of_le hqzRadiusPos hr
  have hRadius : qz.radius = qw.radius := by
    change ((2 : Real) ^ n)⁻¹ = ((2 : Real) ^ n)⁻¹
    rfl
  have hRadiusSq : qz.radius ^ 2 = qw.radius ^ 2 := by rw [hRadius]
  have hzClosed : z ∈ parabolicClosedBox 1 qz.radius qz.baseTime qz.center := by
    change z ∈ parabolicClosedBox 1
      (parabolicDyadicSourceBox
        (parabolicDyadicIndexContaining d z hz n)).radius
      (parabolicDyadicSourceBox
        (parabolicDyadicIndexContaining d z hz n)).baseTime
      (parabolicDyadicSourceBox
        (parabolicDyadicIndexContaining d z hz n)).center
    exact parabolicDyadicAddressContaining_mem_closedForwardBox d z hz n
  have hwClosed : w ∈ parabolicClosedBox 1 qw.radius qw.baseTime qw.center := by
    change w ∈ parabolicClosedBox 1
      (parabolicDyadicSourceBox
        (parabolicDyadicIndexContaining d w hw n)).radius
      (parabolicDyadicSourceBox
        (parabolicDyadicIndexContaining d w hw n)).baseTime
      (parabolicDyadicSourceBox
        (parabolicDyadicIndexContaining d w hw n)).center
    exact parabolicDyadicAddressContaining_mem_closedForwardBox d w hw n
  have hzClosedMem := hzClosed
  have hwClosedMem := hwClosed
  rw [mem_parabolicClosedBox_iff] at hzClosed hwClosed
  have htimeRoot : Real.sqrt |z.1 - w.1| ≤ rho := by
    dsimp only [rho, parabolicCoordinateDist]
    exact le_max_left _ _
  have htime : |z.1 - w.1| ≤ rho ^ 2 := by
    have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _) hrhoPos.le).mpr htimeRoot
    rwa [Real.sq_sqrt (abs_nonneg _)] at hsq
  have hvelocity (coordinate : Fin d) : |z.2 coordinate - w.2 coordinate| ≤ rho := by
    have hnorm : ‖z.2 - w.2‖ ≤ rho := by
      dsimp only [rho, parabolicCoordinateDist]
      exact le_max_right _ _
    have hcoordinate := (pi_norm_le_iff_of_nonneg hrhoPos.le).mp hnorm coordinate
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using hcoordinate
  have hzwTime : z.1 - w.1 ≤ rho ^ 2 := (le_abs_self _).trans htime
  have hwzTime : w.1 - z.1 ≤ rho ^ 2 := by
    nlinarith [neg_le_abs (z.1 - w.1), htime]
  have hRadiusSqLe : qz.radius ^ 2 ≤ rho ^ 2 := by
    have hnonneg : 0 ≤ (rho - qz.radius) * (rho + qz.radius) :=
      mul_nonneg (sub_nonneg.mpr hr) (add_nonneg hrhoPos.le hqzRadiusPos.le)
    nlinarith
  have hqzBase : qz.baseTime ≤ tMin + qz.radius ^ 2 + rho ^ 2 := by
    dsimp only [tMin]
    rcases le_total qz.baseTime qw.baseTime with hbase | hbase
    · rw [min_eq_left hbase]
      nlinarith [sq_nonneg qz.radius, sq_nonneg rho]
    · rw [min_eq_right hbase]
      nlinarith [hzClosed.1, hzClosed.2.1, hwClosed.1, hwClosed.2.1,
        hzwTime, hRadiusSq]
  have hqwBase : qw.baseTime ≤ tMin + qw.radius ^ 2 + rho ^ 2 := by
    dsimp only [tMin]
    rcases le_total qw.baseTime qz.baseTime with hbase | hbase
    · rw [min_eq_right hbase]
      nlinarith [sq_nonneg qw.radius, sq_nonneg rho]
    · rw [min_eq_left hbase]
      nlinarith [hzClosed.1, hzClosed.2.1, hwClosed.1, hwClosed.2.1,
        hwzTime, hRadiusSq]
  have boxEnclosure : ∀ (q : InkSpotsBox d) (c other : TimeVelocity d),
      c ∈ parabolicClosedBox 1 q.radius q.baseTime q.center →
      tMin ≤ q.baseTime →
      q.baseTime ≤ tMin + q.radius ^ 2 + rho ^ 2 →
      0 ≤ q.radius →
      q.radius ≤ rho →
      (∀ coordinate : Fin d, |c.2 coordinate - other.2 coordinate| ≤ rho) →
      c.2 + other.2 = z.2 + w.2 →
      parabolicBox 1 q.radius q.baseTime q.center ⊆
        parabolicBox 1 (3 * rho) tMin ((z.2 + w.2) / 2) ∧
      parabolicClosedBox 1 q.radius q.baseTime q.center ⊆
        parabolicClosedBox 1 (3 * rho) tMin ((z.2 + w.2) / 2) := by
    intro q c other hc hmin hbase hqRadiusNonneg hrad hcoordinate hmidpoint
    rw [mem_parabolicClosedBox_iff] at hc
    have hqRadiusSqLe : q.radius ^ 2 ≤ rho ^ 2 := by
      have hnonneg : 0 ≤ (rho - q.radius) * (rho + q.radius) :=
        mul_nonneg (sub_nonneg.mpr hrad) (add_nonneg hrhoPos.le hqRadiusNonneg)
      nlinarith
    have velocityEstimate (x : TimeVelocity d) (coordinate : Fin d) :
        |x.2 coordinate - ((z.2 + w.2) / 2) coordinate| ≤
          |x.2 coordinate - q.center coordinate| +
            |q.center coordinate - c.2 coordinate| +
              |c.2 coordinate - other.2 coordinate| / 2 := by
      have hsplit : x.2 coordinate - ((z.2 + w.2) / 2) coordinate =
          (x.2 coordinate - q.center coordinate) +
            (q.center coordinate - c.2 coordinate) +
              (c.2 coordinate - other.2 coordinate) / 2 := by
        rw [← hmidpoint]
        simp only [Pi.add_apply, Pi.div_apply, Pi.ofNat_apply]
        ring
      rw [hsplit]
      calc
        |(x.2 coordinate - q.center coordinate) +
            (q.center coordinate - c.2 coordinate) +
              (c.2 coordinate - other.2 coordinate) / 2| ≤
            |(x.2 coordinate - q.center coordinate) +
                (q.center coordinate - c.2 coordinate)| +
              |(c.2 coordinate - other.2 coordinate) / 2| := abs_add_le _ _
        _ ≤ |x.2 coordinate - q.center coordinate| +
              |q.center coordinate - c.2 coordinate| +
                |(c.2 coordinate - other.2 coordinate) / 2| := by
              linarith [abs_add_le (x.2 coordinate - q.center coordinate)
                (q.center coordinate - c.2 coordinate)]
        _ = |x.2 coordinate - q.center coordinate| +
              |q.center coordinate - c.2 coordinate| +
                |c.2 coordinate - other.2 coordinate| / 2 := by
              rw [abs_div]
              norm_num
    constructor
    · intro x hx
      rw [mem_parabolicBox_iff] at hx ⊢
      refine ⟨hmin.trans_lt hx.1, ?_, ?_⟩
      · nlinarith [sq_pos_of_pos hrhoPos]
      · rw [mem_velocityCube_iff]
        intro coordinate
        have hxCoordinate := (mem_velocityCube_iff.mp hx.2.2) coordinate
        have hcCoordinate := (mem_velocityClosedCube_iff.mp hc.2.2) coordinate
        have hcCoordinate' : |q.center coordinate - c.2 coordinate| ≤ q.radius := by
          simpa only [abs_sub_comm] using hcCoordinate
        have hotherCoordinate := hcoordinate coordinate
        have hestimate := velocityEstimate x coordinate
        calc
          |x.2 coordinate - ((z.2 + w.2) / 2) coordinate| ≤
              |x.2 coordinate - q.center coordinate| +
                |q.center coordinate - c.2 coordinate| +
                  |c.2 coordinate - other.2 coordinate| / 2 := hestimate
          _ < q.radius + q.radius + rho / 2 := by
            linarith only [hxCoordinate, hcCoordinate', hotherCoordinate]
          _ ≤ 3 * rho := by linarith only [hrad, hrhoPos.le]
    · intro x hx
      rw [mem_parabolicClosedBox_iff] at hx ⊢
      refine ⟨hmin.trans hx.1, ?_, ?_⟩
      · nlinarith [sq_nonneg rho]
      · rw [mem_velocityClosedCube_iff]
        intro coordinate
        have hxCoordinate := (mem_velocityClosedCube_iff.mp hx.2.2) coordinate
        have hcCoordinate := (mem_velocityClosedCube_iff.mp hc.2.2) coordinate
        have hcCoordinate' : |q.center coordinate - c.2 coordinate| ≤ q.radius := by
          simpa only [abs_sub_comm] using hcCoordinate
        have hotherCoordinate := hcoordinate coordinate
        have hestimate := velocityEstimate x coordinate
        calc
          |x.2 coordinate - ((z.2 + w.2) / 2) coordinate| ≤
              |x.2 coordinate - q.center coordinate| +
                |q.center coordinate - c.2 coordinate| +
                  |c.2 coordinate - other.2 coordinate| / 2 := hestimate
          _ ≤ q.radius + q.radius + rho / 2 := by
            linarith only [hxCoordinate, hcCoordinate', hotherCoordinate]
          _ ≤ 3 * rho := by linarith only [hrad, hrhoPos.le]
  have hzEnclosure := boxEnclosure qz z w hzClosedMem (min_le_left _ _) hqzBase
    hqzRadiusPos.le hr hvelocity rfl
  have hwEnclosure := boxEnclosure qw w z hwClosedMem (min_le_right _ _) hqwBase
    (by simpa only [hRadius] using hqzRadiusPos.le)
    (by change qw.radius ≤ rho; rw [← hRadius]; exact hr)
    (fun coordinate => by
      simpa only [abs_sub_comm] using hvelocity coordinate)
    (by ext coordinate; simp only [Pi.add_apply]; rw [add_comm])
  exact ⟨hzEnclosure.1, hwEnclosure.1, hzEnclosure.2, hwEnclosure.2⟩

end

end HypoellipticAleksandrov.Parabolic

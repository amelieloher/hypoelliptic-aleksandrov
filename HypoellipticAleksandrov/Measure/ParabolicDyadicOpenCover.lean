module

public import HypoellipticAleksandrov.Measure.ParabolicDyadicAddress

/-!
# Open covers from parabolic dyadic addresses

This file collects the countable boundary and first-entry infrastructure for
the parabolic dyadic address tree.  It contains no density, ink-spots, or
saturation data.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Function Topology

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/-- The part of a half-open addressed cell omitted by its open interior. -/
def parabolicDyadicAddressBoundary {d : Nat}
    (a : ParabolicDyadicAddress d) : Set (TimeVelocity d) :=
  parabolicDyadicHalfOpenCell a.2 \ parabolicDyadicOpenCell a.2

/-- The countable union of all addressed parabolic dyadic boundaries. -/
def parabolicDyadicAllBoundary (d : Nat) : Set (TimeVelocity d) :=
  ⋃ a : ParabolicDyadicAddress d, parabolicDyadicAddressBoundary a

/-- The non-root addressed cells that first become wholly contained in `U`. -/
def parabolicDyadicFirstEntry {d : Nat} (U : Set (TimeVelocity d)) :
    Set (ParabolicDyadicAddress d) :=
  fun a => match a with
    | ⟨0, _⟩ => False
    | ⟨_ + 1, index⟩ =>
        parabolicDyadicOpenCell index ⊆ U ∧
          ¬ parabolicDyadicOpenCell (parabolicDyadicParent index) ⊆ U

private theorem parabolicDyadicOpenCell_subset_of_firstEntry {d : Nat}
    {U : Set (TimeVelocity d)} {a : ParabolicDyadicAddress d}
    (ha : a ∈ parabolicDyadicFirstEntry U) : parabolicDyadicOpenCell a.2 ⊆ U := by
  rcases a with ⟨n, index⟩
  cases n with
  | zero => exact False.elim ha
  | succ n => exact ha.1

/-- The open cell of a child is contained in the open cell of its parent. -/
theorem parabolicDyadicOpenCell_child_subset {d n : Nat}
    (index : ParabolicDyadicIndex d n) (child : ParabolicDyadicChild d) :
    parabolicDyadicOpenCell (parabolicDyadicChildIndex index child) ⊆
      parabolicDyadicOpenCell index := by
  rintro ⟨time, velocity⟩ hz
  rw [mem_parabolicDyadicOpenCell_iff] at hz ⊢
  rw [parabolicDyadicTimeCode_childIndex] at hz
  constructor
  · have hpow : 0 < (4 : ℝ) ^ n := pow_pos (by norm_num) _
    have hchild : 0 ≤ (child.1.val : ℝ) := by positivity
    have htime := hz.1
    norm_num [pow_succ] at htime ⊢
    field_simp [ne_of_gt hpow] at htime ⊢
    nlinarith
  constructor
  · have hpow : 0 < (4 : ℝ) ^ n := pow_pos (by norm_num) _
    have hchild : (child.1.val : ℝ) < 4 := by exact_mod_cast child.1.isLt
    have hchild_le : (child.1.val + 1 : ℝ) ≤ 4 := by
      exact_mod_cast (Nat.succ_le_iff.mpr child.1.isLt)
    have htime := hz.2.1
    norm_num [pow_succ] at htime ⊢
    field_simp [ne_of_gt hpow] at htime ⊢
    nlinarith
  · intro coordinate
    have hpow : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) _
    have hchild : 0 ≤ ((child.2 coordinate).val : ℝ) := by positivity
    have hvelocity := hz.2.2 coordinate
    rw [parabolicDyadicVelocityCode_childIndex] at hvelocity
    constructor
    · norm_num [pow_succ] at hvelocity ⊢
      field_simp [ne_of_gt hpow] at hvelocity ⊢
      nlinarith [hvelocity.1]
    · have hchild' : ((child.2 coordinate).val : ℝ) < 2 := by
        exact_mod_cast (child.2 coordinate).isLt
      have hchild_le : ((child.2 coordinate).val + 1 : ℝ) ≤ 2 := by
        exact_mod_cast (Nat.succ_le_iff.mpr (child.2 coordinate).isLt)
      norm_num [pow_succ] at hvelocity ⊢
      field_simp [ne_of_gt hpow] at hvelocity ⊢
      nlinarith [hvelocity.2]

private theorem parabolicDyadicOpenCell_subset_truncate {d m n : Nat}
    (hmn : m ≤ n) (index : ParabolicDyadicIndex d n) :
    parabolicDyadicOpenCell index ⊆
      parabolicDyadicOpenCell (parabolicDyadicTruncate hmn index) := by
  induction n, hmn using Nat.le_induction with
  | base => exact Subset.rfl
  | succ n hmn ih =>
      calc
        parabolicDyadicOpenCell index ⊆
            parabolicDyadicOpenCell (parabolicDyadicParent index) := by
          simpa only [parabolicDyadicChildIndex_parent_last] using
            (parabolicDyadicOpenCell_child_subset
              (parabolicDyadicParent index) (index (Fin.last n)))
        _ ⊆ parabolicDyadicOpenCell
            (parabolicDyadicTruncate hmn (parabolicDyadicParent index)) :=
          ih (parabolicDyadicParent index)
        _ = parabolicDyadicOpenCell
            (parabolicDyadicTruncate (Nat.le_succ_of_le hmn) index) := by
          congr 1

/-- An open addressed cell is contained in the open cell of every ancestor. -/
theorem parabolicDyadicOpenCell_subset_of_addressPrefix {d : Nat}
    {a b : ParabolicDyadicAddress d} (hab : parabolicDyadicAddressPrefix a b) :
    parabolicDyadicOpenCell b.2 ⊆ parabolicDyadicOpenCell a.2 := by
  rcases hab with ⟨hmn, htruncate⟩
  rw [← htruncate]
  exact parabolicDyadicOpenCell_subset_truncate hmn b.2

/-- First-entry addresses are an antichain for the address-prefix relation. -/
theorem isAntichain_parabolicDyadicFirstEntry {d : Nat} (U : Set (TimeVelocity d)) :
    IsAntichain (parabolicDyadicAddressPrefix (d := d))
      (parabolicDyadicFirstEntry U) := by
  rintro ⟨m, a⟩ ha ⟨n, b⟩ hb hne hab
  cases m with
  | zero =>
      change False at ha
      exact ha
  | succ m =>
      cases n with
      | zero =>
          change False at hb
          exact hb
      | succ n =>
          change parabolicDyadicOpenCell a ⊆ U ∧
            ¬ parabolicDyadicOpenCell (parabolicDyadicParent a) ⊆ U at ha
          change parabolicDyadicOpenCell b ⊆ U ∧
            ¬ parabolicDyadicOpenCell (parabolicDyadicParent b) ⊆ U at hb
          rcases hab with ⟨hmn, htruncate⟩
          change m + 1 ≤ n + 1 at hmn
          change parabolicDyadicTruncate hmn b = a at htruncate
          by_cases hmnEq : m + 1 = n + 1
          · have hmnEq' : m = n := by omega
            subst m
            have hba : b = a := by
              calc
                b = parabolicDyadicTruncate (le_refl (n + 1)) b :=
                  (parabolicDyadicTruncate_self b).symm
                _ = a := by simpa only using htruncate
            subst a
            exact hne rfl
          · have hlt : m + 1 < n + 1 := lt_of_le_of_ne hmn hmnEq
            have hmn' : m + 1 ≤ n := Nat.lt_succ_iff.mp hlt
            have hprefix : parabolicDyadicAddressPrefix ⟨m + 1, a⟩
                ⟨n, parabolicDyadicParent b⟩ := by
              refine ⟨hmn', ?_⟩
              calc
                parabolicDyadicTruncate hmn' (parabolicDyadicParent b) =
                    parabolicDyadicTruncate (Nat.le_succ_of_le hmn') b := by
                  funext j
                  simp only [parabolicDyadicTruncate, parabolicDyadicParent]
                  apply congrArg b
                  exact Fin.ext (by rfl)
                _ = a := by simpa only using htruncate
            exact hb.2 ((parabolicDyadicOpenCell_subset_of_addressPrefix hprefix).trans ha.1)

/-- Open cells indexed by distinct first entries are pairwise disjoint. -/
theorem pairwiseDisjoint_parabolicDyadicFirstEntry_openCell {d : Nat}
    (U : Set (TimeVelocity d)) :
    (parabolicDyadicFirstEntry U).Pairwise
      (Disjoint on (fun a : ParabolicDyadicAddress d => parabolicDyadicOpenCell a.2)) := by
  rintro a ha b hb hab
  apply disjoint_parabolicDyadicOpenCell_of_incomparable
  · intro habPrefix
    exact isAntichain_parabolicDyadicFirstEntry U ha hb hab habPrefix
  · intro hbaPrefix
    exact isAntichain_parabolicDyadicFirstEntry U hb ha hab.symm hbaPrefix

/-- An open set captures an interior dyadic cell around each point off every
addressed boundary. -/
theorem exists_parabolicDyadicOpenCell_subset_of_mem_isOpen_off_boundary
    (d : Nat) (U : Set (TimeVelocity d)) (hU : IsOpen U)
    (z : TimeVelocity d) (hzRef : z ∈ parabolicDyadicReferenceCell d)
    (hzU : z ∈ U) (hzBoundary : z ∉ parabolicDyadicAllBoundary d) :
    ∃ a : ParabolicDyadicAddress d,
      z ∈ parabolicDyadicOpenCell a.2 ∧ parabolicDyadicOpenCell a.2 ⊆ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hzU)
  obtain ⟨n, htime, hvelocity⟩ :=
    ((tendsto_parabolicDyadicTimeWidth_atTop.eventually_lt_const hε).and
      (tendsto_parabolicDyadicVelocityWidth_atTop.eventually_lt_const hε)).exists
  rw [← iUnion_parabolicDyadicHalfOpenCell_eq_reference d n] at hzRef
  obtain ⟨index, hzHalf⟩ := Set.mem_iUnion.mp hzRef
  have hzOpen : z ∈ parabolicDyadicOpenCell index := by
    by_contra hzNotOpen
    apply hzBoundary
    exact Set.mem_iUnion.mpr ⟨⟨n, index⟩, ⟨hzHalf, hzNotOpen⟩⟩
  refine ⟨⟨n, index⟩, hzOpen, ?_⟩
  rintro ⟨time', velocity'⟩ hy
  apply hball
  have hyHalf : (time', velocity') ∈ parabolicDyadicHalfOpenCell index :=
    parabolicDyadicOpenCell_subset_halfOpenCell index hy
  rcases z with ⟨time, velocity⟩
  rw [Metric.mem_ball, Prod.dist_eq]
  apply max_lt
  · simpa only [Real.dist_eq, abs_sub_comm] using
      (abs_sub_le_parabolicDyadicTimeWidth index hyHalf hzHalf).trans_lt htime
  · rw [dist_pi_lt_iff hε]
    intro coordinate
    simpa only [Real.dist_eq, abs_sub_comm] using
      (abs_sub_le_parabolicDyadicVelocityWidth index coordinate hyHalf hzHalf).trans_lt hvelocity

private theorem exists_parabolicDyadicFirstEntry_of_mem_isOpen_off_boundary
    (d : Nat) (U : Set (TimeVelocity d)) (hU : IsOpen U)
    (hURef : U ⊆ parabolicDyadicOpenCell (fun i => Fin.elim0 i))
    (hRoot : ¬ parabolicDyadicOpenCell (fun i => Fin.elim0 i) ⊆ U)
    (z : TimeVelocity d) (hzU : z ∈ U) (hzBoundary : z ∉ parabolicDyadicAllBoundary d) :
    ∃ a : ParabolicDyadicAddress d,
      a ∈ parabolicDyadicFirstEntry U ∧ z ∈ parabolicDyadicOpenCell a.2 := by
  classical
  let root : ParabolicDyadicIndex d 0 := fun i => Fin.elim0 i
  have hzRoot : z ∈ parabolicDyadicOpenCell root := hURef hzU
  have hzReference : z ∈ parabolicDyadicReferenceCell d := by
    rw [← parabolicDyadicHalfOpenCell_zero_eq_reference d root]
    exact parabolicDyadicOpenCell_subset_halfOpenCell root hzRoot
  obtain ⟨address, hzAddress, hAddressU⟩ :=
    exists_parabolicDyadicOpenCell_subset_of_mem_isOpen_off_boundary
      d U hU z hzReference hzU hzBoundary
  let P : Nat → Prop := fun n => ∃ index : ParabolicDyadicIndex d n,
    z ∈ parabolicDyadicOpenCell index ∧ parabolicDyadicOpenCell index ⊆ U
  have hP : ∃ n, P n := ⟨address.1, address.2, hzAddress, hAddressU⟩
  have hnZero : Nat.find hP ≠ 0 := by
    intro hn
    have hZero : P 0 := by simpa only [hn] using Nat.find_spec hP
    obtain ⟨index, hzIndex, hIndexU⟩ := hZero
    apply hRoot
    simpa only [Subsingleton.elim index root] using hIndexU
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hnZero
  have hSucc : P (m + 1) := by simpa only [hm] using Nat.find_spec hP
  obtain ⟨index, hzIndex, hIndexU⟩ := hSucc
  refine ⟨⟨m + 1, index⟩, ?_, hzIndex⟩
  change parabolicDyadicOpenCell index ⊆ U ∧
    ¬ parabolicDyadicOpenCell (parabolicDyadicParent index) ⊆ U
  refine ⟨hIndexU, ?_⟩
  intro hParentU
  have hzChild : z ∈ parabolicDyadicOpenCell
      (parabolicDyadicChildIndex (parabolicDyadicParent index) (index (Fin.last m))) := by
    simpa only [parabolicDyadicChildIndex_parent_last] using hzIndex
  have hMin := Nat.find_min' hP (show P m from ⟨parabolicDyadicParent index,
    parabolicDyadicOpenCell_child_subset (parabolicDyadicParent index) (index (Fin.last m))
      hzChild, hParentU⟩)
  rw [hm] at hMin
  omega

/-- Subject to the root exclusion, an open subset of the root is a.e. the
union of its first-entry open cells. -/
theorem ae_eq_iUnion_parabolicDyadicFirstEntry_openCell
    (d : Nat) (U : Set (TimeVelocity d)) (hU : IsOpen U)
    (hURef : U ⊆ parabolicDyadicOpenCell (fun i => Fin.elim0 i))
    (hRoot : ¬ parabolicDyadicOpenCell (fun i => Fin.elim0 i) ⊆ U) :
    U =ᵐ[volume] ⋃ a ∈ parabolicDyadicFirstEntry U, parabolicDyadicOpenCell a.2 := by
  let V : Set (TimeVelocity d) :=
    ⋃ a ∈ parabolicDyadicFirstEntry U, parabolicDyadicOpenCell a.2
  have hVsub : V ⊆ U := by
    intro z hz
    obtain ⟨address, hzAddress⟩ := Set.mem_iUnion.mp hz
    obtain ⟨hEntry, hzAddress⟩ := Set.mem_iUnion.mp hzAddress
    exact parabolicDyadicOpenCell_subset_of_firstEntry hEntry hzAddress
  have hBoundaryZero : volume (parabolicDyadicAllBoundary d) = 0 := by
    unfold parabolicDyadicAllBoundary
    exact measure_iUnion_null fun a =>
      (ae_eq_set.mp (parabolicDyadicOpenCell_ae_eq_halfOpenCell a.2)).2
  change U =ᵐ[volume] V
  apply ae_eq_set.mpr
  constructor
  · apply measure_mono_null ?_ hBoundaryZero
    intro z hz
    by_contra hzBoundary
    obtain ⟨address, hEntry, hzAddress⟩ :=
      exists_parabolicDyadicFirstEntry_of_mem_isOpen_off_boundary
        d U hU hURef hRoot z hz.1 hzBoundary
    exact hz.2 (Set.mem_iUnion.mpr ⟨address,
      Set.mem_iUnion.mpr ⟨hEntry, hzAddress⟩⟩)
  · rw [diff_eq_empty.mpr hVsub]
    exact measure_empty

/-- The boundary discarded from one addressed half-open cell is null. -/
theorem volume_parabolicDyadicAddressBoundary_eq_zero {d : Nat}
    (a : ParabolicDyadicAddress d) :
    volume (parabolicDyadicAddressBoundary a) = 0 := by
  unfold parabolicDyadicAddressBoundary
  exact (ae_eq_set.mp (parabolicDyadicOpenCell_ae_eq_halfOpenCell a.2)).2

/-- The union of all addressed parabolic dyadic boundaries is null. -/
theorem volume_parabolicDyadicAllBoundary_eq_zero (d : Nat) :
    volume (parabolicDyadicAllBoundary d) = 0 := by
  unfold parabolicDyadicAllBoundary
  exact measure_iUnion_null fun a => volume_parabolicDyadicAddressBoundary_eq_zero a

private theorem iUnion_parabolicDyadicHalfOpenCell_eq_reference' (d : Nat) :
    (⋃ a : ParabolicDyadicAddress d, parabolicDyadicHalfOpenCell a.2) =
      parabolicDyadicReferenceCell d := by
  apply Subset.antisymm
  · intro z hz
    obtain ⟨address, hz⟩ := Set.mem_iUnion.mp hz
    exact parabolicDyadicHalfOpenCell_subset_reference address.2 hz
  · intro z hz
    let index : ParabolicDyadicIndex d 0 := fun i => Fin.elim0 i
    rw [← parabolicDyadicHalfOpenCell_zero_eq_reference d index] at hz
    exact Set.mem_iUnion.mpr ⟨⟨0, index⟩, hz⟩

/-- The countable union of all open addressed cells agrees a.e. with the
reference half-open cell. -/
theorem iUnion_parabolicDyadicOpenCell_ae_eq_reference (d : Nat) :
    (⋃ a : ParabolicDyadicAddress d, parabolicDyadicOpenCell a.2) =ᵐ[volume]
      parabolicDyadicReferenceCell d := by
  rw [← iUnion_parabolicDyadicHalfOpenCell_eq_reference' d]
  apply ae_eq_set.mpr
  constructor
  · rw [diff_eq_empty.mpr ?_]
    exact measure_empty
    exact Set.iUnion_mono fun address =>
      parabolicDyadicOpenCell_subset_halfOpenCell address.2
  · apply measure_mono_null ?_ (volume_parabolicDyadicAllBoundary_eq_zero d)
    intro z hz
    simp only [Set.mem_diff, Set.mem_iUnion] at hz
    obtain ⟨address, hzAddress⟩ := hz.1
    change z ∈ ⋃ address : ParabolicDyadicAddress d,
      parabolicDyadicHalfOpenCell address.2 \ parabolicDyadicOpenCell address.2
    exact Set.mem_iUnion.mpr ⟨address, ⟨hzAddress,
      fun hzOpen => hz.2 ⟨address, hzOpen⟩⟩⟩

end

end HypoellipticAleksandrov.Parabolic

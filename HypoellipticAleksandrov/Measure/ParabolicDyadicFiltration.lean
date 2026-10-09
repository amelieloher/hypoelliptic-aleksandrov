module

public import HypoellipticAleksandrov.Measure.ParabolicDyadicMeasure
public import Mathlib.Data.Set.Card
public import Mathlib.Probability.Process.PartitionFiltration
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# Finite parabolic dyadic filtration

This file realizes the finite dyadic filtration on the subtype of the
half-open reference cell.  Each parabolic generation is enumerated by `d + 2`
binary generators: one for each velocity child bit and two for the base-four
time child.

The checkpoint theorem identifies the atoms after a complete generator block
with the addressed half-open cells.  No conditional-expectation formula or
Borel-generation assertion is made here.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/-- The subtype carrier of the parabolic dyadic reference cell. -/
abbrev ParabolicDyadicReferenceSpace (d : ℕ) : Type :=
  {z : TimeVelocity d // z ∈ parabolicDyadicReferenceCell d}

/-- The finite restricted product volume on the reference-cell subtype. -/
def parabolicDyadicReferenceMeasure (d : ℕ) :
    Measure (ParabolicDyadicReferenceSpace d) :=
  Measure.comap Subtype.val volume

/-- The generation block containing a scheduled binary generator. -/
def parabolicDyadicGeneratorBlock (d k : ℕ) : ℕ :=
  k / (d + 2)

/-- The location of a scheduled binary generator in its generation block. -/
def parabolicDyadicGeneratorSlot (d k : ℕ) : Fin (d + 2) :=
  ⟨k % (d + 2), Nat.mod_lt _ (by omega)⟩

/-- The `bit`-th binary digit of a base-four time child. -/
def parabolicDyadicTimeChildBit (child : Fin 4) (bit : Fin 2) : Prop :=
  (child.val / 2 ^ bit.val) % 2 = 1

/-- The binary coordinate of a simultaneous parabolic child selected by a
slot in a `d + 2` generator block. -/
def parabolicDyadicChildBit {d : ℕ} (child : ParabolicDyadicChild d)
    (slot : Fin (d + 2)) : Prop :=
  Fin.addCases
    (fun coordinate => (child.2 coordinate).val = 1)
    (fun bit => parabolicDyadicTimeChildBit child.1 bit)
    slot

/-- The ambient union of all next-generation cells whose final child has the
scheduled binary value one. -/
noncomputable def parabolicDyadicGeneratorAmbient (d k : ℕ) : Set (TimeVelocity d) := by
  classical
  exact ⋃ index : ParabolicDyadicIndex d (parabolicDyadicGeneratorBlock d k + 1),
    if parabolicDyadicChildBit
        (index (Fin.last (parabolicDyadicGeneratorBlock d k)))
        (parabolicDyadicGeneratorSlot d k)
    then parabolicDyadicHalfOpenCell index else ∅

/-- The scheduled binary generator, restricted to the reference subtype. -/
def parabolicDyadicGenerator (d k : ℕ) : Set (ParabolicDyadicReferenceSpace d) :=
  Subtype.val ⁻¹' parabolicDyadicGeneratorAmbient d k

/-- An addressed half-open cell, restricted to the reference subtype. -/
def parabolicDyadicRestrictedCell {d n : ℕ}
    (index : ParabolicDyadicIndex d n) : Set (ParabolicDyadicReferenceSpace d) :=
  Subtype.val ⁻¹' parabolicDyadicHalfOpenCell index

/-- The reference-subtype measure of its whole carrier is the ambient measure
of the reference cell. -/
theorem parabolicDyadicReferenceMeasure_univ (d : ℕ) :
    parabolicDyadicReferenceMeasure d Set.univ =
      volume (parabolicDyadicReferenceCell d) := by
  simpa only [parabolicDyadicReferenceMeasure, Set.image_univ,
    Subtype.range_coe_subtype, Set.setOf_mem_eq] using
    (comap_subtype_coe_apply (measurableSet_parabolicDyadicReferenceCell d) volume
      (Set.univ : Set (ParabolicDyadicReferenceSpace d)))

/-- The total real reference-subtype volume is exactly `2^d`. -/
theorem parabolicDyadicReferenceMeasure_univ_toReal (d : ℕ) :
    (parabolicDyadicReferenceMeasure d Set.univ).toReal = (2 : ℝ) ^ d := by
  let index : ParabolicDyadicIndex d 0 := fun j => Fin.elim0 j
  rw [parabolicDyadicReferenceMeasure_univ]
  rw [← parabolicDyadicHalfOpenCell_zero_eq_reference d index]
  simpa using volume_parabolicDyadicHalfOpenCell_toReal index

/-- The finite reference-subtype volume is not infinite. -/
theorem parabolicDyadicReferenceMeasure_univ_ne_top (d : ℕ) :
    parabolicDyadicReferenceMeasure d Set.univ ≠ ∞ := by
  intro htop
  have hvolume := parabolicDyadicReferenceMeasure_univ_toReal d
  rw [htop] at hvolume
  have hpositive : 0 < (2 : ℝ) ^ d := pow_pos (by norm_num) _
  simp only [ENNReal.toReal_top] at hvolume
  exact hpositive.ne' hvolume.symm

/-- Every restricted addressed cell is measurable. -/
theorem measurableSet_parabolicDyadicRestrictedCell {d n : ℕ}
    (index : ParabolicDyadicIndex d n) :
    MeasurableSet (parabolicDyadicRestrictedCell index) :=
  measurable_subtype_coe (measurableSet_parabolicDyadicHalfOpenCell index)

/-- Every scheduled generator is measurable. -/
theorem measurableSet_parabolicDyadicGenerator (d k : ℕ) :
    MeasurableSet (parabolicDyadicGenerator d k) := by
  classical
  apply measurable_subtype_coe
  unfold parabolicDyadicGeneratorAmbient
  apply MeasurableSet.iUnion
  intro index
  split_ifs
  · exact measurableSet_parabolicDyadicHalfOpenCell index
  · exact MeasurableSet.empty

/-- The finite filtration generated by the scheduled parabolic dyadic bits. -/
def parabolicDyadicFiltration (d : ℕ) :=
  ProbabilityTheory.partitionFiltration (measurableSet_parabolicDyadicGenerator d)

/-- A point in a selected addressed cell belongs to the corresponding
scheduled generator. -/
theorem mem_parabolicDyadicGenerator_of_mem_cell {d k : ℕ}
    (index : ParabolicDyadicIndex d (parabolicDyadicGeneratorBlock d k + 1))
    (hbit : parabolicDyadicChildBit
      (index (Fin.last (parabolicDyadicGeneratorBlock d k)))
      (parabolicDyadicGeneratorSlot d k))
    (z : ParabolicDyadicReferenceSpace d)
    (hz : (z : TimeVelocity d) ∈ parabolicDyadicHalfOpenCell index) :
    z ∈ parabolicDyadicGenerator d k := by
  classical
  refine Set.mem_preimage.mpr ?_
  unfold parabolicDyadicGeneratorAmbient
  refine Set.mem_iUnion.mpr ⟨index, ?_⟩
  simp only [hbit, ↓reduceIte]
  exact hz

/-- In a fixed generation cell, membership in a scheduled generator is
equivalent to the corresponding final-child bit. -/
theorem mem_parabolicDyadicGenerator_iff_childBit_of_mem_cell {d k q : ℕ}
    (hblock : parabolicDyadicGeneratorBlock d k = q)
    (index : ParabolicDyadicIndex d (q + 1))
    (z : ParabolicDyadicReferenceSpace d)
    (hz : (z : TimeVelocity d) ∈ parabolicDyadicHalfOpenCell index) :
    z ∈ parabolicDyadicGenerator d k ↔
      parabolicDyadicChildBit
        (index (Fin.last q))
        (parabolicDyadicGeneratorSlot d k) := by
  classical
  subst q
  constructor
  · intro hgenerator
    change (z : TimeVelocity d) ∈ parabolicDyadicGeneratorAmbient d k at hgenerator
    unfold parabolicDyadicGeneratorAmbient at hgenerator
    obtain ⟨other, hother⟩ := Set.mem_iUnion.mp hgenerator
    change (z : TimeVelocity d) ∈
      if parabolicDyadicChildBit
          (other (Fin.last (parabolicDyadicGeneratorBlock d k)))
          (parabolicDyadicGeneratorSlot d k)
      then parabolicDyadicHalfOpenCell other else ∅ at hother
    by_cases hotherBit : parabolicDyadicChildBit
        (other (Fin.last (parabolicDyadicGeneratorBlock d k)))
        (parabolicDyadicGeneratorSlot d k)
    · by_contra hbit
      have hotherCell : (z : TimeVelocity d) ∈ parabolicDyadicHalfOpenCell other := by
        simpa [hotherBit] using hother
      have hne : other ≠ index := by
        intro heq
        subst other
        exact hbit hotherBit
      exact (Set.disjoint_left.mp
        (parabolicDyadicHalfOpenCell_disjoint_of_ne hne) hotherCell hz).elim
    · simp [hotherBit] at hother
  · exact fun hbit => mem_parabolicDyadicGenerator_of_mem_cell index hbit z hz

/-- Binary time-child bits separate the four time children. -/
theorem parabolicDyadicTimeChildBit_injective {child child' : Fin 4}
    (h : ∀ bit : Fin 2,
      parabolicDyadicTimeChildBit child bit ↔ parabolicDyadicTimeChildBit child' bit) :
    child = child' := by
  apply Fin.ext
  have hzero : child.val % 2 = 1 ↔ child'.val % 2 = 1 := by
    simpa [parabolicDyadicTimeChildBit] using h (0 : Fin 2)
  have hone : (child.val / 2) % 2 = 1 ↔ (child'.val / 2) % 2 = 1 := by
    simpa [parabolicDyadicTimeChildBit] using h (1 : Fin 2)
  omega

/-- The full `d + 2` bit vector separates simultaneous parabolic children. -/
theorem parabolicDyadicChildBit_injective {d : ℕ} {child child' : ParabolicDyadicChild d}
    (h : ∀ slot : Fin (d + 2),
      parabolicDyadicChildBit child slot ↔ parabolicDyadicChildBit child' slot) :
    child = child' := by
  apply Prod.ext
  · apply parabolicDyadicTimeChildBit_injective
    intro bit
    simpa only [parabolicDyadicChildBit, Fin.addCases_right] using (h (Fin.natAdd d bit))
  · funext coordinate
    have hbit := h (Fin.castAdd 2 coordinate)
    have hbit' : (child.2 coordinate).val = 1 ↔ (child'.2 coordinate).val = 1 := by
      simpa only [parabolicDyadicChildBit, Fin.addCases_left] using hbit
    apply Fin.ext
    by_cases ha : (child.2 coordinate).val = 1
    · calc
        (child.2 coordinate).val = 1 := ha
        _ = (child'.2 coordinate).val := (hbit'.mp ha).symm
    · have ha0 : (child.2 coordinate).val = 0 := by omega
      have hb0 : (child'.2 coordinate).val = 0 := by
        by_contra hb0
        have hb1 : (child'.2 coordinate).val = 1 := by omega
        exact ha (hbit'.mpr hb1)
      omega

/-- Membership in a membership-partition atom is exactly equality of all
previous generator outcomes. -/
theorem mem_memPartitionSet_iff {α : Type*} (f : ℕ → Set α) (n : ℕ)
    (a x : α) :
    x ∈ memPartitionSet f n a ↔
      ∀ k < n, (x ∈ f k ↔ a ∈ f k) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    classical
    rw [memPartitionSet_succ]
    by_cases ha : a ∈ f n
    · simp only [ha, ↓reduceIte, Set.mem_inter_iff]
      constructor
      · rintro ⟨hxn, hxf⟩ k hk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
        · exact (ih x).mp hxn k hlt
        · exact iff_of_true hxf ha
      · intro h
        refine ⟨(ih x).mpr fun k hk => h k (Nat.lt_succ_of_lt hk), ?_⟩
        exact (h n (Nat.lt_succ_self n)).mpr ha
    · simp only [ha, ↓reduceIte, Set.mem_diff]
      constructor
      · rintro ⟨hxn, hxf⟩ k hk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
        · exact (ih x).mp hxn k hlt
        · exact iff_of_false hxf ha
      · intro h
        refine ⟨(ih x).mpr fun k hk => h k (Nat.lt_succ_of_lt hk), ?_⟩
        intro hxf
        exact ha ((h n (Nat.lt_succ_self n)).mp hxf)

/-- A membership partition generated by `n` binary questions has at most
`2^n` members, including any empty branches retained by `memPartition`. -/
theorem ncard_memPartition_le {α : Type*} (f : ℕ → Set α) (n : ℕ) :
    (memPartition f n).ncard ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [memPartition_succ]
    let left : Set (Set α) := (fun u : Set α => u ∩ f n) '' memPartition f n
    let right : Set (Set α) := (fun u : Set α => u \ f n) '' memPartition f n
    have hpartition :
        {s | ∃ u ∈ memPartition f n, s = u ∩ f n ∨ s = u \ f n} = left ∪ right := by
      ext s
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_image, left, right]
      constructor
      · rintro ⟨u, hu, hs | hs⟩
        · exact Or.inl ⟨u, hu, hs.symm⟩
        · exact Or.inr ⟨u, hu, hs.symm⟩
      · rintro (⟨u, hu, hs⟩ | ⟨u, hu, hs⟩)
        · exact ⟨u, hu, Or.inl hs.symm⟩
        · exact ⟨u, hu, Or.inr hs.symm⟩
    rw [hpartition]
    calc
      (left ∪ right).ncard ≤ left.ncard + right.ncard := Set.ncard_union_le _ _
      _ ≤ (memPartition f n).ncard + (memPartition f n).ncard := by
        exact Nat.add_le_add
          (Set.ncard_image_le (finite_memPartition f n))
          (Set.ncard_image_le (finite_memPartition f n))
      _ ≤ 2 ^ n + 2 ^ n := Nat.add_le_add ih ih
      _ = 2 ^ (n + 1) := by
        rw [pow_succ, Nat.mul_comm]
        exact (two_mul (2 ^ n)).symm

/-- At a complete-generation offset, the generator block is the prescribed
generation. -/
theorem parabolicDyadicGeneratorBlock_at {d n : ℕ} (slot : Fin (d + 2)) :
    parabolicDyadicGeneratorBlock d ((d + 2) * n + slot.val) = n := by
  unfold parabolicDyadicGeneratorBlock
  rw [Nat.add_div_of_dvd_right (dvd_mul_right (d + 2) n)]
  simp [Nat.div_eq_of_lt slot.isLt]

/-- At a complete-generation offset, the generator slot is the prescribed
slot. -/
theorem parabolicDyadicGeneratorSlot_at {d n : ℕ} (slot : Fin (d + 2)) :
    parabolicDyadicGeneratorSlot d ((d + 2) * n + slot.val) = slot := by
  apply Fin.ext
  unfold parabolicDyadicGeneratorSlot
  change ((d + 2) * n + slot.val) % (d + 2) = slot.val
  simp [Nat.add_mod, slot.isLt]

/-- On a generation-`n + 1` cell, the generator in the `slot` of block `n`
reads exactly the corresponding final-child bit. -/
theorem mem_parabolicDyadicGenerator_at_iff_childBit_of_mem_cell {d n : ℕ}
    (index : ParabolicDyadicIndex d (n + 1)) (slot : Fin (d + 2))
    (z : ParabolicDyadicReferenceSpace d)
    (hz : (z : TimeVelocity d) ∈ parabolicDyadicHalfOpenCell index) :
    z ∈ parabolicDyadicGenerator d ((d + 2) * n + slot.val) ↔
      parabolicDyadicChildBit (index (Fin.last n)) slot := by
  have hmembership := mem_parabolicDyadicGenerator_iff_childBit_of_mem_cell
    (parabolicDyadicGeneratorBlock_at slot) index z hz
  rw [parabolicDyadicGeneratorSlot_at slot] at hmembership
  exact hmembership

/-- A restricted child cell is contained in its restricted parent cell. -/
theorem parabolicDyadicRestrictedCell_child_subset {d n : ℕ}
    (index : ParabolicDyadicIndex d n) (child : ParabolicDyadicChild d) :
    parabolicDyadicRestrictedCell (parabolicDyadicChildIndex index child) ⊆
      parabolicDyadicRestrictedCell index := by
  intro z hz
  exact parabolicDyadicHalfOpenCell_child_subset index child hz

/-- At generation zero the unique restricted addressed cell is the whole
reference subtype. -/
theorem parabolicDyadicRestrictedCell_zero_eq_univ (d : ℕ)
    (index : ParabolicDyadicIndex d 0) :
    parabolicDyadicRestrictedCell index = Set.univ := by
  ext z
  change (z : TimeVelocity d) ∈ parabolicDyadicHalfOpenCell index ↔ z ∈ Set.univ
  rw [parabolicDyadicHalfOpenCell_zero_eq_reference d index]
  simp only [z.property, Set.mem_univ]

/-- Every addressed half-open parabolic dyadic cell has its upper endpoint as
a point.  This also covers `d = 0`, since the velocity verification is then
vacuous. -/
theorem parabolicDyadicHalfOpenCell_nonempty {d n : ℕ}
    (index : ParabolicDyadicIndex d n) :
    (parabolicDyadicHalfOpenCell index).Nonempty := by
  refine ⟨((parabolicDyadicTimeCode n index + 1 : ℝ) / (4 : ℝ) ^ n,
    fun coordinate =>
      -1 + 2 * (parabolicDyadicVelocityCode n index coordinate + 1 : ℝ) /
        (2 : ℝ) ^ n), ?_⟩
  rw [mem_parabolicDyadicHalfOpenCell_iff]
  constructor
  · rw [mem_parabolicDyadicTimeCell_iff]
    constructor
    · have hdenom : 0 < (4 : ℝ) ^ n := pow_pos (by norm_num) n
      have hcode : (parabolicDyadicTimeCode n index : ℝ) <
          (parabolicDyadicTimeCode n index + 1 : ℝ) := by
        exact_mod_cast Nat.lt_succ_self (parabolicDyadicTimeCode n index)
      exact (div_lt_div_iff₀ hdenom hdenom).mpr
        (mul_lt_mul_of_pos_right hcode hdenom)
    · rfl
  · rw [mem_parabolicDyadicVelocityCell_iff]
    intro coordinate
    constructor
    · apply (add_lt_add_iff_left (-1)).mpr
      have hdenom : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) n
      have hcode : (parabolicDyadicVelocityCode n index coordinate : ℝ) <
          (parabolicDyadicVelocityCode n index coordinate + 1 : ℝ) := by
        exact_mod_cast Nat.lt_succ_self (parabolicDyadicVelocityCode n index coordinate)
      calc
        2 * (parabolicDyadicVelocityCode n index coordinate : ℝ) / (2 : ℝ) ^ n =
            2 * ((parabolicDyadicVelocityCode n index coordinate : ℝ) / (2 : ℝ) ^ n) := by
              ring
        _ < 2 * ((parabolicDyadicVelocityCode n index coordinate + 1 : ℝ) /
            (2 : ℝ) ^ n) := by
              exact mul_lt_mul_of_pos_left
                ((div_lt_div_iff₀ hdenom hdenom).mpr
                  (mul_lt_mul_of_pos_right hcode hdenom))
                (by norm_num)
        _ = 2 * (parabolicDyadicVelocityCode n index coordinate + 1 : ℝ) /
            (2 : ℝ) ^ n := by ring
    · rfl

private theorem parabolicDyadic_checkpoint_prefix_lt (d n k : ℕ)
    (hk : k < (d + 2) * n) :
    k < (d + 2) * (n + 1) := by
  calc
    k < (d + 2) * n := hk
    _ < (d + 2) * (n + 1) :=
      (Nat.mul_lt_mul_left (by omega : 0 < d + 2)).mpr (Nat.lt_succ_self n)

private theorem parabolicDyadic_checkpoint_slot_lt (d n k : ℕ)
    (hprevious : ¬ k < (d + 2) * n)
    (hk : k < (d + 2) * (n + 1)) :
    k - (d + 2) * n < d + 2 := by
  apply (Nat.sub_lt_iff_lt_add (Nat.le_of_not_gt hprevious)).mpr
  simpa only [Nat.mul_succ, Nat.add_comm] using hk

private theorem parabolicDyadic_checkpoint_eq_block_add_sub (d n k : ℕ)
    (hprevious : ¬ k < (d + 2) * n) :
    k = (d + 2) * n + (k - (d + 2) * n) := by
  exact (Nat.add_sub_of_le (Nat.le_of_not_gt hprevious)).symm

/-- Checkpoint atoms after `n` complete binary blocks are exactly the
generation-`n` addressed half-open cells containing their base point. -/
theorem memPartitionSet_parabolicDyadicFiltration_checkpoint_eq_cell
    {d n : ℕ} (index : ParabolicDyadicIndex d n)
    (z : ParabolicDyadicReferenceSpace d)
    (hz : (z : TimeVelocity d) ∈ parabolicDyadicHalfOpenCell index) :
    memPartitionSet (parabolicDyadicGenerator d) ((d + 2) * n) z =
      parabolicDyadicRestrictedCell index := by
  induction n generalizing z with
  | zero =>
    rw [show (d + 2) * 0 = 0 by omega, memPartitionSet_zero,
      parabolicDyadicRestrictedCell_zero_eq_univ]
  | succ n ih =>
    let parent : ParabolicDyadicIndex d n := parabolicDyadicParent index
    let child : ParabolicDyadicChild d := index (Fin.last n)
    have hchildIndex : parabolicDyadicChildIndex parent child = index := by
      exact parabolicDyadicChildIndex_parent_last index
    have hzparent : (z : TimeVelocity d) ∈ parabolicDyadicHalfOpenCell parent := by
      apply parabolicDyadicHalfOpenCell_child_subset parent child
      simpa only [hchildIndex] using hz
    have hparentAtom := ih parent z hzparent
    apply Set.Subset.antisymm
    · intro y hy
      have hsignature := (mem_memPartitionSet_iff (parabolicDyadicGenerator d)
        ((d + 2) * (n + 1)) z y).mp hy
      have hyparentAtom : y ∈ memPartitionSet (parabolicDyadicGenerator d) ((d + 2) * n) z :=
        (mem_memPartitionSet_iff (parabolicDyadicGenerator d) ((d + 2) * n) z y).mpr
          (fun k hk => hsignature k (parabolicDyadic_checkpoint_prefix_lt d n k hk))
      have hyparent : (y : TimeVelocity d) ∈ parabolicDyadicHalfOpenCell parent := by
        rw [hparentAtom] at hyparentAtom
        exact hyparentAtom
      have hycover : (y : TimeVelocity d) ∈
          ⋃ candidate : ParabolicDyadicIndex d (n + 1),
            parabolicDyadicHalfOpenCell candidate := by
        rw [iUnion_parabolicDyadicHalfOpenCell_eq_reference]
        exact y.property
      obtain ⟨candidate, hycandidate⟩ := Set.mem_iUnion.mp hycover
      have hcandidateParent : parabolicDyadicParent candidate = parent := by
        by_contra hne
        have hychild : (y : TimeVelocity d) ∈ parabolicDyadicHalfOpenCell
            (parabolicDyadicChildIndex (parabolicDyadicParent candidate)
              (candidate (Fin.last n))) := by
          rw [parabolicDyadicChildIndex_parent_last]
          exact hycandidate
        have hsubset := parabolicDyadicHalfOpenCell_child_subset
          (parabolicDyadicParent candidate) (candidate (Fin.last n)) hychild
        have hdisjoint := parabolicDyadicHalfOpenCell_disjoint_of_ne hne
        exact (Set.disjoint_left.mp hdisjoint hsubset hyparent).elim
      have hbits : ∀ slot : Fin (d + 2),
          parabolicDyadicChildBit (candidate (Fin.last n)) slot ↔
            parabolicDyadicChildBit child slot := by
        intro slot
        have hslot := hsignature ((d + 2) * n + slot.val) (by
          calc
            (d + 2) * n + slot.val < (d + 2) * n + (d + 2) :=
              Nat.add_lt_add_left slot.isLt _
            _ = (d + 2) * (n + 1) := by rw [Nat.mul_succ])
        rw [mem_parabolicDyadicGenerator_at_iff_childBit_of_mem_cell candidate slot y
          hycandidate,
          mem_parabolicDyadicGenerator_at_iff_childBit_of_mem_cell index slot z hz] at hslot
        simpa only [child] using hslot
      have hchild : candidate (Fin.last n) = child :=
        parabolicDyadicChildBit_injective hbits
      have hcandidate : candidate = index := by
        rw [← parabolicDyadicChildIndex_parent_last candidate,
          ← parabolicDyadicChildIndex_parent_last index, hcandidateParent, hchild]
      change (y : TimeVelocity d) ∈ parabolicDyadicHalfOpenCell index
      simpa only [hcandidate] using hycandidate
    · intro y hy
      change (y : TimeVelocity d) ∈ parabolicDyadicHalfOpenCell index at hy
      apply (mem_memPartitionSet_iff (parabolicDyadicGenerator d)
        ((d + 2) * (n + 1)) z y).mpr
      intro k hk
      by_cases hprevious : k < (d + 2) * n
      · have hyparent : (y : TimeVelocity d) ∈ parabolicDyadicHalfOpenCell parent := by
          apply parabolicDyadicHalfOpenCell_child_subset parent child
          simpa only [hchildIndex] using hy
        have hyparentAtom : y ∈ memPartitionSet (parabolicDyadicGenerator d) ((d + 2) * n) z := by
          rw [hparentAtom]
          exact hyparent
        exact (mem_memPartitionSet_iff (parabolicDyadicGenerator d) ((d + 2) * n) z y).mp
          hyparentAtom k hprevious
      · let slot : Fin (d + 2) := ⟨k - (d + 2) * n,
          parabolicDyadic_checkpoint_slot_lt d n k hprevious hk⟩
        have hslot : k = (d + 2) * n + slot.val := by
          dsimp [slot]
          exact parabolicDyadic_checkpoint_eq_block_add_sub d n k hprevious
        rw [hslot]
        rw [mem_parabolicDyadicGenerator_at_iff_childBit_of_mem_cell index slot y hy,
          mem_parabolicDyadicGenerator_at_iff_childBit_of_mem_cell index slot z hz]

/-- Different addresses determine different restricted half-open cells. -/
theorem parabolicDyadicRestrictedCell_injective {d n : ℕ} :
    Function.Injective
      (parabolicDyadicRestrictedCell :
        ParabolicDyadicIndex d n → Set (ParabolicDyadicReferenceSpace d)) := by
  intro index index' heq
  by_contra hne
  obtain ⟨z, hz⟩ := parabolicDyadicHalfOpenCell_nonempty index
  let z' : ParabolicDyadicReferenceSpace d :=
    ⟨z, parabolicDyadicHalfOpenCell_subset_reference index hz⟩
  have hzIndex : z' ∈ parabolicDyadicRestrictedCell index := by
    change z ∈ parabolicDyadicHalfOpenCell index
    exact hz
  have hzIndex' : z' ∈ parabolicDyadicRestrictedCell index' := by
    rw [← heq]
    exact hzIndex
  change z ∈ parabolicDyadicHalfOpenCell index' at hzIndex'
  exact (Set.disjoint_left.mp
    (parabolicDyadicHalfOpenCell_disjoint_of_ne hne) hz hzIndex').elim

/-- At every complete-generation checkpoint, the full membership-partition
family is precisely the family of restricted addressed half-open cells. -/
theorem memPartition_parabolicDyadicFiltration_checkpoint_eq_range (d n : ℕ) :
    memPartition (parabolicDyadicGenerator d) ((d + 2) * n) =
      Set.range (parabolicDyadicRestrictedCell :
        ParabolicDyadicIndex d n → Set (ParabolicDyadicReferenceSpace d)) := by
  symm
  apply Set.eq_of_subset_of_ncard_le
  · rintro cell ⟨index, rfl⟩
    obtain ⟨z, hz⟩ := parabolicDyadicHalfOpenCell_nonempty index
    let z' : ParabolicDyadicReferenceSpace d :=
      ⟨z, parabolicDyadicHalfOpenCell_subset_reference index hz⟩
    have hz' : z' ∈ parabolicDyadicRestrictedCell index := by
      change z ∈ parabolicDyadicHalfOpenCell index
      exact hz
    rw [← memPartitionSet_parabolicDyadicFiltration_checkpoint_eq_cell index z' hz']
    exact memPartitionSet_mem (parabolicDyadicGenerator d) ((d + 2) * n) z'
  · calc
      (memPartition (parabolicDyadicGenerator d) ((d + 2) * n)).ncard ≤
          2 ^ ((d + 2) * n) :=
        ncard_memPartition_le (parabolicDyadicGenerator d) ((d + 2) * n)
      _ = (Set.range (parabolicDyadicRestrictedCell :
          ParabolicDyadicIndex d n → Set (ParabolicDyadicReferenceSpace d))).ncard := by
        rw [Set.ncard_range_of_injective parabolicDyadicRestrictedCell_injective,
          Nat.card_eq_fintype_card, card_parabolicDyadicIndex_eq_two_pow]
  · exact finite_memPartition (parabolicDyadicGenerator d) ((d + 2) * n)


end

end HypoellipticAleksandrov.Parabolic

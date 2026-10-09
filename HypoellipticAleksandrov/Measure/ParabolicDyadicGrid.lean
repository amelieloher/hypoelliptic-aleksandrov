module

public import HypoellipticAleksandrov.Parabolic.HarnackGeometry
public import Mathlib.Data.Fintype.BigOperators

/-!
# Finite parabolic dyadic address grids

This file records the finite address tree for the reference rectangle
`(0, 1] × (-1, 1]^d`.  A refinement quarters time and bisects every velocity
coordinate.  Half-open cells are the exact finite partition objects; open
cells are recorded separately for later interior arguments.
-/

@[expose] public section

open MeasureTheory Set

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/-- One simultaneous parabolic refinement choice: four time children and two
velocity children in each coordinate. -/
abbrev ParabolicDyadicChild (d : ℕ) : Type :=
  Fin 4 × (Fin d → Fin 2)

/-- A generation-`n` parabolic cell is addressed by its `n` successive
refinement choices. -/
abbrev ParabolicDyadicIndex (d n : ℕ) : Type :=
  Fin n → ParabolicDyadicChild d

/-- Remove the final refinement choice from an address. -/
def parabolicDyadicParent {d n : ℕ} :
    ParabolicDyadicIndex d (n + 1) → ParabolicDyadicIndex d n :=
  fun index j => index j.castSucc

/-- Append one simultaneous refinement choice to an address. -/
def parabolicDyadicChildIndex {d n : ℕ} (index : ParabolicDyadicIndex d n)
    (child : ParabolicDyadicChild d) : ParabolicDyadicIndex d (n + 1) :=
  Fin.lastCases child index

@[simp] theorem parabolicDyadicParent_childIndex {d n : ℕ}
    (index : ParabolicDyadicIndex d n) (child : ParabolicDyadicChild d) :
    parabolicDyadicParent (parabolicDyadicChildIndex index child) = index := by
  funext j
  simp [parabolicDyadicParent, parabolicDyadicChildIndex]

@[simp] theorem parabolicDyadicChildIndex_last {d n : ℕ}
    (index : ParabolicDyadicIndex d n) (child : ParabolicDyadicChild d) :
    parabolicDyadicChildIndex index child (Fin.last n) = child := by
  simp [parabolicDyadicChildIndex]

/-- Decomposing an address into its prefix and final choice reconstructs it. -/
@[simp] theorem parabolicDyadicChildIndex_parent_last {d n : ℕ}
    (index : ParabolicDyadicIndex d (n + 1)) :
    parabolicDyadicChildIndex (parabolicDyadicParent index) (index (Fin.last n)) = index := by
  funext j
  obtain ⟨k, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last j
  · simp [parabolicDyadicParent, parabolicDyadicChildIndex]
  · simp [parabolicDyadicChildIndex]

/-- Appending a child is injective in its prefix and final choice. -/
theorem parabolicDyadicChildIndex_injective {d n : ℕ} :
    Function.Injective fun pair : ParabolicDyadicIndex d n × ParabolicDyadicChild d =>
      parabolicDyadicChildIndex pair.1 pair.2 := by
  rintro ⟨index, child⟩ ⟨index', child'⟩ h
  have hindex : index = index' := by
    simpa only [parabolicDyadicParent_childIndex] using congrArg parabolicDyadicParent h
  subst index'
  have hchild : child = child' := by
    simpa only [parabolicDyadicChildIndex_last] using congrFun h (Fin.last n)
  subst child'
  rfl

/-- Every positive-generation address has a unique prefix and final child. -/
theorem existsUnique_parabolicDyadicParent_child {d n : ℕ}
    (index : ParabolicDyadicIndex d (n + 1)) :
    ∃! pair : ParabolicDyadicIndex d n × ParabolicDyadicChild d,
      parabolicDyadicChildIndex pair.1 pair.2 = index := by
  refine ⟨(parabolicDyadicParent index, index (Fin.last n)), ?_, ?_⟩
  · exact parabolicDyadicChildIndex_parent_last index
  · intro pair hpair
    exact parabolicDyadicChildIndex_injective (hpair.trans
      (parabolicDyadicChildIndex_parent_last index).symm)

/-- The source branching number is four time choices times two choices in each
velocity coordinate. -/
theorem card_parabolicDyadicChild (d : ℕ) :
    Fintype.card (ParabolicDyadicChild d) = 4 * 2 ^ d := by
  simp [ParabolicDyadicChild]

/-- The source branching number in the paper's normalized power-of-two form. -/
theorem card_parabolicDyadicChild_eq_two_pow (d : ℕ) :
    Fintype.card (ParabolicDyadicChild d) = 2 ^ (d + 2) := by
  calc
    Fintype.card (ParabolicDyadicChild d) = 4 * 2 ^ d :=
      card_parabolicDyadicChild d
    _ = 2 ^ d * 4 := Nat.mul_comm _ _
    _ = 2 ^ d * 2 ^ 2 := by norm_num
    _ = 2 ^ (d + 2) := (pow_add 2 d 2).symm

/-- The generation-`n` address set has the expected branching cardinality. -/
theorem card_parabolicDyadicIndex (d n : ℕ) :
    Fintype.card (ParabolicDyadicIndex d n) = (4 * 2 ^ d) ^ n := by
  simp [ParabolicDyadicIndex, ParabolicDyadicChild]

/-- The generation cardinality in the paper's normalized power-of-two form. -/
theorem card_parabolicDyadicIndex_eq_two_pow (d n : ℕ) :
    Fintype.card (ParabolicDyadicIndex d n) = 2 ^ ((d + 2) * n) := by
  have hbranch : 4 * 2 ^ d = 2 ^ (d + 2) :=
    (card_parabolicDyadicChild d).symm.trans
      (card_parabolicDyadicChild_eq_two_pow d)
  calc
    Fintype.card (ParabolicDyadicIndex d n) = (4 * 2 ^ d) ^ n :=
      card_parabolicDyadicIndex d n
    _ = (2 ^ (d + 2)) ^ n := congrArg (fun cardinality : ℕ => cardinality ^ n) hbranch
    _ = 2 ^ ((d + 2) * n) := (pow_mul 2 (d + 2) n).symm

/-- Read the base-four time address from a refinement word. -/
def parabolicDyadicTimeCode {d : ℕ} : (n : ℕ) → ParabolicDyadicIndex d n → ℕ
  | 0, _ => 0
  | n + 1, index =>
      4 * parabolicDyadicTimeCode n (parabolicDyadicParent index) +
        (index (Fin.last n)).1.val

/-- Read the base-two address in one fixed velocity coordinate from a refinement word. -/
def parabolicDyadicVelocityCode {d : ℕ} : (n : ℕ) →
    ParabolicDyadicIndex d n → Fin d → ℕ
  | 0, _, _ => 0
  | n + 1, index, coordinate =>
      2 * parabolicDyadicVelocityCode n (parabolicDyadicParent index) coordinate +
        ((index (Fin.last n)).2 coordinate).val

/-- The time code lies in the base-four range for its generation. -/
theorem parabolicDyadicTimeCode_lt_pow {d n : ℕ} (index : ParabolicDyadicIndex d n) :
    parabolicDyadicTimeCode n index < 4 ^ n := by
  induction n with
  | zero => simp [parabolicDyadicTimeCode]
  | succ n ih =>
      rw [parabolicDyadicTimeCode]
      have hchild : (index (Fin.last n)).1.val < 4 := (index (Fin.last n)).1.isLt
      calc
        4 * parabolicDyadicTimeCode n (parabolicDyadicParent index) +
            (index (Fin.last n)).1.val <
            4 * parabolicDyadicTimeCode n (parabolicDyadicParent index) + 4 :=
          Nat.add_lt_add_left hchild _
        _ = 4 * (parabolicDyadicTimeCode n (parabolicDyadicParent index) + 1) := by omega
        _ ≤ 4 * 4 ^ n := Nat.mul_le_mul_left 4 (Nat.succ_le_iff.mpr
          (ih (parabolicDyadicParent index)))
        _ = 4 ^ (n + 1) := by simp [pow_succ, Nat.mul_comm]

/-- Every coordinate's velocity code lies in the base-two range for its generation. -/
theorem parabolicDyadicVelocityCode_lt_pow {d n : ℕ}
    (index : ParabolicDyadicIndex d n) (coordinate : Fin d) :
    parabolicDyadicVelocityCode n index coordinate < 2 ^ n := by
  induction n with
  | zero => simp [parabolicDyadicVelocityCode]
  | succ n ih =>
      rw [parabolicDyadicVelocityCode]
      have hchild : ((index (Fin.last n)).2 coordinate).val < 2 :=
        ((index (Fin.last n)).2 coordinate).isLt
      calc
        2 * parabolicDyadicVelocityCode n (parabolicDyadicParent index) coordinate +
            ((index (Fin.last n)).2 coordinate).val <
            2 * parabolicDyadicVelocityCode n (parabolicDyadicParent index) coordinate + 2 :=
          Nat.add_lt_add_left hchild _
        _ = 2 * (parabolicDyadicVelocityCode n (parabolicDyadicParent index) coordinate + 1) := by
          omega
        _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 (Nat.succ_le_iff.mpr
          (ih (parabolicDyadicParent index)))
        _ = 2 ^ (n + 1) := by simp [pow_succ, Nat.mul_comm]

/-- Appending a child appends its time digit in base four. -/
theorem parabolicDyadicTimeCode_childIndex {d n : ℕ}
    (index : ParabolicDyadicIndex d n) (child : ParabolicDyadicChild d) :
    parabolicDyadicTimeCode (n + 1) (parabolicDyadicChildIndex index child) =
      4 * parabolicDyadicTimeCode n index + child.1.val := by
  simp [parabolicDyadicTimeCode]

/-- Appending a child appends each velocity digit in base two. -/
theorem parabolicDyadicVelocityCode_childIndex {d n : ℕ}
    (index : ParabolicDyadicIndex d n) (child : ParabolicDyadicChild d) (coordinate : Fin d) :
    parabolicDyadicVelocityCode (n + 1) (parabolicDyadicChildIndex index child) coordinate =
      2 * parabolicDyadicVelocityCode n index coordinate + (child.2 coordinate).val := by
  simp [parabolicDyadicVelocityCode]

/-- The half-open time interval of an addressed cell in `(0, 1]`. -/
def parabolicDyadicTimeCell {d n : ℕ} (index : ParabolicDyadicIndex d n) : Set ℝ :=
  Ioc ((parabolicDyadicTimeCode n index : ℝ) / (4 : ℝ) ^ n)
    ((parabolicDyadicTimeCode n index + 1 : ℝ) / (4 : ℝ) ^ n)

/-- The half-open velocity rectangle of an addressed cell in `(-1, 1]^d`. -/
def parabolicDyadicVelocityCell {d n : ℕ} (index : ParabolicDyadicIndex d n) : Set (PDE.Vec d) :=
  Set.univ.pi fun coordinate =>
    Ioc (-1 + 2 * (parabolicDyadicVelocityCode n index coordinate : ℝ) / (2 : ℝ) ^ n)
      (-1 + 2 * (parabolicDyadicVelocityCode n index coordinate + 1 : ℝ) / (2 : ℝ) ^ n)

/-- The half-open addressed cell.  These, rather than the open cells, are the
objects that later form the exact finite partition. -/
def parabolicDyadicHalfOpenCell {d n : ℕ} (index : ParabolicDyadicIndex d n) :
    Set (TimeVelocity d) :=
  parabolicDyadicTimeCell index ×ˢ parabolicDyadicVelocityCell index

/-- The open interior of an addressed cell.  It is not asserted here to form
an exact partition. -/
def parabolicDyadicOpenCell {d n : ℕ} (index : ParabolicDyadicIndex d n) :
    Set (TimeVelocity d) :=
  Ioo ((parabolicDyadicTimeCode n index : ℝ) / (4 : ℝ) ^ n)
    ((parabolicDyadicTimeCode n index + 1 : ℝ) / (4 : ℝ) ^ n) ×ˢ
    Set.univ.pi (fun coordinate =>
      Ioo (-1 + 2 * (parabolicDyadicVelocityCode n index coordinate : ℝ) / (2 : ℝ) ^ n)
        (-1 + 2 * (parabolicDyadicVelocityCode n index coordinate + 1 : ℝ) / (2 : ℝ) ^ n))

@[simp] theorem mem_parabolicDyadicTimeCell_iff {d n : ℕ}
    {index : ParabolicDyadicIndex d n} {time : ℝ} :
    time ∈ parabolicDyadicTimeCell index ↔
      (parabolicDyadicTimeCode n index : ℝ) / (4 : ℝ) ^ n < time ∧
        time ≤ (parabolicDyadicTimeCode n index + 1 : ℝ) / (4 : ℝ) ^ n :=
  Iff.rfl

@[simp] theorem mem_parabolicDyadicVelocityCell_iff {d n : ℕ}
    {index : ParabolicDyadicIndex d n} {velocity : PDE.Vec d} :
    velocity ∈ parabolicDyadicVelocityCell index ↔
      ∀ coordinate : Fin d,
        -1 + 2 * (parabolicDyadicVelocityCode n index coordinate : ℝ) / (2 : ℝ) ^ n <
            velocity coordinate ∧
          velocity coordinate ≤
            -1 + 2 * (parabolicDyadicVelocityCode n index coordinate + 1 : ℝ) / (2 : ℝ) ^ n := by
  simp [parabolicDyadicVelocityCell]

@[simp] theorem mem_parabolicDyadicHalfOpenCell_iff {d n : ℕ}
    {index : ParabolicDyadicIndex d n} {time : ℝ} {velocity : PDE.Vec d} :
    (time, velocity) ∈ parabolicDyadicHalfOpenCell index ↔
      time ∈ parabolicDyadicTimeCell index ∧ velocity ∈ parabolicDyadicVelocityCell index :=
  Iff.rfl

@[simp] theorem mem_parabolicDyadicOpenCell_iff {d n : ℕ}
    {index : ParabolicDyadicIndex d n} {time : ℝ} {velocity : PDE.Vec d} :
    (time, velocity) ∈ parabolicDyadicOpenCell index ↔
      (parabolicDyadicTimeCode n index : ℝ) / (4 : ℝ) ^ n < time ∧
        time < (parabolicDyadicTimeCode n index + 1 : ℝ) / (4 : ℝ) ^ n ∧
          ∀ coordinate : Fin d,
            -1 + 2 * (parabolicDyadicVelocityCode n index coordinate : ℝ) / (2 : ℝ) ^ n <
                velocity coordinate ∧
              velocity coordinate <
                -1 + 2 * (parabolicDyadicVelocityCode n index coordinate + 1 : ℝ) /
                  (2 : ℝ) ^ n := by
  constructor
  · rintro ⟨⟨htlower, htupper⟩, hvelocity⟩
    refine ⟨htlower, htupper, fun coordinate => ?_⟩
    exact hvelocity coordinate trivial
  · rintro ⟨htlower, htupper, hvelocity⟩
    exact ⟨⟨htlower, htupper⟩, fun coordinate _ => hvelocity coordinate⟩

/-- Half-open time intervals of addressed cells are measurable. -/
theorem measurableSet_parabolicDyadicTimeCell {d n : ℕ}
    (index : ParabolicDyadicIndex d n) : MeasurableSet (parabolicDyadicTimeCell index) :=
  measurableSet_Ioc

/-- Half-open velocity rectangles of addressed cells are measurable. -/
theorem measurableSet_parabolicDyadicVelocityCell {d n : ℕ}
    (index : ParabolicDyadicIndex d n) : MeasurableSet (parabolicDyadicVelocityCell index) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioc

/-- Half-open addressed cells are measurable. -/
theorem measurableSet_parabolicDyadicHalfOpenCell {d n : ℕ}
    (index : ParabolicDyadicIndex d n) : MeasurableSet (parabolicDyadicHalfOpenCell index) :=
  (measurableSet_parabolicDyadicTimeCell index).prod
    (measurableSet_parabolicDyadicVelocityCell index)

/-- Open addressed cells are measurable. -/
theorem measurableSet_parabolicDyadicOpenCell {d n : ℕ}
    (index : ParabolicDyadicIndex d n) : MeasurableSet (parabolicDyadicOpenCell index) :=
  measurableSet_Ioo.prod (MeasurableSet.univ_pi fun _ => measurableSet_Ioo)

end

end HypoellipticAleksandrov.Parabolic

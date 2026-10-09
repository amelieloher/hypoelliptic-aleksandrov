module

public import HypoellipticAleksandrov.Measure.ParabolicDyadicMeasure
public import Mathlib.Basic.Countable.Basic

/-!
# Heterogeneous parabolic dyadic addresses

This module joins the finite parabolic dyadic address families across all
generations.  It records truncation, the resulting prefix order, and the cell
geometry determined solely by that order.  In particular, no density or
ink-spots data enter this API.
-/

@[expose] public section

open Set

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/-- An addressed parabolic dyadic cell together with its generation. -/
abbrev ParabolicDyadicAddress (d : Nat) : Type :=
  Sigma (ParabolicDyadicIndex d)

/-- Restrict a parabolic dyadic address to an earlier generation. -/
def parabolicDyadicTruncate {d m n : Nat} (hmn : m <= n)
    (index : ParabolicDyadicIndex d n) : ParabolicDyadicIndex d m :=
  fun j => index (j.castLE hmn)

/-- Remove `k` final refinement choices from an address. -/
def parabolicDyadicIteratedParent {d n : Nat}
    (index : ParabolicDyadicIndex d n) (k : Nat) (_hk : k <= n) :
    ParabolicDyadicIndex d (n - k) :=
  parabolicDyadicTruncate (Nat.sub_le n k) index

/-- Address `a` is a prefix of `b` when it is the truncation of `b` to the
generation of `a`. -/
def parabolicDyadicAddressPrefix {d : Nat}
    (a b : ParabolicDyadicAddress d) : Prop :=
  exists h : a.1 <= b.1, parabolicDyadicTruncate h b.2 = a.2

/-- Truncating an address to its own generation does nothing. -/
theorem parabolicDyadicTruncate_self {d n : Nat}
    (index : ParabolicDyadicIndex d n) :
    parabolicDyadicTruncate (le_refl n) index = index := by
  funext j
  simp only [parabolicDyadicTruncate]
  apply congrArg index
  exact Fin.ext (by rfl)

/-- Taking a parent commutes with truncation across one final generation. -/
theorem parabolicDyadicParent_truncate_succ {d m n : Nat}
    (hmn : m <= n) (index : ParabolicDyadicIndex d (n + 1)) :
    parabolicDyadicParent (parabolicDyadicTruncate (Nat.succ_le_succ hmn) index) =
      parabolicDyadicTruncate hmn (parabolicDyadicParent index) := by
  funext j
  simp only [parabolicDyadicTruncate, parabolicDyadicParent]
  apply congrArg index
  exact Fin.ext (by rfl)

/-- Successive truncations agree with their composite truncation. -/
theorem parabolicDyadicTruncate_trans {d l m n : Nat}
    (hlm : l <= m) (hmn : m <= n) (index : ParabolicDyadicIndex d n) :
    parabolicDyadicTruncate hlm (parabolicDyadicTruncate hmn index) =
      parabolicDyadicTruncate (hlm.trans hmn) index := by
  funext j
  simp only [parabolicDyadicTruncate]
  apply congrArg index
  exact Fin.ext (by rfl)

private theorem parabolicDyadicTruncate_le_succ_eq_truncate_parent {d m n : Nat}
    (hmn : m <= n) (index : ParabolicDyadicIndex d (n + 1)) :
    parabolicDyadicTruncate (Nat.le_succ_of_le hmn) index =
      parabolicDyadicTruncate hmn (parabolicDyadicParent index) := by
  funext j
  simp only [parabolicDyadicTruncate, parabolicDyadicParent]
  apply congrArg index
  exact Fin.ext (by rfl)

/-- Zero iterated parents leave an address unchanged. -/
theorem parabolicDyadicIteratedParent_zero {d n : Nat}
    (index : ParabolicDyadicIndex d n) :
    parabolicDyadicIteratedParent index 0 (Nat.zero_le n) = index := by
  simpa only [parabolicDyadicIteratedParent, Nat.sub_zero] using
    parabolicDyadicTruncate_self index

/-- One iterated parent is the immediate parent. -/
theorem parabolicDyadicIteratedParent_one {d n : Nat}
    (index : ParabolicDyadicIndex d (n + 1)) :
    parabolicDyadicIteratedParent index 1 (Nat.succ_le_succ (Nat.zero_le n)) =
      parabolicDyadicParent index := by
  simpa only [parabolicDyadicIteratedParent, Nat.add_sub_cancel,
    parabolicDyadicTruncate_self] using
    parabolicDyadicTruncate_le_succ_eq_truncate_parent (Nat.le_refl n) index

/-- The prefix relation is reflexive. -/
theorem parabolicDyadicAddressPrefix_refl {d : Nat} :
    ∀ a, parabolicDyadicAddressPrefix (d := d) a a := by
  rintro ⟨n, index⟩
  exact ⟨le_refl n, parabolicDyadicTruncate_self index⟩

/-- The prefix relation is transitive. -/
theorem parabolicDyadicAddressPrefix_trans {d : Nat} :
    ∀ ⦃a b c : ParabolicDyadicAddress d⦄,
      parabolicDyadicAddressPrefix a b → parabolicDyadicAddressPrefix b c →
        parabolicDyadicAddressPrefix a c := by
  rintro ⟨l, a⟩ ⟨m, b⟩ ⟨n, c⟩ ⟨hlm, hba⟩ ⟨hmn, hcb⟩
  refine ⟨hlm.trans hmn, ?_⟩
  calc
    parabolicDyadicTruncate (hlm.trans hmn) c =
        parabolicDyadicTruncate hlm (parabolicDyadicTruncate hmn c) :=
      (parabolicDyadicTruncate_trans hlm hmn c).symm
    _ = parabolicDyadicTruncate hlm b := congrArg (parabolicDyadicTruncate hlm) hcb
    _ = a := hba

/-- The prefix relation is antisymmetric. -/
theorem parabolicDyadicAddressPrefix_antisymm {d : Nat} :
    ∀ ⦃a b : ParabolicDyadicAddress d⦄,
      parabolicDyadicAddressPrefix a b → parabolicDyadicAddressPrefix b a → a = b := by
  rintro ⟨m, a⟩ ⟨n, b⟩ ⟨hmn, hba⟩ ⟨hnm, hab⟩
  have hmn_eq : m = n := Nat.le_antisymm hmn hnm
  subst n
  have hba' : parabolicDyadicTruncate (le_refl m) b = a := by
    simpa only using hba
  have hab' : parabolicDyadicTruncate (le_refl m) a = b := by
    simpa only using hab
  have hba_eq : b = a := by
    calc
      b = parabolicDyadicTruncate (le_refl m) b :=
        (parabolicDyadicTruncate_self b).symm
      _ = a := hba'
  subst b
  rfl

private theorem parabolicDyadicHalfOpenCell_subset_truncate {d m n : Nat}
    (hmn : m <= n) (index : ParabolicDyadicIndex d n) :
    parabolicDyadicHalfOpenCell index ⊆
      parabolicDyadicHalfOpenCell (parabolicDyadicTruncate hmn index) := by
  induction n, hmn using Nat.le_induction with
  | base =>
      exact Subset.rfl
  | succ n hmn ih =>
      calc
        parabolicDyadicHalfOpenCell index ⊆
            parabolicDyadicHalfOpenCell (parabolicDyadicParent index) := by
          simpa only [parabolicDyadicChildIndex_parent_last] using
            (parabolicDyadicHalfOpenCell_child_subset
              (parabolicDyadicParent index) (index (Fin.last n)))
        _ ⊆ parabolicDyadicHalfOpenCell
            (parabolicDyadicTruncate hmn (parabolicDyadicParent index)) :=
          ih (parabolicDyadicParent index)
        _ = parabolicDyadicHalfOpenCell
            (parabolicDyadicTruncate (Nat.le_succ_of_le hmn) index) := by
          calc
            parabolicDyadicHalfOpenCell
                (parabolicDyadicTruncate hmn (parabolicDyadicParent index)) =
                parabolicDyadicHalfOpenCell
                (parabolicDyadicTruncate (Nat.le_succ_of_le hmn) index) := by
                    rw [parabolicDyadicTruncate_le_succ_eq_truncate_parent]

/-- A cell is contained in every addressed ancestor cell. -/
theorem parabolicDyadicHalfOpenCell_subset_of_addressPrefix {d : Nat}
    {a b : ParabolicDyadicAddress d} (hab : parabolicDyadicAddressPrefix a b) :
    parabolicDyadicHalfOpenCell b.2 ⊆ parabolicDyadicHalfOpenCell a.2 := by
  rcases hab with ⟨hmn, htruncate⟩
  rw [← htruncate]
  exact parabolicDyadicHalfOpenCell_subset_truncate hmn b.2

/-- The open cell is contained in the corresponding half-open cell. -/
theorem parabolicDyadicOpenCell_subset_halfOpenCell {d n : Nat}
    (index : ParabolicDyadicIndex d n) :
    parabolicDyadicOpenCell index ⊆ parabolicDyadicHalfOpenCell index := by
  rintro ⟨time, velocity⟩ hz
  rw [mem_parabolicDyadicOpenCell_iff] at hz
  rw [mem_parabolicDyadicHalfOpenCell_iff, mem_parabolicDyadicTimeCell_iff,
    mem_parabolicDyadicVelocityCell_iff]
  refine ⟨⟨hz.1, hz.2.1.le⟩, fun coordinate => ?_⟩
  exact ⟨(hz.2.2 coordinate).1, (hz.2.2 coordinate).2.le⟩

/-- Two half-open addressed cells which meet have comparable addresses. -/
theorem parabolicDyadicAddressPrefix_or_prefix_of_not_disjoint_halfOpenCell
    {d : Nat} (a b : ParabolicDyadicAddress d)
    (h : ¬ Disjoint (parabolicDyadicHalfOpenCell a.2)
      (parabolicDyadicHalfOpenCell b.2)) :
    parabolicDyadicAddressPrefix a b ∨ parabolicDyadicAddressPrefix b a := by
  classical
  rcases a with ⟨m, a⟩
  rcases b with ⟨n, b⟩
  by_cases hmn : m <= n
  · by_cases htruncate : parabolicDyadicTruncate hmn b = a
    · exact Or.inl ⟨hmn, htruncate⟩
    · exfalso
      apply h
      exact (parabolicDyadicHalfOpenCell_disjoint_of_ne htruncate).symm.mono
        Subset.rfl (parabolicDyadicHalfOpenCell_subset_truncate hmn b)
  · have hnm : n <= m := Nat.le_of_not_ge hmn
    by_cases htruncate : parabolicDyadicTruncate hnm a = b
    · exact Or.inr ⟨hnm, htruncate⟩
    · exfalso
      apply h
      exact (parabolicDyadicHalfOpenCell_disjoint_of_ne htruncate).mono
        (parabolicDyadicHalfOpenCell_subset_truncate hnm a) Subset.rfl

/-- Incomparable addresses determine disjoint half-open cells. -/
theorem disjoint_parabolicDyadicHalfOpenCell_of_incomparable {d : Nat}
    {a b : ParabolicDyadicAddress d}
    (hab : ¬ parabolicDyadicAddressPrefix a b)
    (hba : ¬ parabolicDyadicAddressPrefix b a) :
    Disjoint (parabolicDyadicHalfOpenCell a.2) (parabolicDyadicHalfOpenCell b.2) := by
  classical
  by_contra hdisjoint
  rcases parabolicDyadicAddressPrefix_or_prefix_of_not_disjoint_halfOpenCell a b hdisjoint with
    hab' | hba'
  · exact hab hab'
  · exact hba hba'

/-- Incomparable addresses determine disjoint open cells. -/
theorem disjoint_parabolicDyadicOpenCell_of_incomparable {d : Nat}
    {a b : ParabolicDyadicAddress d}
    (hab : ¬ parabolicDyadicAddressPrefix a b)
    (hba : ¬ parabolicDyadicAddressPrefix b a) :
    Disjoint (parabolicDyadicOpenCell a.2) (parabolicDyadicOpenCell b.2) := by
  exact (disjoint_parabolicDyadicHalfOpenCell_of_incomparable hab hba).mono
    (parabolicDyadicOpenCell_subset_halfOpenCell a.2)
    (parabolicDyadicOpenCell_subset_halfOpenCell b.2)

/-- Heterogeneous parabolic dyadic addresses form a countable type. -/
instance parabolicDyadicAddressCountable (d : Nat) : Countable (ParabolicDyadicAddress d) := by
  infer_instance

end

end HypoellipticAleksandrov.Parabolic

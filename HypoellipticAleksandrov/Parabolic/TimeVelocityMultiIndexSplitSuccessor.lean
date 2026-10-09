module

public import HypoellipticAleksandrov.Parabolic.GenericParabolicIndexArithmetic
public import HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndexLeibniz

/-!
# Successor reindexing for time--velocity multi-indices

This file proves the coordinatewise Pascal reindexing needed after differentiating a
multi-index Leibniz sum and identifies the bounded time and velocity successors with
literal addition of their coordinate unit multi-indices.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic
open scoped BigOperators
namespace TimeVelocityMultiIndex

private abbrev SplitTail {d : ℕ} (beta : TimeVelocityMultiIndex d)
    (c : TimeVelocityCoord d) :=
  (j : {j : TimeVelocityCoord d // j ≠ c}) → Fin (beta j + 1)

private noncomputable instance splitTailCoordFintype {d : ℕ}
    (c : TimeVelocityCoord d) : Fintype {j : TimeVelocityCoord d // j ≠ c} :=
  Fintype.ofFinite _

private def mkOld {d : ℕ} (beta : TimeVelocityMultiIndex d)
    (c : TimeVelocityCoord d) (k : Fin (beta c + 1)) (a : SplitTail beta c) : Split beta :=
  fun j => ⟨if h : j = c then k else a ⟨j, h⟩, by
    by_cases h : j = c
    · subst j; simp; omega
    · simp [h]; omega⟩

private def mkSucc {d : ℕ} (beta : TimeVelocityMultiIndex d)
    (c : TimeVelocityCoord d) (k : Fin (beta c + 2)) (a : SplitTail beta c) :
    Split (beta + Pi.single c 1) := fun j =>
  ⟨if h : j = c then k else a ⟨j, h⟩, by
    by_cases h : j = c
    · subst j; simp; omega
    · simp [h]; omega⟩

@[simp] private theorem mkOld_apply_same {d : ℕ} (beta : TimeVelocityMultiIndex d)
    (c : TimeVelocityCoord d) (k : Fin (beta c + 1)) (a : SplitTail beta c) :
    ((mkOld beta c k a) c : ℕ) = k := by simp [mkOld]

@[simp] private theorem mkOld_apply_ne {d : ℕ} (beta : TimeVelocityMultiIndex d)
    (c : TimeVelocityCoord d) (k : Fin (beta c + 1)) (a : SplitTail beta c)
    (j : TimeVelocityCoord d) (h : j ≠ c) :
    ((mkOld beta c k a) j : ℕ) = a ⟨j, h⟩ := by simp [mkOld, h]

@[simp] private theorem mkSucc_apply_same {d : ℕ} (beta : TimeVelocityMultiIndex d)
    (c : TimeVelocityCoord d) (k : Fin (beta c + 2)) (a : SplitTail beta c) :
    ((mkSucc beta c k a) c : ℕ) = k := by simp [mkSucc]

@[simp] private theorem mkSucc_apply_ne {d : ℕ} (beta : TimeVelocityMultiIndex d)
    (c : TimeVelocityCoord d) (k : Fin (beta c + 2)) (a : SplitTail beta c)
    (j : TimeVelocityCoord d) (h : j ≠ c) :
    ((mkSucc beta c k a) j : ℕ) = a ⟨j, h⟩ := by simp [mkSucc, h]

private def splitAtEquiv {d : ℕ} (beta : TimeVelocityMultiIndex d)
    (c : TimeVelocityCoord d) : Split beta ≃ Fin (beta c + 1) × SplitTail beta c where
  toFun g := ⟨g c, fun j => g j⟩
  invFun p := mkOld beta c p.1 p.2
  left_inv g := by
    funext j
    apply Fin.ext
    by_cases h : j = c
    · subst j; simp
    · simp [h]
  right_inv p := by
    apply Prod.ext
    · simp [mkOld]
    · funext j
      simp [mkOld, j.2]

private def splitSuccAtEquiv {d : ℕ} (beta : TimeVelocityMultiIndex d)
    (c : TimeVelocityCoord d) :
    Split (beta + Pi.single c 1) ≃ Fin (beta c + 2) × SplitTail beta c where
  toFun g := ⟨⟨g c, by have hc := (g c).isLt; simp at hc; omega⟩,
    fun j => ⟨g j, by simpa [Pi.single_apply, j.2] using g j |>.isLt⟩⟩
  invFun p := mkSucc beta c p.1 p.2
  left_inv g := by
    funext j
    by_cases h : j = c
    · subst j
      apply Fin.ext
      simp
    · apply Fin.ext
      simp [h]
  right_inv p := by
    apply Prod.ext
    · apply Fin.ext
      simp
    · funext j
      apply Fin.ext
      simp [j.2]

@[simp] private theorem splitAtEquiv_symm_apply {d : ℕ}
    (beta : TimeVelocityMultiIndex d) (c : TimeVelocityCoord d)
    (p : Fin (beta c + 1) × SplitTail beta c) :
    (splitAtEquiv beta c).symm p = mkOld beta c p.1 p.2 := rfl

@[simp] private theorem splitSuccAtEquiv_symm_apply {d : ℕ}
    (beta : TimeVelocityMultiIndex d) (c : TimeVelocityCoord d)
    (p : Fin (beta c + 2) × SplitTail beta c) :
    (splitSuccAtEquiv beta c).symm p = mkSucc beta c p.1 p.2 := rfl

private noncomputable def tailChoose {d : ℕ} (beta : TimeVelocityMultiIndex d)
    (c : TimeVelocityCoord d) (a : SplitTail beta c) : ℕ :=
  ∏ j : {j : TimeVelocityCoord d // j ≠ c},
    Nat.choose (beta (j : TimeVelocityCoord d)) (a j)

private theorem choose_mkOld {d : ℕ} (beta : TimeVelocityMultiIndex d)
    (c : TimeVelocityCoord d) (k : Fin (beta c + 1)) (a : SplitTail beta c) :
    beta.choose (mkOld beta c k a).left =
      Nat.choose (beta c) k * tailChoose beta c a := by
  classical
  unfold choose tailChoose
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ c)]
  rw [Finset.sdiff_singleton_eq_erase]
  rw [Finset.prod_subtype (p := fun j => j ≠ c) (s := Finset.univ.erase c)]
  · congr 1
    · simp [Split.left]
    apply Finset.prod_congr rfl
    intro j hj
    congr 1
    exact mkOld_apply_ne beta c k a j j.2
  · intro j
    simp

private theorem choose_mkSucc {d : ℕ} (beta : TimeVelocityMultiIndex d)
    (c : TimeVelocityCoord d) (k : Fin (beta c + 2)) (a : SplitTail beta c) :
    (beta + Pi.single c 1).choose (mkSucc beta c k a).left =
      Nat.choose (beta c + 1) k * tailChoose beta c a := by
  classical
  unfold choose tailChoose
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ c)]
  rw [Finset.sdiff_singleton_eq_erase]
  rw [Finset.prod_subtype (p := fun j => j ≠ c) (s := Finset.univ.erase c)]
  · congr 1
    · simp [Split.left]
    apply Finset.prod_congr rfl
    intro j hj
    simp only [Pi.add_apply, Pi.single_apply, if_neg j.2, add_zero]
    congr 1
    exact mkSucc_apply_ne beta c k a j j.2
  · intro j
    simp

private theorem mkSucc_left_eq_old_left_add {d : ℕ} (beta : TimeVelocityMultiIndex d)
    (c : TimeVelocityCoord d) (k : Fin (beta c + 1)) (a : SplitTail beta c) :
    (mkSucc beta c ⟨k + 1, by omega⟩ a).left =
      (mkOld beta c k a).left + Pi.single c 1 := by
  funext j
  change ((mkSucc beta c ⟨k + 1, by omega⟩ a) j : ℕ) =
    ((mkOld beta c k a) j : ℕ) + (Pi.single c 1 : TimeVelocityMultiIndex d) j
  by_cases h : j = c
  · subst j
    simp
  · simp [h]

private theorem mkSucc_right_eq_old_right {d : ℕ} (beta : TimeVelocityMultiIndex d)
    (c : TimeVelocityCoord d) (k : Fin (beta c + 1)) (a : SplitTail beta c) :
    (mkSucc beta c ⟨k + 1, by omega⟩ a).right = (mkOld beta c k a).right := by
  funext j
  change (beta + Pi.single c 1 : TimeVelocityMultiIndex d) j -
      (mkSucc beta c ⟨k + 1, by omega⟩ a) j =
    beta j - (mkOld beta c k a) j
  by_cases h : j = c
  · subst j
    simp
  · simp [h]

private theorem mkSucc_left_eq_old_left {d : ℕ} (beta : TimeVelocityMultiIndex d)
    (c : TimeVelocityCoord d) (k : Fin (beta c + 1)) (a : SplitTail beta c) :
    (mkSucc beta c ⟨k, by omega⟩ a).left = (mkOld beta c k a).left := by
  funext j
  change ((mkSucc beta c ⟨k, by omega⟩ a) j : ℕ) = (mkOld beta c k a) j
  by_cases h : j = c
  · subst j; simp
  · simp [h]

private theorem mkSucc_right_eq_old_right_add {d : ℕ} (beta : TimeVelocityMultiIndex d)
    (c : TimeVelocityCoord d) (k : Fin (beta c + 1)) (a : SplitTail beta c) :
    (mkSucc beta c ⟨k, by omega⟩ a).right =
      (mkOld beta c k a).right + Pi.single c 1 := by
  funext j
  change (beta + Pi.single c 1 : TimeVelocityMultiIndex d) j -
      (mkSucc beta c ⟨k, by omega⟩ a) j =
    beta j - (mkOld beta c k a) j + (Pi.single c 1 : TimeVelocityMultiIndex d) j
  by_cases h : j = c
  · subst j
    simp
    have := k.isLt
    omega
  · simp [h]

private def finRangeRep (m i : ℕ) : Fin (m + 1) :=
  ⟨i % (m + 1), Nat.mod_lt _ (by omega)⟩

@[simp] private theorem finRangeRep_val {m i : ℕ} (hi : i < m + 1) :
    (finRangeRep m i : ℕ) = i := by
  simp [finRangeRep, Nat.mod_eq_of_lt hi]

private theorem sum_fin_eq_sum_range_rep
    {M : Type*} [AddCommMonoid M] {m : ℕ} (f : Fin (m + 1) → M) :
    (∑ k, f k) = ∑ i ∈ Finset.range (m + 1), f (finRangeRep m i) := by
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [dif_pos (Finset.mem_range.mp hi)]
  congr 1
  apply Fin.ext
  simp [finRangeRep, Nat.mod_eq_of_lt (Finset.mem_range.mp hi)]

/-- Pascal reindexing of the two differentiated sides of a split sum. -/
theorem sum_choose_split_add_single
    {d : ℕ} (beta : TimeVelocityMultiIndex d) (c : TimeVelocityCoord d)
    (F : TimeVelocityMultiIndex d → TimeVelocityMultiIndex d → ℝ) :
    (∑ gamma : Split beta, (beta.choose gamma.left : ℝ) *
      (F (gamma.left + Pi.single c 1) gamma.right +
        F gamma.left (gamma.right + Pi.single c 1))) =
      ∑ delta : Split (beta + Pi.single c 1),
        ((beta + Pi.single c 1).choose delta.left : ℝ) * F delta.left delta.right := by
  classical
  let lhsTerm := fun gamma : Split beta => (beta.choose gamma.left : ℝ) *
      (F (gamma.left + Pi.single c 1) gamma.right +
        F gamma.left (gamma.right + Pi.single c 1))
  let rhsTerm := fun delta : Split (beta + Pi.single c 1) =>
    ((beta + Pi.single c 1).choose delta.left : ℝ) * F delta.left delta.right
  change (∑ gamma, lhsTerm gamma) = ∑ delta, rhsTerm delta
  have hleft : (∑ gamma, lhsTerm gamma) =
      ∑ p, lhsTerm ((splitAtEquiv beta c).symm p) :=
    (Equiv.sum_comp (splitAtEquiv beta c).symm lhsTerm).symm
  have hright : (∑ delta, rhsTerm delta) =
      ∑ p, rhsTerm ((splitSuccAtEquiv beta c).symm p) :=
    (Equiv.sum_comp (splitSuccAtEquiv beta c).symm rhsTerm).symm
  rw [hleft, hright]
  dsimp only [lhsTerm, rhsTerm]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp_rw [splitAtEquiv_symm_apply, splitSuccAtEquiv_symm_apply,
    choose_mkOld, choose_mkSucc]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [sum_fin_eq_sum_range_rep, sum_fin_eq_sum_range_rep]
  rw [Finset.sum_congr rfl (by
    intro k hk
    rw [finRangeRep_val (Finset.mem_range.mp hk)])]
  conv_rhs =>
    rw [Finset.sum_congr rfl (by
      intro k hk
      rw [finRangeRep_val (Finset.mem_range.mp hk)])]
  simp_rw [Nat.cast_mul, mul_assoc]
  rw [Finset.sum_choose_succ_mul
    (f := fun i j => (tailChoose beta c a : ℝ) *
      F (mkSucc beta c (finRangeRep (beta c + 1) i) a).left
        (mkSucc beta c (finRangeRep (beta c + 1) i) a).right) (beta c)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < beta c + 1 := Finset.mem_range.mp hk
  have hk0succ : k < (beta c + 1) + 1 := by omega
  have hk1succ : k + 1 < (beta c + 1) + 1 := by omega
  have hrep0 : finRangeRep (beta c + 1) k =
      ⟨(finRangeRep (beta c) k : ℕ), by omega⟩ := by
    apply Fin.ext
    change (finRangeRep (beta c + 1) k : ℕ) =
      (finRangeRep (beta c) k : ℕ)
    rw [finRangeRep_val hk0succ, finRangeRep_val hk']
  have hrep1 : finRangeRep (beta c + 1) (k + 1) =
      ⟨(finRangeRep (beta c) k : ℕ) + 1, by omega⟩ := by
    apply Fin.ext
    change (finRangeRep (beta c + 1) (k + 1) : ℕ) =
      (finRangeRep (beta c) k : ℕ) + 1
    rw [finRangeRep_val hk1succ, finRangeRep_val hk']
  rw [hrep0, hrep1]
  rw [mul_add, mul_add]
  rw [mkSucc_left_eq_old_left, mkSucc_right_eq_old_right_add,
    mkSucc_left_eq_old_left_add, mkSucc_right_eq_old_right]
  ring

end TimeVelocityMultiIndex

namespace ParabolicDerivativeIndex

@[simp] theorem coe_timeSucc_eq_add_single
    {d L : ℕ} (beta : ParabolicDerivativeIndex d L)
    (h : beta.1.parabolicWeight + 2 ≤ L) :
    (timeSucc beta h).1 =
      beta.1 + Pi.single (timeCoord d) 1 := by
  classical
  funext c
  rcases c with _ | i
  · simp [timeSucc, TimeVelocityMultiIndex.ofTimeVelocity,
      TimeVelocityMultiIndex.timeOrder, timeCoord]
  · simp [timeSucc, TimeVelocityMultiIndex.ofTimeVelocity,
      TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity,
      timeCoord, velocityCoord]

@[simp] theorem coe_velocitySucc_eq_add_single
    {d L : ℕ} (beta : ParabolicDerivativeIndex d L)
    (i : Fin d)
    (h : beta.1.parabolicWeight + 1 ≤ L) :
    (velocitySucc beta i h).1 =
      beta.1 + Pi.single (velocityCoord i) 1 := by
  classical
  funext c
  rcases c with _ | j
  · simp [velocitySucc, TimeVelocityMultiIndex.ofTimeVelocity,
      TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity,
      timeCoord, velocityCoord]
  · by_cases hji : j = i
    · subst j
      simp [velocitySucc, TimeVelocityMultiIndex.ofTimeVelocity,
        TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity,
        timeCoord, velocityCoord]
    · simp [velocitySucc, TimeVelocityMultiIndex.ofTimeVelocity,
        TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity,
        timeCoord, velocityCoord, hji]

end ParabolicDerivativeIndex
end HypoellipticAleksandrov.Parabolic

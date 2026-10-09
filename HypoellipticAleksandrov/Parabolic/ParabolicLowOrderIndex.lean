module

public import HypoellipticAleksandrov.Parabolic.ParabolicDerivativeIndex
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Tactic

/-!
# Parabolic multi-indices of weight at most two

This module gives the canonical classification of time--velocity multi-indices
whose parabolic weight is at most two.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic.ParabolicDerivativeIndex

/-- Canonical shapes of parabolic multi-indices of weight at most two. -/
inductive LowOrderClass (d : ℕ) where
  | zero
  | time
  | velocity (i : Fin d)
  | velocity₂ (i j : Fin d) (hij : i ≤ j)
  deriving DecidableEq, Fintype

/-- The zero index at parabolic bound two. -/
def zeroTwo (d : ℕ) : ParabolicDerivativeIndex d 2 :=
  ParabolicDerivativeIndex.zero d 2

/-- The single time derivative at parabolic bound two. -/
def timeOne (d : ℕ) : ParabolicDerivativeIndex d 2 :=
  ParabolicDerivativeIndex.timeSucc (zeroTwo d) (by
    simp [zeroTwo, TimeVelocityMultiIndex.parabolicWeight,
      VelocityMultiIndex.parabolicWeight, VelocityMultiIndex.order,
      TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity])

/-- A single velocity derivative at parabolic bound two. -/
def velocityOne {d : ℕ} (i : Fin d) :
    ParabolicDerivativeIndex d 2 :=
  ParabolicDerivativeIndex.velocitySucc (zeroTwo d) i (by
    simp [zeroTwo, TimeVelocityMultiIndex.parabolicWeight,
      VelocityMultiIndex.parabolicWeight, VelocityMultiIndex.order,
      TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity])

/-- Two successive velocity derivatives at parabolic bound two, first in
coordinate `i` and then in coordinate `j`. -/
def velocityTwo {d : ℕ} (i j : Fin d) :
    ParabolicDerivativeIndex d 2 :=
  ParabolicDerivativeIndex.velocitySucc (velocityOne i) j (by
    unfold velocityOne
    rw [parabolicWeight_velocitySucc]
    simp [zeroTwo, TimeVelocityMultiIndex.parabolicWeight,
      VelocityMultiIndex.parabolicWeight, VelocityMultiIndex.order,
      TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity])

/-- Interpret a canonical low-order shape as its bounded multi-index. -/
def LowOrderClass.toIndex {d : ℕ} :
    LowOrderClass d → ParabolicDerivativeIndex d 2
  | .zero => zeroTwo d
  | .time => timeOne d
  | .velocity i => velocityOne i
  | .velocity₂ i j _ => velocityTwo i j

@[simp] theorem coe_zeroTwo (d : ℕ) :
    (zeroTwo d).1 = (0 : TimeVelocityMultiIndex d) :=
  rfl

@[simp] theorem coe_timeOne (d : ℕ) :
    (timeOne d).1 = TimeVelocityMultiIndex.ofTimeVelocity 1 0 :=
  rfl

@[simp] theorem coe_velocityOne {d : ℕ} (i : Fin d) :
    (velocityOne i).1 =
      TimeVelocityMultiIndex.ofTimeVelocity 0 (Pi.single i 1) :=
  rfl

@[simp] theorem coe_velocityTwo {d : ℕ} (i j : Fin d) :
    (velocityTwo i j).1 =
      TimeVelocityMultiIndex.ofTimeVelocity 0
        (Function.update (Pi.single i 1) j
          ((Pi.single i 1 : Fin d → ℕ) j + 1)) :=
  rfl

@[simp] theorem LowOrderClass.toIndex_zero (d : ℕ) :
    (LowOrderClass.zero : LowOrderClass d).toIndex = zeroTwo d :=
  rfl

@[simp] theorem LowOrderClass.toIndex_time (d : ℕ) :
    (LowOrderClass.time : LowOrderClass d).toIndex = timeOne d :=
  rfl

@[simp] theorem LowOrderClass.toIndex_velocity
    {d : ℕ} (i : Fin d) :
    (LowOrderClass.velocity i).toIndex = velocityOne i :=
  rfl

@[simp] theorem LowOrderClass.toIndex_velocity₂
    {d : ℕ} (i j : Fin d) (hij : i ≤ j) :
    (LowOrderClass.velocity₂ i j hij).toIndex = velocityTwo i j :=
  rfl

private noncomputable def velocityMultiset {d : ℕ}
    (alpha : Fin d → ℕ) : Multiset (Fin d) :=
  Finsupp.toMultiset (Finsupp.equivFunOnFinite.symm alpha)

private theorem count_velocityMultiset {d : ℕ}
    (alpha : Fin d → ℕ) (i : Fin d) :
    (velocityMultiset alpha).count i = alpha i := by
  simp [velocityMultiset]

private theorem card_velocityMultiset {d : ℕ} (alpha : Fin d → ℕ) :
    (velocityMultiset alpha).card = VelocityMultiIndex.order alpha := by
  classical
  simp [velocityMultiset, VelocityMultiIndex.order, Finsupp.card_toMultiset,
    Finsupp.sum_fintype]

private theorem count_singleton_eq_piSingle {d : ℕ} (i a : Fin d) :
    ({i} : Multiset (Fin d)).count a =
      (Pi.single i 1 : Fin d → ℕ) a := by
  by_cases h : a = i <;> simp [Pi.single_apply, h]

private theorem count_pair_eq_update {d : ℕ} (i j a : Fin d) :
    ({i, j} : Multiset (Fin d)).count a =
      Function.update (Pi.single i 1 : Fin d → ℕ) j
        ((Pi.single i 1 : Fin d → ℕ) j + 1) a := by
  by_cases haj : a = j
  · subst a
    by_cases hji : j = i <;> simp [Pi.single_apply, hji]
  · by_cases hai : a = i
    · subst a
      simp [haj]
    · simp [Pi.single_apply, haj, hai]

private theorem ofTimeVelocity_zero (d : ℕ) :
    TimeVelocityMultiIndex.ofTimeVelocity 0 0 =
      (0 : TimeVelocityMultiIndex d) := by
  funext c
  cases c <;> rfl

private theorem velocityMultiset_two {d : ℕ} (i j : Fin d) :
    velocityMultiset (velocityTwo i j).1.velocity = {i, j} := by
  ext a
  rw [count_velocityMultiset, count_pair_eq_update]
  rfl

private theorem velocityTwo_class_eq_of_pair_eq {d : ℕ} {i j k l : Fin d}
    (hij : i ≤ j) (hkl : k ≤ l)
    (hpair : ({i, j} : Multiset (Fin d)) = {k, l}) :
    LowOrderClass.velocity₂ i j hij = LowOrderClass.velocity₂ k l hkl := by
  rcases Multiset.cons_eq_cons.mp hpair with hsame | hswap
  · obtain ⟨rfl, hjl⟩ := hsame
    have : j = l := by simpa using hjl
    subst l
    rfl
  · obtain ⟨_, cs, hj, hl⟩ := hswap
    have hcard : cs.card = 0 := by
      have hc := congrArg Multiset.card hj
      simpa using hc
    have hcs : cs = 0 := Multiset.card_eq_zero.mp hcard
    subst cs
    have hjk : j = k := by simpa using hj
    have hli : l = i := by simpa using hl
    subst k
    subst l
    have hij' : i = j := le_antisymm hij hkl
    subst j
    rfl

/-- Canonical low-order shapes classify bounded indices of weight at most
two bijectively. -/
theorem LowOrderClass.toIndex_bijective (d : ℕ) :
    Function.Bijective (@LowOrderClass.toIndex d) := by
  classical
  constructor
  · intro s t h
    cases s with
    | zero =>
        cases t with
        | zero => rfl
        | time =>
          have hq := congrArg (fun b => b.1.timeOrder) h
          simp [LowOrderClass.toIndex, zeroTwo, timeOne] at hq
        | velocity i =>
          have hi := congrArg (fun b => b.1.velocity i) h
          simp [LowOrderClass.toIndex, zeroTwo, velocityOne] at hi
        | velocity₂ i j hij =>
          have hw := congrArg (fun b => b.1.parabolicWeight) h
          rw [LowOrderClass.toIndex_zero, LowOrderClass.toIndex_velocity₂] at hw
          change (zeroTwo d).1.parabolicWeight =
            (velocityTwo i j).1.parabolicWeight at hw
          simp only [velocityTwo] at hw
          rw [parabolicWeight_velocitySucc] at hw
          simp only [velocityOne] at hw
          simp only [parabolicWeight_velocitySucc] at hw
          have hz : (zeroTwo d).1.parabolicWeight = 0 := by
            simp [zeroTwo, TimeVelocityMultiIndex.parabolicWeight,
              VelocityMultiIndex.parabolicWeight, VelocityMultiIndex.order,
              TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity]
          omega
    | time =>
        cases t with
        | zero =>
          have hq := congrArg (fun b => b.1.timeOrder) h
          simp [LowOrderClass.toIndex, zeroTwo, timeOne] at hq
        | time => rfl
        | velocity i =>
          have hq := congrArg (fun b => b.1.timeOrder) h
          simp [LowOrderClass.toIndex, timeOne, velocityOne] at hq
        | velocity₂ i j hij =>
          have hq := congrArg (fun b => b.1.timeOrder) h
          simp [LowOrderClass.toIndex, timeOne, velocityTwo, velocityOne] at hq
    | velocity i =>
        cases t with
        | zero =>
          have hi := congrArg (fun b => b.1.velocity i) h
          simp [LowOrderClass.toIndex, zeroTwo, velocityOne] at hi
        | time =>
          have hq := congrArg (fun b => b.1.timeOrder) h
          simp [LowOrderClass.toIndex, timeOne, velocityOne] at hq
        | velocity k =>
          have hv : Pi.single i 1 = Pi.single k 1 :=
            congrArg (fun b => b.1.velocity) h
          have hik : i = k := by
            by_contra hne
            have hi := congrFun hv i
            simp [hne] at hi
          subst k
          rfl
        | velocity₂ k l hkl =>
          have hw := congrArg (fun b => b.1.parabolicWeight) h
          rw [LowOrderClass.toIndex_velocity,
            LowOrderClass.toIndex_velocity₂] at hw
          change (velocityOne i).1.parabolicWeight =
            (velocityTwo k l).1.parabolicWeight at hw
          simp only [velocityTwo] at hw
          rw [parabolicWeight_velocitySucc] at hw
          simp only [velocityOne] at hw
          simp only [parabolicWeight_velocitySucc] at hw
          have hz : (zeroTwo d).1.parabolicWeight = 0 := by
            simp [zeroTwo, TimeVelocityMultiIndex.parabolicWeight,
              VelocityMultiIndex.parabolicWeight, VelocityMultiIndex.order,
              TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity]
          omega
    | velocity₂ i j hij =>
        cases t with
        | zero =>
          have hw := congrArg (fun b => b.1.parabolicWeight) h
          rw [LowOrderClass.toIndex_velocity₂, LowOrderClass.toIndex_zero] at hw
          change (velocityTwo i j).1.parabolicWeight =
            (zeroTwo d).1.parabolicWeight at hw
          simp only [velocityTwo] at hw
          rw [parabolicWeight_velocitySucc] at hw
          simp only [velocityOne] at hw
          simp only [parabolicWeight_velocitySucc] at hw
          have hz : (zeroTwo d).1.parabolicWeight = 0 := by
            simp [zeroTwo, TimeVelocityMultiIndex.parabolicWeight,
              VelocityMultiIndex.parabolicWeight, VelocityMultiIndex.order,
              TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity]
          omega
        | time =>
          have hq := congrArg (fun b => b.1.timeOrder) h
          simp [LowOrderClass.toIndex, timeOne, velocityTwo, velocityOne] at hq
        | velocity k =>
          have hw := congrArg (fun b => b.1.parabolicWeight) h
          rw [LowOrderClass.toIndex_velocity₂,
            LowOrderClass.toIndex_velocity] at hw
          change (velocityTwo i j).1.parabolicWeight =
            (velocityOne k).1.parabolicWeight at hw
          simp only [velocityTwo] at hw
          rw [parabolicWeight_velocitySucc] at hw
          simp only [velocityOne] at hw
          simp only [parabolicWeight_velocitySucc] at hw
          have hz : (zeroTwo d).1.parabolicWeight = 0 := by
            simp [zeroTwo, TimeVelocityMultiIndex.parabolicWeight,
              VelocityMultiIndex.parabolicWeight, VelocityMultiIndex.order,
              TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity]
          omega
        | velocity₂ k l hkl =>
          apply velocityTwo_class_eq_of_pair_eq hij hkl
          have hm := congrArg (fun b => velocityMultiset b.1.velocity) h
          rw [LowOrderClass.toIndex_velocity₂,
            LowOrderClass.toIndex_velocity₂] at hm
          simpa only [velocityMultiset_two] using hm
  · intro beta
    let q := beta.1.timeOrder
    let alpha := beta.1.velocity
    let m := velocityMultiset alpha
    have hbound : 2 * q + m.card ≤ 2 := by
      simpa [q, m, alpha, TimeVelocityMultiIndex.parabolicWeight,
        VelocityMultiIndex.parabolicWeight, card_velocityMultiset] using beta.2
    have hqle : q ≤ 1 := by omega
    have hqeq : beta.1.timeOrder = q := rfl
    interval_cases q
    · have hmle : m.card ≤ 2 := by omega
      interval_cases hc : m.card
      · have hm : m = 0 := Multiset.card_eq_zero.mp hc
        refine ⟨LowOrderClass.zero, Subtype.ext ?_⟩
        rw [← TimeVelocityMultiIndex.ofTimeVelocity_timeOrder_velocity beta.1, hqeq]
        change (zeroTwo d).1 = _
        rw [coe_zeroTwo]
        symm
        rw [← ofTimeVelocity_zero d]
        apply congrArg (TimeVelocityMultiIndex.ofTimeVelocity 0)
        funext a
        have ha := congrArg (fun z : Multiset (Fin d) => z.count a) hm
        have ha' : beta.1.velocity a = 0 := by
          simpa [m, count_velocityMultiset, alpha] using ha
        simpa using ha'
      · obtain ⟨i, hm⟩ := Multiset.card_eq_one.mp hc
        refine ⟨LowOrderClass.velocity i, Subtype.ext ?_⟩
        rw [← TimeVelocityMultiIndex.ofTimeVelocity_timeOrder_velocity beta.1, hqeq]
        change (velocityOne i).1 = _
        rw [coe_velocityOne]
        symm
        apply congrArg (TimeVelocityMultiIndex.ofTimeVelocity 0)
        funext a
        have ha := congrArg (fun z : Multiset (Fin d) => z.count a) hm
        have ha' : beta.1.velocity a = ({i} : Multiset (Fin d)).count a := by
          simpa [m, count_velocityMultiset, alpha] using ha
        exact ha'.trans (count_singleton_eq_piSingle i a)
      · obtain ⟨i, j, hm⟩ := Multiset.card_eq_two.mp hc
        rcases le_total i j with hij | hji
        · refine ⟨LowOrderClass.velocity₂ i j hij, Subtype.ext ?_⟩
          rw [← TimeVelocityMultiIndex.ofTimeVelocity_timeOrder_velocity beta.1, hqeq]
          change (velocityTwo i j).1 = _
          rw [coe_velocityTwo]
          symm
          apply congrArg (TimeVelocityMultiIndex.ofTimeVelocity 0)
          funext a
          have ha := congrArg (fun z : Multiset (Fin d) => z.count a) hm
          have ha' : beta.1.velocity a = ({i, j} : Multiset (Fin d)).count a := by
            simpa [m, count_velocityMultiset, alpha] using ha
          exact ha'.trans (count_pair_eq_update i j a)
        · refine ⟨LowOrderClass.velocity₂ j i hji, Subtype.ext ?_⟩
          rw [← TimeVelocityMultiIndex.ofTimeVelocity_timeOrder_velocity beta.1, hqeq]
          change (velocityTwo j i).1 = _
          rw [coe_velocityTwo]
          symm
          apply congrArg (TimeVelocityMultiIndex.ofTimeVelocity 0)
          funext a
          have ha := congrArg (fun z : Multiset (Fin d) => z.count a) hm
          have ha' : beta.1.velocity a = ({i, j} : Multiset (Fin d)).count a := by
            simpa [m, count_velocityMultiset, alpha] using ha
          calc
            beta.1.velocity a = ({i, j} : Multiset (Fin d)).count a := ha'
            _ = ({j, i} : Multiset (Fin d)).count a := by
              rw [Multiset.pair_comm]
            _ = Function.update (Pi.single j 1 : Fin d → ℕ) i
                ((Pi.single j 1 : Fin d → ℕ) i + 1) a :=
              count_pair_eq_update j i a
    · have hm : m.card = 0 := by omega
      have hm0 : m = 0 := Multiset.card_eq_zero.mp hm
      refine ⟨LowOrderClass.time, Subtype.ext ?_⟩
      rw [← TimeVelocityMultiIndex.ofTimeVelocity_timeOrder_velocity beta.1, hqeq]
      change (timeOne d).1 = _
      rw [coe_timeOne]
      symm
      apply congrArg (TimeVelocityMultiIndex.ofTimeVelocity 1)
      funext a
      have ha := congrArg (fun z : Multiset (Fin d) => z.count a) hm0
      simpa [m, count_velocityMultiset, alpha] using ha

/-- The canonical equivalence between bounded weight-two indices and their
four low-order shapes. -/
noncomputable def equivLowOrderClass (d : ℕ) :
    ParabolicDerivativeIndex d 2 ≃ LowOrderClass d :=
  (Equiv.ofBijective (@LowOrderClass.toIndex d)
    (LowOrderClass.toIndex_bijective d)).symm

@[simp] theorem equivLowOrderClass_symm_apply
    {d : ℕ} (s : LowOrderClass d) :
    (equivLowOrderClass d).symm s = s.toIndex :=
  rfl

@[simp] theorem LowOrderClass.toIndex_equivLowOrderClass_apply
    {d : ℕ} (beta : ParabolicDerivativeIndex d 2) :
    (equivLowOrderClass d beta).toIndex = beta :=
  (equivLowOrderClass d).symm_apply_apply beta

end HypoellipticAleksandrov.Parabolic.ParabolicDerivativeIndex

module

public import HypoellipticAleksandrov.Parabolic.TimeVelocityMultiIndex
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Tactic

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

/-- Time--velocity multi-indices of parabolic weight at most `L`. -/
abbrev ParabolicDerivativeIndex (d L : ℕ) :=
  {beta : TimeVelocityMultiIndex d // beta.parabolicWeight ≤ L}

namespace ParabolicDerivativeIndex

private theorem sum_update_add {d : ℕ} (f : Fin d → ℕ) (i : Fin d) (n : ℕ) :
    (∑ j, Function.update f i n j) + f i = (∑ j, f j) + n := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i),
    Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i)]
  omega

/-- The order-zero parabolic derivative index. -/
def zero (d L : ℕ) : ParabolicDerivativeIndex d L :=
  ⟨0, by simp [TimeVelocityMultiIndex.parabolicWeight,
    VelocityMultiIndex.parabolicWeight, TimeVelocityMultiIndex.timeOrder,
    TimeVelocityMultiIndex.velocity, VelocityMultiIndex.order]⟩

/-- Enlarge the parabolic-weight bound without changing the multi-index. -/
def castLE {d L M : ℕ} (hLM : L ≤ M)
    (beta : ParabolicDerivativeIndex d L) :
    ParabolicDerivativeIndex d M :=
  ⟨beta.1, beta.2.trans hLM⟩

@[simp] theorem coe_zero (d L : ℕ) :
    (zero d L).1 = (0 : TimeVelocityMultiIndex d) := rfl

@[simp] theorem coe_castLE {d L M : ℕ} (hLM : L ≤ M)
    (beta : ParabolicDerivativeIndex d L) :
    (castLE hLM beta).1 = beta.1 := rfl

/-- Add one time derivative while remaining at the fixed bound `L`. -/
def timeSucc {d L : ℕ} (beta : ParabolicDerivativeIndex d L)
    (h : beta.1.parabolicWeight + 2 ≤ L) :
    ParabolicDerivativeIndex d L :=
  ⟨TimeVelocityMultiIndex.ofTimeVelocity
      (beta.1.timeOrder + 1) beta.1.velocity,
    by
      change beta.1.velocity.parabolicWeight (beta.1.timeOrder + 1) ≤ L
      change beta.1.velocity.parabolicWeight beta.1.timeOrder + 2 ≤ L at h
      unfold VelocityMultiIndex.parabolicWeight at h ⊢
      omega⟩

/-- Add one velocity derivative while remaining at the fixed bound `L`. -/
def velocitySucc {d L : ℕ} (beta : ParabolicDerivativeIndex d L)
    (i : Fin d) (h : beta.1.parabolicWeight + 1 ≤ L) :
    ParabolicDerivativeIndex d L :=
  ⟨TimeVelocityMultiIndex.ofTimeVelocity beta.1.timeOrder
      (Function.update beta.1.velocity i (beta.1.velocity i + 1)),
    by
      have hsum :
          (∑ j, Function.update beta.1.velocity i
              (beta.1.velocity i + 1) j) =
            (∑ j, beta.1.velocity j) + 1 := by
        have hs := sum_update_add beta.1.velocity i (beta.1.velocity i + 1)
        omega
      change 2 * beta.1.timeOrder +
        (∑ j, Function.update beta.1.velocity i
          (beta.1.velocity i + 1) j) ≤ L
      change 2 * beta.1.timeOrder + (∑ j, beta.1.velocity j) + 1 ≤ L at h
      omega⟩

@[simp] theorem coe_timeSucc {d L : ℕ}
    (beta : ParabolicDerivativeIndex d L)
    (h : beta.1.parabolicWeight + 2 ≤ L) :
    (timeSucc beta h).1 = TimeVelocityMultiIndex.ofTimeVelocity
      (beta.1.timeOrder + 1) beta.1.velocity := rfl

@[simp] theorem coe_velocitySucc {d L : ℕ}
    (beta : ParabolicDerivativeIndex d L) (i : Fin d)
    (h : beta.1.parabolicWeight + 1 ≤ L) :
    (velocitySucc beta i h).1 =
      TimeVelocityMultiIndex.ofTimeVelocity beta.1.timeOrder
        (Function.update beta.1.velocity i (beta.1.velocity i + 1)) := rfl

@[simp] theorem timeOrder_timeSucc {d L : ℕ}
    (beta : ParabolicDerivativeIndex d L)
    (h : beta.1.parabolicWeight + 2 ≤ L) :
    (timeSucc beta h).1.timeOrder = beta.1.timeOrder + 1 := rfl

@[simp] theorem velocity_timeSucc {d L : ℕ}
    (beta : ParabolicDerivativeIndex d L)
    (h : beta.1.parabolicWeight + 2 ≤ L) :
    (timeSucc beta h).1.velocity = beta.1.velocity := rfl

@[simp] theorem parabolicWeight_timeSucc {d L : ℕ}
    (beta : ParabolicDerivativeIndex d L)
    (h : beta.1.parabolicWeight + 2 ≤ L) :
    (timeSucc beta h).1.parabolicWeight = beta.1.parabolicWeight + 2 := by
  simp [timeSucc, TimeVelocityMultiIndex.parabolicWeight,
    VelocityMultiIndex.parabolicWeight]
  omega

@[simp] theorem timeOrder_velocitySucc {d L : ℕ}
    (beta : ParabolicDerivativeIndex d L) (i : Fin d)
    (h : beta.1.parabolicWeight + 1 ≤ L) :
    (velocitySucc beta i h).1.timeOrder = beta.1.timeOrder := rfl

@[simp] theorem velocity_velocitySucc_apply_self {d L : ℕ}
    (beta : ParabolicDerivativeIndex d L) (i : Fin d)
    (h : beta.1.parabolicWeight + 1 ≤ L) :
    (velocitySucc beta i h).1.velocity i = beta.1.velocity i + 1 := by
  simp [velocitySucc]

@[simp] theorem velocity_velocitySucc_apply_of_ne {d L : ℕ}
    (beta : ParabolicDerivativeIndex d L) (i j : Fin d)
    (hji : j ≠ i) (h : beta.1.parabolicWeight + 1 ≤ L) :
    (velocitySucc beta i h).1.velocity j = beta.1.velocity j := by
  simp [velocitySucc, hji]

@[simp] theorem parabolicWeight_velocitySucc {d L : ℕ}
    (beta : ParabolicDerivativeIndex d L) (i : Fin d)
    (h : beta.1.parabolicWeight + 1 ≤ L) :
    (velocitySucc beta i h).1.parabolicWeight =
      beta.1.parabolicWeight + 1 := by
  have hsum :
      (∑ j, Function.update beta.1.velocity i
          (beta.1.velocity i + 1) j) =
        (∑ j, beta.1.velocity j) + 1 := by
    have hs := sum_update_add beta.1.velocity i (beta.1.velocity i + 1)
    omega
  change 2 * beta.1.timeOrder +
    (∑ j, Function.update beta.1.velocity i (beta.1.velocity i + 1) j) =
      2 * beta.1.timeOrder + (∑ j, beta.1.velocity j) + 1
  omega

private theorem time_predecessor {d L : ℕ} (beta : ParabolicDerivativeIndex d L)
    (hq : 0 < beta.1.timeOrder) :
    ∃ (gamma : ParabolicDerivativeIndex d L)
        (h : gamma.1.parabolicWeight + 2 ≤ L),
      beta = timeSucc gamma h := by
  let raw := TimeVelocityMultiIndex.ofTimeVelocity
    (beta.1.timeOrder - 1) beta.1.velocity
  have hw : raw.parabolicWeight + 2 = beta.1.parabolicWeight := by
    simp [raw, TimeVelocityMultiIndex.parabolicWeight,
      VelocityMultiIndex.parabolicWeight]
    omega
  have hraw : raw.parabolicWeight ≤ L := by omega
  let gamma : ParabolicDerivativeIndex d L := ⟨raw, hraw⟩
  have hstay : gamma.1.parabolicWeight + 2 ≤ L := by
    change raw.parabolicWeight + 2 ≤ L
    omega
  refine ⟨gamma, hstay, ?_⟩
  apply Subtype.ext
  rw [coe_timeSucc]
  change beta.1 = TimeVelocityMultiIndex.ofTimeVelocity
    (beta.1.timeOrder - 1 + 1) beta.1.velocity
  have hqeq : beta.1.timeOrder - 1 + 1 = beta.1.timeOrder := by omega
  calc
    beta.1 = TimeVelocityMultiIndex.ofTimeVelocity
        beta.1.timeOrder beta.1.velocity :=
      TimeVelocityMultiIndex.ofTimeVelocity_timeOrder_velocity beta.1 |>.symm
    _ = TimeVelocityMultiIndex.ofTimeVelocity
        (beta.1.timeOrder - 1 + 1) beta.1.velocity := by rw [hqeq]

private theorem velocity_predecessor {d L : ℕ}
    (beta : ParabolicDerivativeIndex d L) (i : Fin d)
    (hi : 0 < beta.1.velocity i) :
    ∃ (gamma : ParabolicDerivativeIndex d L)
        (h : gamma.1.parabolicWeight + 1 ≤ L),
      beta = velocitySucc gamma i h := by
  let alpha : VelocityMultiIndex d :=
    Function.update beta.1.velocity i (beta.1.velocity i - 1)
  let raw := TimeVelocityMultiIndex.ofTimeVelocity beta.1.timeOrder alpha
  have ha : VelocityMultiIndex.order alpha + 1 = beta.1.velocity.order := by
    have hsum :
        (∑ j, Function.update beta.1.velocity i
            (beta.1.velocity i - 1) j) + beta.1.velocity i =
          (∑ j, beta.1.velocity j) + (beta.1.velocity i - 1) := by
      exact sum_update_add beta.1.velocity i (beta.1.velocity i - 1)
    change (∑ j, Function.update beta.1.velocity i
      (beta.1.velocity i - 1) j) + 1 = ∑ j, beta.1.velocity j
    omega
  have hw : raw.parabolicWeight + 1 = beta.1.parabolicWeight := by
    change 2 * beta.1.timeOrder + VelocityMultiIndex.order alpha + 1 =
      2 * beta.1.timeOrder + beta.1.velocity.order
    omega
  have hraw : raw.parabolicWeight ≤ L := by omega
  let gamma : ParabolicDerivativeIndex d L := ⟨raw, hraw⟩
  have hstay : gamma.1.parabolicWeight + 1 ≤ L := by
    change raw.parabolicWeight + 1 ≤ L
    omega
  have halpha :
      Function.update alpha i (alpha i + 1) = beta.1.velocity := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [alpha]
      omega
    · simp [alpha, hji]
  refine ⟨gamma, hstay, ?_⟩
  apply Subtype.ext
  rw [coe_velocitySucc]
  change beta.1 = TimeVelocityMultiIndex.ofTimeVelocity beta.1.timeOrder
    (Function.update alpha i (alpha i + 1))
  calc
    beta.1 = TimeVelocityMultiIndex.ofTimeVelocity
        beta.1.timeOrder beta.1.velocity :=
      TimeVelocityMultiIndex.ofTimeVelocity_timeOrder_velocity beta.1 |>.symm
    _ = TimeVelocityMultiIndex.ofTimeVelocity beta.1.timeOrder
        (Function.update alpha i (alpha i + 1)) := by rw [halpha]

/-- Every bounded parabolic index is zero or a one-coordinate successor. -/
theorem eq_zero_or_eq_timeSucc_or_eq_velocitySucc
    {d L : ℕ} (beta : ParabolicDerivativeIndex d L) :
    beta = zero d L ∨
      (∃ (gamma : ParabolicDerivativeIndex d L)
          (h : gamma.1.parabolicWeight + 2 ≤ L),
        beta = timeSucc gamma h) ∨
      ∃ (gamma : ParabolicDerivativeIndex d L) (i : Fin d)
          (h : gamma.1.parabolicWeight + 1 ≤ L),
        beta = velocitySucc gamma i h := by
  classical
  by_cases hq : 0 < beta.1.timeOrder
  · exact Or.inr (Or.inl (time_predecessor beta hq))
  by_cases hv : ∃ i, 0 < beta.1.velocity i
  · obtain ⟨i, hi⟩ := hv
    exact Or.inr (Or.inr (by
      obtain ⟨gamma, h, heq⟩ := velocity_predecessor beta i hi
      exact ⟨gamma, i, h, heq⟩))
  · left
    apply Subtype.ext
    funext j
    rcases j with j | j
    · have htime := Nat.eq_zero_of_not_pos hq
      have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
      simpa only [zero, TimeVelocityMultiIndex.timeOrder, timeCoord, hj, Pi.zero_apply]
        using htime
    · simp [zero]
      exact Nat.eq_zero_of_not_pos (fun hj => hv ⟨j, hj⟩)

/-- Induction by zero and the two fixed-bound successor operations. -/
theorem inductionOn {d L : ℕ}
    {P : ParabolicDerivativeIndex d L → Prop}
    (beta : ParabolicDerivativeIndex d L)
    (hzero : P (zero d L))
    (htime : ∀ (gamma : ParabolicDerivativeIndex d L)
        (h : gamma.1.parabolicWeight + 2 ≤ L),
      P gamma → P (timeSucc gamma h))
    (hvelocity : ∀ (gamma : ParabolicDerivativeIndex d L) (i : Fin d)
        (h : gamma.1.parabolicWeight + 1 ≤ L),
      P gamma → P (velocitySucc gamma i h)) : P beta := by
  induction hw : beta.1.parabolicWeight using Nat.strong_induction_on generalizing beta with
  | h n ih =>
      rcases eq_zero_or_eq_timeSucc_or_eq_velocitySucc beta with hz | ht | hv
      · simpa [hz] using hzero
      · obtain ⟨gamma, hstay, rfl⟩ := ht
        apply htime gamma hstay
        apply ih gamma.1.parabolicWeight
        · rw [parabolicWeight_timeSucc] at hw
          omega
        · rfl
      · obtain ⟨gamma, i, hstay, rfl⟩ := hv
        apply hvelocity gamma i hstay
        apply ih gamma.1.parabolicWeight
        · rw [parabolicWeight_velocitySucc] at hw
          omega
        · rfl

/-- Every coordinate multiplicity is bounded by the parabolic bound. -/
theorem coe_apply_le {d L : ℕ}
    (beta : ParabolicDerivativeIndex d L)
    (j : TimeVelocityCoord d) : beta.1 j ≤ L := by
  rcases j with j | j
  · have hq : 2 * beta.1.timeOrder ≤ beta.1.parabolicWeight := by
      simp [TimeVelocityMultiIndex.parabolicWeight,
        VelocityMultiIndex.parabolicWeight]
    have hle : beta.1.timeOrder ≤ 2 * beta.1.timeOrder := by omega
    exact hle.trans (hq.trans beta.2)
  · have hj : beta.1.velocity j ≤ beta.1.velocity.order := by
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have ha : beta.1.velocity.order ≤ beta.1.parabolicWeight := by
      simp [TimeVelocityMultiIndex.parabolicWeight,
        VelocityMultiIndex.parabolicWeight]
    exact hj.trans (ha.trans beta.2)

noncomputable instance instFintypeParabolicDerivativeIndex
    (d L : ℕ) : Fintype (ParabolicDerivativeIndex d L) := by
  classical
  let e : ParabolicDerivativeIndex d L →
      (TimeVelocityCoord d → Fin (L + 1)) := fun beta j =>
    ⟨beta.1 j, Nat.lt_succ_iff.mpr (coe_apply_le beta j)⟩
  exact Fintype.ofInjective e (by
    intro a b hab
    apply Subtype.ext
    funext j
    exact congrArg Fin.val (congrFun hab j))

end ParabolicDerivativeIndex
end HypoellipticAleksandrov.Parabolic

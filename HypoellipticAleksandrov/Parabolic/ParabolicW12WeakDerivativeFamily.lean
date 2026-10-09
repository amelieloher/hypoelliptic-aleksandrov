module

public import HypoellipticAleksandrov.Parabolic.ParabolicLowOrderIndex
public import HypoellipticAleksandrov.Parabolic.ParabolicWeakDerivativeFamily
public import HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique

/-!
# Weight-two weak-derivative family from a selected W12 jet

This module packages the selected representatives of an open-domain
parabolic W12 jet into one coherent family through parabolic weight two.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic.ParabolicW12Function

open MeasureTheory

private theorem equiv_zeroTwo (d : ℕ) :
    ParabolicDerivativeIndex.equivLowOrderClass d
      (ParabolicDerivativeIndex.zeroTwo d) = .zero := by
  apply (ParabolicDerivativeIndex.equivLowOrderClass d).symm.injective
  rw [Equiv.symm_apply_apply]
  rfl

private theorem equiv_timeOne (d : ℕ) :
    ParabolicDerivativeIndex.equivLowOrderClass d
      (ParabolicDerivativeIndex.timeOne d) = .time := by
  apply (ParabolicDerivativeIndex.equivLowOrderClass d).symm.injective
  rw [Equiv.symm_apply_apply]
  rfl

private theorem equiv_velocityOne {d : ℕ} (i : Fin d) :
    ParabolicDerivativeIndex.equivLowOrderClass d
      (ParabolicDerivativeIndex.velocityOne i) = .velocity i := by
  apply (ParabolicDerivativeIndex.equivLowOrderClass d).symm.injective
  rw [Equiv.symm_apply_apply]
  rfl

private theorem equiv_velocityTwo {d : ℕ} (i j : Fin d) (hij : i ≤ j) :
    ParabolicDerivativeIndex.equivLowOrderClass d
      (ParabolicDerivativeIndex.velocityTwo i j) = .velocity₂ i j hij := by
  apply (ParabolicDerivativeIndex.equivLowOrderClass d).symm.injective
  rw [Equiv.symm_apply_apply]
  rfl

private theorem parabolicWeight_zeroTwo (d : ℕ) :
    (ParabolicDerivativeIndex.zeroTwo d).1.parabolicWeight = 0 := by
  simp [ParabolicDerivativeIndex.zeroTwo,
    TimeVelocityMultiIndex.parabolicWeight,
    VelocityMultiIndex.parabolicWeight, VelocityMultiIndex.order,
    TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity]

private theorem parabolicWeight_timeOne (d : ℕ) :
    (ParabolicDerivativeIndex.timeOne d).1.parabolicWeight = 2 := by
  unfold ParabolicDerivativeIndex.timeOne
  rw [ParabolicDerivativeIndex.parabolicWeight_timeSucc,
    parabolicWeight_zeroTwo]

private theorem parabolicWeight_velocityOne {d : ℕ} (i : Fin d) :
    (ParabolicDerivativeIndex.velocityOne i).1.parabolicWeight = 1 := by
  unfold ParabolicDerivativeIndex.velocityOne
  rw [ParabolicDerivativeIndex.parabolicWeight_velocitySucc,
    parabolicWeight_zeroTwo]

private theorem parabolicWeight_velocityTwo {d : ℕ} (i j : Fin d) :
    (ParabolicDerivativeIndex.velocityTwo i j).1.parabolicWeight = 2 := by
  unfold ParabolicDerivativeIndex.velocityTwo
  rw [ParabolicDerivativeIndex.parabolicWeight_velocitySucc,
    parabolicWeight_velocityOne]

private theorem velocityTwo_comm {d : ℕ} (i j : Fin d) :
    ParabolicDerivativeIndex.velocityTwo i j =
      ParabolicDerivativeIndex.velocityTwo j i := by
  apply Subtype.ext
  funext c
  cases c with
  | inl q => rfl
  | inr k =>
      by_cases hki : k = i
      · subst k
        by_cases hij : i = j
        · subst j
          rfl
        · simp [ParabolicDerivativeIndex.velocityTwo,
            ParabolicDerivativeIndex.velocityOne,
            ParabolicDerivativeIndex.velocitySucc,
            TimeVelocityMultiIndex.ofTimeVelocity,
            TimeVelocityMultiIndex.timeOrder,
            TimeVelocityMultiIndex.velocity, velocityCoord, hij]
      · by_cases hkj : k = j
        · subst k
          simp [ParabolicDerivativeIndex.velocityTwo,
            ParabolicDerivativeIndex.velocityOne,
            ParabolicDerivativeIndex.velocitySucc,
            TimeVelocityMultiIndex.ofTimeVelocity,
            TimeVelocityMultiIndex.timeOrder,
            TimeVelocityMultiIndex.velocity, velocityCoord, hki]
        · simp [ParabolicDerivativeIndex.velocityTwo,
            ParabolicDerivativeIndex.velocityOne,
            ParabolicDerivativeIndex.velocitySucc,
            TimeVelocityMultiIndex.ofTimeVelocity,
            TimeVelocityMultiIndex.timeOrder,
            TimeVelocityMultiIndex.velocity, velocityCoord, hki, hkj]

private theorem equiv_timeSucc_zero {d : ℕ}
    (h : (ParabolicDerivativeIndex.zeroTwo d).1.parabolicWeight + 2 ≤ 2) :
    ParabolicDerivativeIndex.equivLowOrderClass d
      (ParabolicDerivativeIndex.timeSucc
        (ParabolicDerivativeIndex.zeroTwo d) h) = .time := by
  apply (ParabolicDerivativeIndex.equivLowOrderClass d).symm.injective
  rw [Equiv.symm_apply_apply]
  apply Subtype.ext
  rfl

private theorem equiv_velocitySucc_zero {d : ℕ} (i : Fin d)
    (h : (ParabolicDerivativeIndex.zeroTwo d).1.parabolicWeight + 1 ≤ 2) :
    ParabolicDerivativeIndex.equivLowOrderClass d
      (ParabolicDerivativeIndex.velocitySucc
        (ParabolicDerivativeIndex.zeroTwo d) i h) = .velocity i := by
  apply (ParabolicDerivativeIndex.equivLowOrderClass d).symm.injective
  rw [Equiv.symm_apply_apply]
  apply Subtype.ext
  rfl

private theorem equiv_velocitySucc_velocity_of_le {d : ℕ} (j i : Fin d)
    (hji : j ≤ i)
    (h : (ParabolicDerivativeIndex.velocityOne j).1.parabolicWeight + 1 ≤ 2) :
    ParabolicDerivativeIndex.equivLowOrderClass d
      (ParabolicDerivativeIndex.velocitySucc
        (ParabolicDerivativeIndex.velocityOne j) i h) = .velocity₂ j i hji := by
  apply (ParabolicDerivativeIndex.equivLowOrderClass d).symm.injective
  rw [Equiv.symm_apply_apply]
  apply Subtype.ext
  rfl

private theorem equiv_velocitySucc_velocity_of_ge {d : ℕ} (j i : Fin d)
    (hij : i ≤ j)
    (h : (ParabolicDerivativeIndex.velocityOne j).1.parabolicWeight + 1 ≤ 2) :
    ParabolicDerivativeIndex.equivLowOrderClass d
      (ParabolicDerivativeIndex.velocitySucc
        (ParabolicDerivativeIndex.velocityOne j) i h) = .velocity₂ i j hij := by
  apply (ParabolicDerivativeIndex.equivLowOrderClass d).symm.injective
  rw [Equiv.symm_apply_apply]
  exact velocityTwo_comm j i

/-- Package a selected open-domain parabolic W12 jet as one coherent family
of all weak derivatives through parabolic weight two. -/
noncomputable def toWeakDerivativeFamily
    {d : ℕ} {U : Set (TimeVelocity d)}
    (hU : IsOpen U) (w : ParabolicW12Function d U 2) :
    ParabolicWeakDerivativeFamily d 2 U w.toFun where
  representative beta :=
    match ParabolicDerivativeIndex.equivLowOrderClass d beta with
    | .zero => w.toFun
    | .time => w.timeDeriv
    | .velocity i => fun z => w.velocityGrad z i
    | .velocity₂ i j _ => fun z => w.velocityHessian z i j
  memLp beta := by
    generalize hs : ParabolicDerivativeIndex.equivLowOrderClass d beta = s
    have hb : s.toIndex = beta := by
      rw [← hs]
      exact ParabolicDerivativeIndex.LowOrderClass.toIndex_equivLowOrderClass_apply beta
    subst beta
    cases s with
    | zero => exact w.memLp
    | time => exact w.timeDeriv_memLp
    | velocity i => exact w.velocityGrad_memLp i
    | velocity₂ i j hij => exact w.velocityHessian_memLp i j
  zero_ae := by
    change (match ParabolicDerivativeIndex.equivLowOrderClass d
      (ParabolicDerivativeIndex.zeroTwo d) with
      | .zero => w.toFun
      | .time => w.timeDeriv
      | .velocity i => fun z => w.velocityGrad z i
      | .velocity₂ i j _ => fun z => w.velocityHessian z i j)
        =ᵐ[timeVelocityVolumeOn U] w.toFun
    rw [equiv_zeroTwo]
  hasWeakTimeSucc beta h := by
    generalize hs : ParabolicDerivativeIndex.equivLowOrderClass d beta = s
    have hb : s.toIndex = beta := by
      rw [← hs]
      exact ParabolicDerivativeIndex.LowOrderClass.toIndex_equivLowOrderClass_apply beta
    subst beta
    cases s with
    | zero =>
        simp only [ParabolicDerivativeIndex.LowOrderClass.toIndex] at h ⊢
        rw [equiv_timeSucc_zero]
        exact w.hasWeakTimeDeriv
    | time =>
        simp only [ParabolicDerivativeIndex.LowOrderClass.toIndex] at h ⊢
        rw [parabolicWeight_timeOne] at h
        omega
    | velocity i =>
        simp only [ParabolicDerivativeIndex.LowOrderClass.toIndex] at h ⊢
        rw [parabolicWeight_velocityOne] at h
        omega
    | velocity₂ i j hij =>
        simp only [ParabolicDerivativeIndex.LowOrderClass.toIndex] at h ⊢
        rw [parabolicWeight_velocityTwo] at h
        omega
  hasWeakVelocitySucc beta i h := by
    generalize hs : ParabolicDerivativeIndex.equivLowOrderClass d beta = s
    have hb : s.toIndex = beta := by
      rw [← hs]
      exact ParabolicDerivativeIndex.LowOrderClass.toIndex_equivLowOrderClass_apply beta
    subst beta
    cases s with
    | zero =>
        simp only [ParabolicDerivativeIndex.LowOrderClass.toIndex] at h ⊢
        rw [equiv_velocitySucc_zero]
        exact w.hasWeakVelocityPartialDeriv i
    | time =>
        simp only [ParabolicDerivativeIndex.LowOrderClass.toIndex] at h ⊢
        rw [parabolicWeight_timeOne] at h
        omega
    | velocity j =>
        simp only [ParabolicDerivativeIndex.LowOrderClass.toIndex] at h ⊢
        rcases le_total j i with hji | hij
        · rw [equiv_velocitySucc_velocity_of_le j i hji]
          exact w.hasWeakVelocitySecondPartialDeriv j i
        · rw [equiv_velocitySucc_velocity_of_ge j i hij]
          apply (w.hasWeakVelocitySecondPartialDeriv j i).congr_ae
            (Filter.Eventually.of_forall (fun _ => rfl))
          exact w.velocityHessian_ae_eq_swap hU j i
    | velocity₂ j k hjk =>
        simp only [ParabolicDerivativeIndex.LowOrderClass.toIndex] at h ⊢
        rw [parabolicWeight_velocityTwo] at h
        omega

/-- The zero-index representative is the selected root function. -/
@[simp] theorem toWeakDerivativeFamily_representative_zeroTwo
    {d : ℕ} {U : Set (TimeVelocity d)}
    (hU : IsOpen U) (w : ParabolicW12Function d U 2) :
    (toWeakDerivativeFamily hU w).representative
      (ParabolicDerivativeIndex.zeroTwo d) = w.toFun := by
  simp [toWeakDerivativeFamily, equiv_zeroTwo]

/-- The one-time-derivative representative is the selected time derivative. -/
@[simp] theorem toWeakDerivativeFamily_representative_timeOne
    {d : ℕ} {U : Set (TimeVelocity d)}
    (hU : IsOpen U) (w : ParabolicW12Function d U 2) :
    (toWeakDerivativeFamily hU w).representative
      (ParabolicDerivativeIndex.timeOne d) = w.timeDeriv := by
  simp [toWeakDerivativeFamily, equiv_timeOne]

/-- A first velocity representative is the selected velocity gradient. -/
@[simp] theorem toWeakDerivativeFamily_representative_velocityOne
    {d : ℕ} {U : Set (TimeVelocity d)}
    (hU : IsOpen U) (w : ParabolicW12Function d U 2)
    (i : Fin d) :
    (toWeakDerivativeFamily hU w).representative
      (ParabolicDerivativeIndex.velocityOne i) =
        fun z => w.velocityGrad z i := by
  simp [toWeakDerivativeFamily, equiv_velocityOne]

/-- An ordered second velocity representative is the selected Hessian entry. -/
@[simp] theorem toWeakDerivativeFamily_representative_velocityTwo
    {d : ℕ} {U : Set (TimeVelocity d)}
    (hU : IsOpen U) (w : ParabolicW12Function d U 2)
    (i j : Fin d) (hij : i ≤ j) :
    (toWeakDerivativeFamily hU w).representative
      (ParabolicDerivativeIndex.velocityTwo i j) =
        fun z => w.velocityHessian z i j := by
  simp [toWeakDerivativeFamily, equiv_velocityTwo i j hij]

end HypoellipticAleksandrov.Parabolic.ParabolicW12Function

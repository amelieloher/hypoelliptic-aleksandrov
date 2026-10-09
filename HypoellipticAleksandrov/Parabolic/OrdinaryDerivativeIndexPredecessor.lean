module

public import HypoellipticAleksandrov.Parabolic.OrdinaryWeakDerivativeFamilyView

/-!
# Predecessors of bounded ordinary derivative indices

This file decomposes every bounded ordinary time--velocity multi-index into the
zero index or a bounded time or velocity successor.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped ENNReal Topology

namespace TimeVelocityDerivativeIndex

/-- Every bounded ordinary index is zero or a bounded time/velocity successor. -/
theorem eq_zero_or_eq_timeSucc_or_eq_velocitySucc
    {d m : ℕ} (beta : TimeVelocityDerivativeIndex d m) :
    beta = zero d m ∨
      (∃ (gamma : TimeVelocityDerivativeIndex d m)
        (h : gamma.1.order + 1 ≤ m),
          beta = timeSucc gamma h) ∨
      ∃ (i : Fin d) (gamma : TimeVelocityDerivativeIndex d m)
        (h : gamma.1.order + 1 ≤ m),
          beta = velocitySucc gamma i h := by
  classical
  by_cases ht : beta.1.timeOrder = 0
  · by_cases hv : beta.1.velocity = 0
    · left
      apply Subtype.ext
      rw [← TimeVelocityMultiIndex.ofTimeVelocity_timeOrder_velocity beta.1,
        ht, hv]
      funext c
      cases c <;> rfl
    · right
      right
      have hi : ∃ i : Fin d, beta.1.velocity i ≠ 0 := by
        by_contra h
        push_neg at h
        exact hv (funext h)
      obtain ⟨i, hi⟩ := hi
      let gammaIndex := TimeVelocityMultiIndex.ofTimeVelocity beta.1.timeOrder
        (Function.update beta.1.velocity i (beta.1.velocity i - 1))
      have horder : gammaIndex.order + 1 ≤ m := by
        have hpos : 0 < beta.1.velocity i := Nat.pos_of_ne_zero hi
        have hsum :
            (∑ j, Function.update beta.1.velocity i
              (beta.1.velocity i - 1) j) + 1 =
              ∑ j, beta.1.velocity j := by
          rw [Finset.sum_update_of_mem (Finset.mem_univ i),
            Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i)]
          omega
        change beta.1.timeOrder +
            (∑ j, Function.update beta.1.velocity i
              (beta.1.velocity i - 1) j) + 1 ≤ m
        rw [ht, zero_add, hsum]
        simpa [TimeVelocityMultiIndex.order, ht, VelocityMultiIndex.order] using beta.2
      let gamma : TimeVelocityDerivativeIndex d m :=
        ⟨gammaIndex, Nat.le_trans (Nat.le_add_right _ _) horder⟩
      refine ⟨i, gamma, horder, ?_⟩
      apply Subtype.ext
      rw [coe_velocitySucc]
      change beta.1 = TimeVelocityMultiIndex.ofTimeVelocity beta.1.timeOrder
        (Function.update
          (Function.update beta.1.velocity i (beta.1.velocity i - 1)) i
          ((Function.update beta.1.velocity i
            (beta.1.velocity i - 1)) i + 1))
      rw [Function.update_self,
        Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hi)]
      rw [← TimeVelocityMultiIndex.ofTimeVelocity_timeOrder_velocity beta.1]
      congr 1
      funext j
      by_cases hji : j = i
      · subst j
        simp
      · simp [hji]
  · right
    left
    let gammaIndex := TimeVelocityMultiIndex.ofTimeVelocity
      (beta.1.timeOrder - 1) beta.1.velocity
    have horder : gammaIndex.order + 1 ≤ m := by
      have hpos : 0 < beta.1.timeOrder := Nat.pos_of_ne_zero ht
      change (beta.1.timeOrder - 1) + beta.1.velocity.order + 1 ≤ m
      have hbeta := beta.2
      change beta.1.timeOrder + beta.1.velocity.order ≤ m at hbeta
      omega
    let gamma : TimeVelocityDerivativeIndex d m :=
      ⟨gammaIndex, Nat.le_trans (Nat.le_add_right _ _) horder⟩
    refine ⟨gamma, horder, ?_⟩
    apply Subtype.ext
    rw [coe_timeSucc]
    change beta.1 = TimeVelocityMultiIndex.ofTimeVelocity
      (beta.1.timeOrder - 1 + 1) beta.1.velocity
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr ht)]
    exact (TimeVelocityMultiIndex.ofTimeVelocity_timeOrder_velocity beta.1).symm

end TimeVelocityDerivativeIndex

end HypoellipticAleksandrov.Parabolic

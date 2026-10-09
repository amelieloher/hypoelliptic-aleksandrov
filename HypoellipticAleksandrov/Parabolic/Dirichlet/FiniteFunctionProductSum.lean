module

public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Finite sums over dependent function spaces

This file separates one coordinate in a weighted product summed over a finite dependent
function space.
-/

@[expose] public section

open scoped BigOperators

noncomputable section

/-- A weighted product over a finite dependent function space factors coordinatewise. -/
theorem Fintype.sum_apply_mul_prod
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    {R : Type*} [CommSemiring R]
    (i : ι) (A : κ i → R) (w : ∀ j, κ j → R) :
    (∑ k : ∀ j, κ j, A (k i) * ∏ j : ι, w j (k j)) =
      (∑ a : κ i, A a * w i a) *
        ∏ j ∈ (Finset.univ.erase i), ∑ a : κ j, w j a := by
  let v : ∀ j, κ j → R := fun j a =>
    if h : j = i then A (h ▸ a) * w j a else w j a
  have hvprod (k : ∀ j, κ j) :
      (∏ j, v j (k j)) = A (k i) * ∏ j, w j (k j) := by
    have hverase :
        (∏ j ∈ Finset.univ.erase i, v j (k j)) =
          ∏ j ∈ Finset.univ.erase i, w j (k j) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp only [v, dif_neg (Finset.ne_of_mem_erase hj)]
    rw [← Finset.mul_prod_erase Finset.univ (fun j => w j (k j)) (Finset.mem_univ i)]
    rw [← Finset.prod_erase_mul Finset.univ (fun j => v j (k j)) (Finset.mem_univ i)]
    rw [hverase]
    simp only [v, dif_pos]
    ac_rfl
  have hvsum :
      (∏ j, ∑ a, v j a) =
        (∑ a : κ i, A a * w i a) *
          ∏ j ∈ (Finset.univ.erase i), ∑ a : κ j, w j a := by
    rw [← Finset.mul_prod_erase Finset.univ (fun j => ∑ a, v j a) (Finset.mem_univ i)]
    simp only [v, dif_pos]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    simp_rw [dif_neg (Finset.ne_of_mem_erase hj)]
  rw [← hvsum, Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact (hvprod k).symm

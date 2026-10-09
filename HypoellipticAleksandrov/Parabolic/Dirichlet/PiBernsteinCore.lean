module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.FiniteFunctionProductSum
public import Mathlib.Analysis.SpecialFunctions.Bernstein

/-!
# Product Bernstein approximation core

This module defines product Bernstein approximations on finite unit cubes and proves their
positivity, total-mass, product-metric, and summed-variance identities.
-/

@[expose] public section

open scoped BigOperators Topology unitInterval

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

section PiBernstein

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [Module ℝ E] [ContinuousSMul ℝ E]

/-- The product Bernstein grid on the unit cube. -/
def piBernsteinGrid {d n : ℕ} (k : Fin d → Fin (n + 1)) : Fin d → I :=
  fun i => bernstein.z (k i)

/-- The scalar product Bernstein basis on the unit cube. -/
def piBernsteinBasis {d : ℕ} (n : ℕ) (k : Fin d → Fin (n + 1)) :
    C(Fin d → I, ℝ) :=
  ∏ i : Fin d, (bernstein n (k i)).comp
    ⟨fun x => x i, continuous_apply i⟩

/-- The product Bernstein approximation of a continuous map on the unit cube. -/
def piBernsteinApproximation {d : ℕ} (n : ℕ) (f : C(Fin d → I, E)) :
    C(Fin d → I, E) :=
  ∑ k : Fin d → Fin (n + 1),
    piBernsteinBasis n k • ContinuousMap.const (Fin d → I) (f (piBernsteinGrid k))

/-- Failure of a product-metric proximity test bounds the summed squared displacement below. -/
theorem sq_le_sum_sq_sub_of_not_dist_lt_piBernsteinGrid
    {d n : ℕ} (k : Fin d → Fin (n + 1)) (x : Fin d → I) (δ : ℝ)
    (hδ : 0 ≤ δ) (hfar : ¬ dist (piBernsteinGrid k) x < δ) :
    δ ^ 2 ≤ ∑ i : Fin d,
      ((x i : ℝ) - (piBernsteinGrid k i : ℝ)) ^ 2 := by
  rcases hδ.eq_or_lt with rfl | hδpos
  · norm_num
    exact Finset.sum_nonneg fun i _ => sq_nonneg
      ((x i : ℝ) - (piBernsteinGrid k i : ℝ))
  · rw [dist_pi_lt_iff hδpos] at hfar
    push_neg at hfar
    obtain ⟨i, hi⟩ := hfar
    calc
      δ ^ 2 ≤ dist (piBernsteinGrid k i) (x i) ^ 2 := by nlinarith
      _ = ((x i : ℝ) - (piBernsteinGrid k i : ℝ)) ^ 2 := by
        rw [Subtype.dist_eq, Real.dist_eq]
        rw [abs_sub_comm, sq_abs]
      _ ≤ ∑ j : Fin d,
          ((x j : ℝ) - (piBernsteinGrid k j : ℝ)) ^ 2 := by
        exact Finset.single_le_sum (fun j _ => sq_nonneg
          ((x j : ℝ) - (piBernsteinGrid k j : ℝ))) (Finset.mem_univ i)

/-- Every product Bernstein weight is nonnegative. -/
theorem piBernsteinBasis_nonneg {d n : ℕ}
    (k : Fin d → Fin (n + 1)) (x : Fin d → I) :
    0 ≤ piBernsteinBasis n k x := by
  simp only [piBernsteinBasis, ContinuousMap.prod_apply]
  exact Finset.prod_nonneg fun _ _ => bernstein_nonneg

/-- Product Bernstein weights have total mass one, including in dimension zero. -/
theorem sum_piBernsteinBasis {d n : ℕ} (x : Fin d → I) :
    (∑ k : Fin d → Fin (n + 1), piBernsteinBasis n k x) = 1 := by
  classical
  simp only [piBernsteinBasis, ContinuousMap.prod_apply, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk]
  calc
    (∑ k : Fin d → Fin (n + 1), ∏ i : Fin d, bernstein n (k i) (x i)) =
        ∏ i : Fin d, ∑ j : Fin (n + 1), bernstein n j (x i) := by
      symm
      exact Fintype.prod_sum (fun i (j : Fin (n + 1)) => bernstein n j (x i))
    _ = 1 := by simp only [bernstein.probability, Finset.prod_const_one]

/-- The summed squared coordinate displacement has the product Bernstein variance. -/
theorem sum_sq_sub_piBernsteinGrid_mul_piBernsteinBasis
    {d n : ℕ} (hn : n ≠ 0) (x : Fin d → I) :
    (∑ k : Fin d → Fin (n + 1),
        (∑ i : Fin d, ((x i : ℝ) - (piBernsteinGrid k i : ℝ)) ^ 2) *
          piBernsteinBasis n k x) =
      ∑ i : Fin d, (x i : ℝ) * (1 - (x i : ℝ)) / n := by
  classical
  simp only [piBernsteinBasis, ContinuousMap.prod_apply, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  change (∑ k : Fin d → Fin (n + 1),
      ((x i : ℝ) - (bernstein.z (k i) : ℝ)) ^ 2 *
        ∏ j : Fin d, bernstein n (k j) (x j)) = _
  rw [Fintype.sum_apply_mul_prod i
    (fun a : Fin (n + 1) => ((x i : ℝ) - (bernstein.z a : ℝ)) ^ 2)
    (fun j (a : Fin (n + 1)) => bernstein n a (x j))]
  rw [bernstein.variance hn]
  simp only [bernstein.probability, Finset.prod_const_one, mul_one]

end PiBernstein

end HypoellipticAleksandrov.Parabolic.Dirichlet

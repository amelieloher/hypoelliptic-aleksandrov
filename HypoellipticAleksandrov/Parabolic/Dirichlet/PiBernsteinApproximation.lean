module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.PiBernsteinCore
public import Mathlib.Topology.ContinuousMap.LocallyConvex

/-!
# Uniform convergence of product Bernstein approximations

This module proves uniform convergence of product Bernstein approximations on
finite unit cubes for maps into a locally convex real topological vector space.
-/

@[expose] public section

open Filter Topology
open scoped BigOperators Topology unitInterval

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

section PiBernstein

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [Module ℝ E] [ContinuousSMul ℝ E]

/-- Product Bernstein approximations converge uniformly on every finite unit cube. -/
theorem piBernsteinApproximation_uniform {d : ℕ} [LocallyConvexSpace ℝ E]
    (f : C(Fin d → I, E)) :
    Tendsto (fun n : ℕ => piBernsteinApproximation n f) atTop (𝓝 f) := by
  classical
  letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  suffices ∀ U ∈ 𝓝 (0 : E), Convex ℝ U →
      ∀ᶠ n in atTop, ∀ x : Fin d → I,
        gauge U (piBernsteinApproximation n f x - f x) < 1 by
    rw [(LocallyConvexSpace.convex_basis_zero ℝ E).uniformity_of_nhds_zero_swapped
      |>.compactConvergenceUniformity_of_compact |> nhds_basis_uniformity |>.tendsto_right_iff]
    rintro U ⟨hU₀, hcU⟩
    filter_upwards [this U hU₀ hcU] with n hn x
    exact gauge_lt_one_subset_self hcU (mem_of_mem_nhds hU₀)
      (absorbent_nhds_zero hU₀) (hn x)
  intro U hU₀ hUc
  obtain ⟨C, hC⟩ : ∃ C, ∀ x y, gauge U (f x - f y) ≤ C := by
    have hcontinuous : Continuous fun (x, y) => gauge U (f x - f y) := by
      fun_prop (disch := assumption)
    simpa only [BddAbove, Set.Nonempty, mem_upperBounds, Set.forall_mem_range,
      Prod.forall] using isCompact_range hcontinuous |>.bddAbove
  have hC₀ : 0 ≤ C := le_trans (gauge_nonneg _) (hC 0 0)
  obtain ⟨δ, hδ₀, hδ⟩ : ∃ δ > 0, ∀ x y : Fin d → I,
      dist x y < δ → gauge U (f x - f y) < 1 / 2 := by
    have huniform := CompactSpace.uniformContinuous_of_continuous (map_continuous f)
    rw [Metric.uniformity_basis_dist.uniformContinuous_iff
      (basis_sets _).uniformity_of_nhds_zero_swapped] at huniform
    exact huniform {z | gauge U z < 1 / 2} <| tendsto_gauge_nhds_zero hU₀
      |>.eventually_lt_const <| by positivity
  have hdim : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hlimit := tendsto_const_div_atTop_nhds_zero_nat (C / δ ^ 2 * d)
  filter_upwards [hlimit.eventually_lt_const (half_pos one_pos), eventually_ne_atTop 0]
    with n hn hn₀ x
  set S : Finset (Fin d → Fin (n + 1)) :=
    {k : Fin d → Fin (n + 1) | dist (piBernsteinGrid k) x < δ}
  calc
    gauge U (piBernsteinApproximation n f x - f x) =
        gauge U (∑ k : Fin d → Fin (n + 1),
          piBernsteinBasis n k x • (f (piBernsteinGrid k) - f x)) := by
      simp [piBernsteinApproximation, smul_sub, ← Finset.sum_smul,
        sum_piBernsteinBasis]
    _ ≤ ∑ k : Fin d → Fin (n + 1),
        gauge U (piBernsteinBasis n k x • (f (piBernsteinGrid k) - f x)) :=
      gauge_sum_le hUc (absorbent_nhds_zero hU₀) _ _
    _ = ∑ k : Fin d → Fin (n + 1),
        piBernsteinBasis n k x * gauge U (f (piBernsteinGrid k) - f x) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [gauge_smul_of_nonneg (piBernsteinBasis_nonneg k x), smul_eq_mul]
    _ = (∑ k ∈ S,
          piBernsteinBasis n k x * gauge U (f (piBernsteinGrid k) - f x)) +
        ∑ k ∈ Sᶜ,
          piBernsteinBasis n k x * gauge U (f (piBernsteinGrid k) - f x) :=
      (S.sum_add_sum_compl _).symm
    _ < 1 / 2 + 1 / 2 := add_lt_add_of_le_of_lt (by
      calc
        ∑ k ∈ S, piBernsteinBasis n k x *
              gauge U (f (piBernsteinGrid k) - f x) ≤
            ∑ k ∈ S, piBernsteinBasis n k x * (1 / 2) := by
          gcongr with k hk
          · exact piBernsteinBasis_nonneg k x
          · refine (hδ _ _ ?_).le
            simpa only [Finset.mem_filter, Finset.mem_univ, true_and, S] using hk
        _ = 1 / 2 * ∑ k ∈ S, piBernsteinBasis n k x := by
          rw [mul_comm, Finset.sum_mul]
        _ ≤ 1 / 2 * ∑ k : Fin d → Fin (n + 1), piBernsteinBasis n k x := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Finset.sum_le_sum_of_subset_of_nonneg S.subset_univ
          intro k _ _
          exact piBernsteinBasis_nonneg k x
        _ = 1 / 2 := by rw [sum_piBernsteinBasis, mul_one]) (by
      calc
        ∑ k ∈ Sᶜ, piBernsteinBasis n k x *
              gauge U (f (piBernsteinGrid k) - f x) ≤
            ∑ k ∈ Sᶜ, C * piBernsteinBasis n k x := by
          simp only [mul_comm (piBernsteinBasis n _ x)]
          gcongr with k hk
          · exact piBernsteinBasis_nonneg k x
          · exact hC _ _
        _ = C * ∑ k ∈ Sᶜ, piBernsteinBasis n k x := by rw [Finset.mul_sum]
        _ ≤ C * ∑ k ∈ Sᶜ,
            (∑ i : Fin d,
              ((x i : ℝ) - (piBernsteinGrid k i : ℝ)) ^ 2) / δ ^ 2 *
              piBernsteinBasis n k x := by
          gcongr with k hk
          conv_lhs => rw [← one_mul (piBernsteinBasis n k x)]
          have hfar : ¬ dist (piBernsteinGrid k) x < δ := by
            simpa only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ,
              true_and, S] using hk
          have hsquare :=
            sq_le_sum_sq_sub_of_not_dist_lt_piBernsteinGrid k x δ hδ₀.le hfar
          have hratio : 1 ≤
              (∑ i : Fin d, ((x i : ℝ) - (piBernsteinGrid k i : ℝ)) ^ 2) /
                δ ^ 2 := by
            rw [one_le_div₀ (sq_pos_of_pos hδ₀)]
            exact hsquare
          exact mul_le_mul hratio le_rfl (piBernsteinBasis_nonneg k x)
            (zero_le_one.trans hratio)
        _ ≤ C * ∑ k : Fin d → Fin (n + 1),
            (∑ i : Fin d,
              ((x i : ℝ) - (piBernsteinGrid k i : ℝ)) ^ 2) / δ ^ 2 *
              piBernsteinBasis n k x := by
          apply mul_le_mul_of_nonneg_left _ hC₀
          apply Finset.sum_le_sum_of_subset_of_nonneg Sᶜ.subset_univ
          intro k _ _
          exact mul_nonneg (div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _)
            (sq_nonneg δ)) (piBernsteinBasis_nonneg k x)
        _ = C * (∑ k : Fin d → Fin (n + 1),
            (∑ i : Fin d,
              ((x i : ℝ) - (piBernsteinGrid k i : ℝ)) ^ 2) *
              piBernsteinBasis n k x) / δ ^ 2 := by
          simp only [← mul_div_right_comm, ← mul_div_assoc, ← Finset.sum_div]
        _ = C / δ ^ 2 *
            (∑ i : Fin d, (x i : ℝ) * (1 - (x i : ℝ)) / n) := by
          rw [sum_sq_sub_piBernsteinGrid_mul_piBernsteinBasis hn₀]
          ring
        _ ≤ C / δ ^ 2 * d / n := by
          have hCδ : 0 ≤ C / δ ^ 2 := div_nonneg hC₀ (sq_nonneg δ)
          have hsum : (∑ i : Fin d, (x i : ℝ) * (1 - (x i : ℝ))) ≤ d := by
            calc
              (∑ i : Fin d, (x i : ℝ) * (1 - (x i : ℝ))) ≤
                  ∑ _i : Fin d, (1 : ℝ) := by
                apply Finset.sum_le_sum
                intro i _
                calc
                  (x i : ℝ) * (1 - (x i : ℝ)) ≤ 1 * 1 := by
                    gcongr <;> unit_interval
                  _ = 1 := mul_one 1
              _ = d := by simp only [Finset.sum_const, Finset.card_univ,
                Fintype.card_fin, nsmul_eq_mul, mul_one]
          calc
            C / δ ^ 2 * (∑ i : Fin d,
                (x i : ℝ) * (1 - (x i : ℝ)) / n) =
                (C / δ ^ 2 * ∑ i : Fin d,
                  (x i : ℝ) * (1 - (x i : ℝ))) / n := by
              rw [← Finset.sum_div]
              ring
            _ ≤ (C / δ ^ 2 * d) / n :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hCδ)
                (Nat.cast_nonneg n)
            _ = C / δ ^ 2 * d / n := rfl
        _ < 1 / 2 := hn)
    _ = 1 := add_halves 1

end PiBernstein

end HypoellipticAleksandrov.Parabolic.Dirichlet

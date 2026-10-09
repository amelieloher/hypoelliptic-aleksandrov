module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AnnularNormalizationAnnuli
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-! # Uniform compact bounds from bounded degrees and one annular mass bound -/

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- Adjacent dyadic radii differ by exactly two. -/
theorem bellman_dyadic_succ (j : ℤ) : (2 : ℝ) ^ (j + 1) = 2 * 2 ^ j := by
  rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one, mul_comm]

/-- Open thick dyadic annuli supply the finite compact-cover argument. -/
def bellmanOpenDyadicAnnulus (j : ℤ) : Set BellmanPuncturedPlane :=
  {q | 2 ^ j < bellmanGauge q.val ∧ bellmanGauge q.val < 4 * 2 ^ j}

/-- Every open thick annulus is open in the punctured topology. -/
theorem bellmanOpenDyadicAnnulus_isOpen (j : ℤ) : IsOpen (bellmanOpenDyadicAnnulus j) :=
  (isOpen_lt continuous_const (bellmanGauge_continuous.comp continuous_subtype_val)).inter
    (isOpen_lt (bellmanGauge_continuous.comp continuous_subtype_val) continuous_const)

/-- Thick dyadic annuli cover the punctured plane by open sets. -/
theorem bellmanOpenDyadicAnnulus_iUnion :
    (⋃ j : ℤ, bellmanOpenDyadicAnnulus j) = univ := by
  apply eq_univ_of_forall
  intro q
  obtain ⟨j, hj⟩ := exists_mem_Ico_zpow (bellmanGauge_pos q.val q.property)
    (by norm_num : (1 : ℝ) < 2)
  have he : (2 : ℝ) ^ j = 2 * 2 ^ (j - 1) := by
    convert bellman_dyadic_succ (j - 1) using 1
    congr 1
    omega
  have hr : 0 < (2 : ℝ) ^ (j - 1) := zpow_pos (by norm_num) _
  refine mem_iUnion.mpr ⟨j - 1, ?_⟩
  change 2 ^ (j - 1) < bellmanGauge q.val ∧ bellmanGauge q.val < 4 * 2 ^ (j - 1)
  rw [bellman_dyadic_succ] at hj
  constructor <;> nlinarith only [he, hr, hj.1, hj.2]

/-- Each thick annulus is covered by two adjacent closed source annuli. -/
theorem bellmanOpenDyadicAnnulus_subset (j : ℤ) :
    bellmanOpenDyadicAnnulus j ⊆ bellmanDyadicAnnulus j ∪ bellmanDyadicAnnulus (j + 1) := by
  intro q hq
  rcases le_or_gt (bellmanGauge q.val) (2 * (2 : ℝ) ^ j) with h | h
  · exact Or.inl ((mem_bellmanDyadicAnnulus_iff j q).mpr ⟨hq.1.le, h⟩)
  · apply Or.inr
    apply (mem_bellmanDyadicAnnulus_iff (j + 1) q).mpr
    rw [bellman_dyadic_succ]
    exact ⟨h.le, by linarith only [hq.2]⟩

/-- Fixed positive dilation factors are uniformly bounded over a bounded degree interval. -/
theorem bellman_degree_factor_bounded (r : ℝ) (hr : 0 < r) (a b : ℝ) :
    ∃ C : ℝ≥0, ∀ beta ∈ Icc a b, ENNReal.ofReal (r ^ (4 - beta)) ≤ C := by
  have hc : Continuous (fun beta : ℝ => r ^ (4 - beta)) :=
    (Real.continuous_const_rpow hr.ne').comp (continuous_const.sub continuous_id)
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hc.continuousOn
  refine ⟨⟨max 0 M, le_max_left _ _⟩, ?_⟩
  intro beta hbeta
  have hb : r ^ (4 - beta) ≤ max 0 M :=
    (hM (mem_image_of_mem _ hbeta)).trans (le_max_right _ _)
  have h := ENNReal.ofReal_le_ofReal hb
  exact h.trans_eq (ENNReal.ofReal_eq_coe_nnreal (le_max_left 0 M))

/-- Bounded homogeneous degrees and a common annular mass bound control every compact. -/
theorem bellman_homogeneous_compact_bound (beta : ℕ → ℝ)
    (mu : ℕ → Measure BellmanPuncturedPlane)
    (hd : ∀ n, HasBellmanDensityDegree (beta n) (mu n))
    (hm : ∀ n, mu n bellmanUnitAnnulus ≤ 1)
    (hb : ∃ a b : ℝ, ∀ n, a ≤ beta n ∧ beta n ≤ b)
    (K : Set BellmanPuncturedPlane) (hK : IsCompact K) :
    ∃ C : ℝ≥0, ∀ n, mu n K ≤ C := by
  obtain ⟨a, b, hb⟩ := hb
  have hf (j : ℤ) := bellman_degree_factor_bounded (2 ^ j)
    (zpow_pos (by norm_num) j) a b
  choose C hC using hf
  have hclosed (n : ℕ) (j : ℤ) : mu n (bellmanDyadicAnnulus j) ≤ C j := by
    rw [bellmanDyadicAnnulus, hd n _ _ _ bellmanUnitAnnulus_isCompact.measurableSet]
    calc ENNReal.ofReal ((2 ^ j) ^ (4 - beta n)) * mu n bellmanUnitAnnulus
        ≤ ENNReal.ofReal ((2 ^ j) ^ (4 - beta n)) * 1 := mul_le_mul_right (hm n) _
      _ ≤ C j := by rw [mul_one]; exact hC j _ (hb n)
  have hopen (n : ℕ) (j : ℤ) :
      mu n (bellmanOpenDyadicAnnulus j) ≤ (C j : ℝ≥0∞) + C (j + 1) :=
    (measure_mono (bellmanOpenDyadicAnnulus_subset j)).trans
      ((measure_union_le _ _).trans (add_le_add (hclosed n j) (hclosed n (j + 1))))
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover bellmanOpenDyadicAnnulus
    bellmanOpenDyadicAnnulus_isOpen (by rw [bellmanOpenDyadicAnnulus_iUnion]; exact subset_univ K)
  refine ⟨∑ j ∈ s, (C j + C (j + 1)), ?_⟩
  intro n
  calc mu n K ≤ mu n (⋃ j ∈ s, bellmanOpenDyadicAnnulus j) := measure_mono hs
    _ ≤ ∑ j ∈ s, mu n (bellmanOpenDyadicAnnulus j) := measure_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ s, ((C j : ℝ≥0∞) + C (j + 1)) := Finset.sum_le_sum (fun j _ => hopen n j)
    _ = _ := by simp only [ENNReal.ofNNReal_finsetSum, ENNReal.coe_add]

end HypoellipticAleksandrov.KineticAleksandrov

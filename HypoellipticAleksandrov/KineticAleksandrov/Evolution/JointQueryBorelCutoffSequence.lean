module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.CompositionTraceCutoff
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic.Linarith

/-! # Increasing smooth compact cutoffs of an open finite-dimensional set -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open Set Function

/-- Accumulate cutoffs using the smooth union operation `a + (1-a)b`. -/
def accumulatedCutoffs {E : Type*} (χ : ℕ → E → ℝ) : ℕ → E → ℝ
  | 0 => χ 0
  | j + 1 => fun x => accumulatedCutoffs χ j x + (1 - accumulatedCutoffs χ j x) * χ (j + 1) x

/-- Accumulated cutoffs take values in `[0,1]` when all their inputs do. -/
theorem accumulatedCutoffs_bounds {E : Type*} (χ : ℕ → E → ℝ)
    (hχ : ∀ j x, 0 ≤ χ j x ∧ χ j x ≤ 1) :
    ∀ j x, 0 ≤ accumulatedCutoffs χ j x ∧ accumulatedCutoffs χ j x ≤ 1 := by
  intro j
  induction j with
  | zero => exact hχ 0
  | succ j ih =>
    intro x
    have ha := ih x
    have hb := hχ (j + 1) x
    have hprod := mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr hb.2)
    have hnon := mul_nonneg (sub_nonneg.mpr ha.2) hb.1
    dsimp only [accumulatedCutoffs]
    constructor <;> nlinarith only [ha.1, hprod, hnon]

/-- Accumulated cutoffs increase pointwise. -/
theorem monotone_accumulatedCutoffs {E : Type*} (χ : ℕ → E → ℝ)
    (hχ : ∀ j x, 0 ≤ χ j x ∧ χ j x ≤ 1) (x : E) :
    Monotone (fun j => accumulatedCutoffs χ j x) := by
  apply monotone_nat_of_le_succ
  intro j
  change accumulatedCutoffs χ j x ≤
    accumulatedCutoffs χ j x + (1 - accumulatedCutoffs χ j x) * χ (j + 1) x
  exact le_add_of_nonneg_right (mul_nonneg
    (sub_nonneg.mpr (accumulatedCutoffs_bounds χ hχ j x).2) (hχ (j + 1) x).1)

/-- The accumulated cutoff at an index dominates that index's input cutoff. -/
theorem le_accumulatedCutoffs {E : Type*} (χ : ℕ → E → ℝ)
    (hχ : ∀ j x, 0 ≤ χ j x ∧ χ j x ≤ 1) (j : ℕ) (x : E) :
    χ j x ≤ accumulatedCutoffs χ j x := by
  cases j with
  | zero => exact le_rfl
  | succ j =>
    have ha := (accumulatedCutoffs_bounds χ hχ j x).1
    have hp := mul_nonneg ha (sub_nonneg.mpr (hχ (j + 1) x).2)
    dsimp only [accumulatedCutoffs]
    nlinarith only [hp]

/-- Accumulation preserves smoothness, compact support and an interior support condition. -/
theorem accumulatedCutoffs_regular
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {U : Set E}
    (χ : ℕ → E → ℝ)
    (hχ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (χ j) ∧ HasCompactSupport (χ j) ∧ tsupport (χ j) ⊆ U) :
    ∀ j, ContDiff ℝ (⊤ : ℕ∞) (accumulatedCutoffs χ j) ∧
      HasCompactSupport (accumulatedCutoffs χ j) ∧ tsupport (accumulatedCutoffs χ j) ⊆ U := by
  intro j
  induction j with
  | zero => exact hχ 0
  | succ j ih =>
    refine ⟨ih.1.add ((contDiff_const.sub ih.1).mul (hχ (j + 1)).1),
      ih.2.1.add (hχ (j + 1)).2.1.mul_left, ?_⟩
    exact (tsupport_add _ _).trans (union_subset ih.2.2
      (tsupport_mul_subset_right.trans (hχ (j + 1)).2.2))

/-- Every open finite-dimensional real set has increasing smooth compact interior cutoffs,
eventually identically one at each of its points. -/
theorem exists_increasing_smooth_interior_cutoffs
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {U : Set E} (hU : IsOpen U) :
    ∃ χ : ℕ → E → ℝ,
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (χ j) ∧ HasCompactSupport (χ j) ∧ tsupport (χ j) ⊆ U) ∧
      (∀ j x, 0 ≤ χ j x ∧ χ j x ≤ 1) ∧ (∀ x, Monotone (fun j => χ j x)) ∧
      ∀ x ∈ U, ∃ N : ℕ, ∀ j, N ≤ j → χ j x = 1 := by
  have : LocallyCompactSpace U := hU.locallyCompactSpace
  have : SigmaCompactSpace U := inferInstance
  let K (j : ℕ) : Set E := Subtype.val '' compactCovering U j
  have hK (j : ℕ) : IsCompact (K j) :=
    (isCompact_compactCovering U j).image continuous_subtype_val
  have hKU (j : ℕ) : K j ⊆ U := fun x hx => by
    obtain ⟨y, _, rfl⟩ := hx
    exact y.2
  choose χ hs hc ht hb h1 using
    (fun j => exists_smooth_bump_of_isCompact_subset_isOpen (hK j) hU (hKU j))
  refine ⟨accumulatedCutoffs χ, accumulatedCutoffs_regular χ
    (fun j => ⟨hs j, hc j, ht j⟩), accumulatedCutoffs_bounds χ hb,
    monotone_accumulatedCutoffs χ hb, ?_⟩
  intro x hx
  obtain ⟨N, hN⟩ := exists_mem_compactCovering (⟨x, hx⟩ : U)
  have hχN : χ N x = 1 := h1 N x ⟨⟨x, hx⟩, hN, rfl⟩
  refine ⟨N, fun j hj => le_antisymm (accumulatedCutoffs_bounds χ hb j x).2 ?_⟩
  calc
    1 = χ N x := hχN.symm
    _ ≤ accumulatedCutoffs χ N x := le_accumulatedCutoffs χ hb N x
    _ ≤ accumulatedCutoffs χ j x := monotone_accumulatedCutoffs χ hb x hj

end HypoellipticAleksandrov.KineticAleksandrov

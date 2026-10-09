module

import Mathlib.Tactic.Linarith
public import Mathlib.MeasureTheory.Integral.CompactlySupported
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.UrysohnsLemma
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TerminalFunctionalExtension

/-!
# Measurability of a family of finite measures from its integrals against `C_c`

Outside-context measure theory for Let `X` be a second countable, locally compact,
pseudometrizable Borel space and `ν : α → Measure X` a measurable-space-indexed family of
subprobability measures.  If `a ↦ ∫ f dν a` is measurable for every `f` in a uniformly dense
family of `C_c(X, ℝ)`, then `ν` is measurable.  The proof passes successively to all of
`C_c`, to bounded continuous functions (cutoff and dominated convergence), to measures of closed
sets (`HasOuterApproxClosed`), and finally to all measurable sets by the π-λ theorem.
-/

@[expose] public section

noncomputable section


namespace HypoellipticAleksandrov.KineticAleksandrov

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped CompactlySupported ENNReal NNReal

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

/-- A sequence of compactly supported cutoffs with values in `[0, 1]` tending to `1`. -/
theorem exists_compactSupport_cutoff :
    ∃ φ : ℕ → C_c(X, ℝ), (∀ j x, 0 ≤ φ j x ∧ φ j x ≤ 1) ∧
      ∀ x, Tendsto (fun j => φ j x) atTop (𝓝 1) := by
  let K : CompactExhaustion X := CompactExhaustion.choice X
  have hex : ∀ j, ∃ f : C(X, ℝ), EqOn f 1 (K j) ∧ IsCompact (tsupport f) ∧
      tsupport f ⊆ interior (K (j + 1)) ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 := fun j =>
    exists_continuousMap_one_of_isCompact_subset_isOpen (K.isCompact j) isOpen_interior
      (K.subset_interior_succ j)
  choose f hf1 hfc hfs hf01 using hex
  refine ⟨fun j => ⟨f j, hfc j⟩, fun j x => hf01 j x, fun x => ?_⟩
  obtain ⟨J, hJ⟩ : ∃ J, x ∈ K J := by
    have : x ∈ ⋃ J, K J := by rw [K.iUnion_eq]; trivial
    simpa using this
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop J] with j hj
  exact (hf1 j (K.subset hj hJ)).symm

variable {α : Type*} [MeasurableSpace α]

/-- Passing from `C_c` to bounded continuous functions: measurability of the integrals. -/
theorem measurable_integral_of_continuous_bounded (ν : α → Measure X)
    [∀ a, IsFiniteMeasure (ν a)]
    (H : ∀ f : C_c(X, ℝ), Measurable fun a => ∫ x, f x ∂ν a)
    (h : X → ℝ) (hc : Continuous h) (M : ℝ) (hM : ∀ x, |h x| ≤ M) :
    Measurable fun a => ∫ x, h x ∂ν a := by
  obtain ⟨φ, hφ01, hφlim⟩ := exists_compactSupport_cutoff (X := X)
  let g : ℕ → C_c(X, ℝ) := fun j =>
    ⟨⟨fun x => h x * φ j x, hc.mul (φ j).continuous⟩, (φ j).hasCompactSupport.mul_left⟩
  refine measurable_of_tendsto_metrizable (f := fun j a => ∫ x, g j x ∂ν a) (fun j => H (g j))
    (tendsto_pi_nhds.2 fun a => ?_)
  refine tendsto_integral_of_dominated_convergence (fun _ => |M|)
    (fun j => (g j).continuous.aestronglyMeasurable) (integrable_const _) (fun j => ?_) ?_
  · refine Filter.Eventually.of_forall fun x => ?_
    show ‖h x * φ j x‖ ≤ |M|
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hφ01 j x).1]
    calc |h x| * φ j x ≤ |M| * 1 :=
          mul_le_mul ((hM x).trans (le_abs_self M)) (hφ01 j x).2 (hφ01 j x).1 (abs_nonneg M)
      _ = |M| := mul_one _
  · refine Filter.Eventually.of_forall fun x => ?_
    have := (hφlim x).const_mul (h x)
    rw [mul_one] at this
    exact this

/-- Measurability of the measures of closed sets. -/
theorem measurable_measure_closed [PseudoMetrizableSpace X] (ν : α → Measure X)
    [∀ a, IsFiniteMeasure (ν a)]
    (H : ∀ f : C_c(X, ℝ), Measurable fun a => ∫ x, f x ∂ν a)
    {C : Set X} (hC : IsClosed C) : Measurable fun a => ν a C := by
  have hlim : ∀ a, Tendsto (fun n => ∫⁻ x, (hC.apprSeq n x : ℝ≥0∞) ∂ν a) atTop (𝓝 (ν a C)) :=
    fun a => HasOuterApproxClosed.tendsto_lintegral_apprSeq hC (ν a)
  refine measurable_of_tendsto_metrizable (f := fun n a => ∫⁻ x, (hC.apprSeq n x : ℝ≥0∞) ∂ν a)
    (fun n => ?_) (tendsto_pi_nhds.2 hlim)
  have hcont : Continuous fun x => ((hC.apprSeq n x : ℝ≥0) : ℝ) :=
    NNReal.continuous_coe.comp (hC.apprSeq n).continuous
  have hint := measurable_integral_of_continuous_bounded ν H _ hcont 1 fun x => by
    rw [NNReal.abs_eq]; exact_mod_cast HasOuterApproxClosed.apprSeq_apply_le_one hC n x
  have heq : ∀ a, ∫⁻ x, (hC.apprSeq n x : ℝ≥0∞) ∂ν a =
      ENNReal.ofReal (∫ x, ((hC.apprSeq n x : ℝ≥0) : ℝ) ∂ν a) := by
    intro a
    rw [ofReal_integral_eq_lintegral_ofReal]
    · simp
    · exact (integrable_const (1 : ℝ)).mono' hcont.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, NNReal.abs_eq]
          exact_mod_cast HasOuterApproxClosed.apprSeq_apply_le_one hC n x)
    · exact Filter.Eventually.of_forall fun x => NNReal.coe_nonneg _
  simp_rw [heq]
  exact hint.ennreal_ofReal

/-- A subprobability-kernel-shaped family is measurable once all `C_c` integrals are. -/
theorem measurable_of_integral_measurable [PseudoMetrizableSpace X] (ν : α → Measure X)
    [∀ a, IsFiniteMeasure (ν a)]
    (H : ∀ f : C_c(X, ℝ), Measurable fun a => ∫ x, f x ∂ν a) : Measurable ν := by
  refine Measurable.measure_of_isPiSystem (S := {s : Set X | IsClosed s}) ?_ isPiSystem_isClosed
    (fun s hs => measurable_measure_closed ν H hs) (measurable_measure_closed ν H isClosed_univ)
  rw [BorelSpace.measurable_eq (α := X), borel_eq_generateFrom_isClosed]

/-- Passing from a uniformly dense family to all of `C_c`: measurability of the integrals. -/
theorem measurable_integral_of_dense {P : Type*} (T : P → C_c(X, ℝ)) (ν : α → Measure X)
    [∀ a, IsFiniteMeasure (ν a)] (hmass : ∀ a, ν a univ ≤ 1)
    (hdense : ∀ f : C_c(X, ℝ), ∀ ε : ℝ, 0 < ε → ∃ F, ∀ x, |T F x - f x| ≤ ε)
    (hT : ∀ F, Measurable fun a => ∫ x, T F x ∂ν a) (f : C_c(X, ℝ)) :
    Measurable fun a => ∫ x, f x ∂ν a := by
  choose F hF using fun k : ℕ => hdense f (1 / ((k : ℝ) + 1)) (by positivity)
  refine measurable_of_tendsto_metrizable (f := fun k a => ∫ x, T (F k) x ∂ν a) (fun k => hT _)
    (tendsto_pi_nhds.2 fun a => ?_)
  have hbd : ∀ k, |∫ x, T (F k) x ∂ν a - ∫ x, f x ∂ν a| ≤ 1 / ((k : ℝ) + 1) := by
    intro k
    rw [← integral_sub (T (F k)).integrable f.integrable]
    have := norm_integral_le_of_norm_le_const (μ := ν a)
      (f := fun x => T (F k) x - f x) (C := 1 / ((k : ℝ) + 1))
      (Filter.Eventually.of_forall fun x => by simpa using hF k x)
    have hreal : (ν a).real univ ≤ 1 := by
      rw [Measure.real]
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hmass a)
    calc |∫ x, (T (F k) x - f x) ∂ν a| = ‖∫ x, (T (F k) x - f x) ∂ν a‖ := (Real.norm_eq_abs _).symm
      _ ≤ 1 / ((k : ℝ) + 1) * (ν a).real univ := this
      _ ≤ 1 / ((k : ℝ) + 1) * 1 := mul_le_mul_of_nonneg_left hreal (by positivity)
      _ = 1 / ((k : ℝ) + 1) := mul_one _
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun k => dist_nonneg) (fun k => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
  rw [Real.dist_eq]
  exact hbd k

end HypoellipticAleksandrov.KineticAleksandrov

module

public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Tactic

/-! # Countable simultaneous extraction of locally bounded integral functionals

This is compact exhaustion and diagonal extraction in weak dual balls, rather than
compactness of globally finite measures. The resulting functionals are reconstructed
as Radon measures in the subsequent Riesz step.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory Filter Topology
namespace HypoellipticAleksandrov.KineticAleksandrov

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- Integration on a compact carrier is a continuous linear functional. -/
def bellmanCompactIntegral (mu : Measure X) [IsFiniteMeasure mu] : C(X, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    ({
      toFun := fun f => ∫ x, f x ∂mu
      map_add' := fun f g => integral_add
        ((BoundedContinuousFunction.mkOfCompact f).integrable mu)
        ((BoundedContinuousFunction.mkOfCompact g).integrable mu)
      map_smul' := fun c f => integral_smul c f } : C(X, ℝ) →ₗ[ℝ] ℝ)
    (mu.real univ) (fun f => by
      have hb := (BoundedContinuousFunction.mkOfCompact f).norm_integral_le_mul_norm mu
      rw [BoundedContinuousFunction.norm_mkOfCompact] at hb
      convert! hb using 1)

/-- Local mass bounds give the corresponding dual norm bounds. -/
theorem bellmanCompactIntegral_norm_le (mu : Measure X) [IsFiniteMeasure mu]
    (C : ℝ) (hC : 0 ≤ C) (hm : mu.real univ ≤ C) :
    ‖bellmanCompactIntegral mu‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro f
  change ‖∫ x, f x ∂mu‖ ≤ C * ‖f‖
  have hb := (BoundedContinuousFunction.mkOfCompact f).norm_integral_le_mul_norm mu
  simp only [BoundedContinuousFunction.norm_mkOfCompact] at hb
  convert! hb.trans (mul_le_mul_of_nonneg_right hm (norm_nonneg _)) using 1

/-- One common subsequence for every compact-exhaustion coordinate and every measure lane. -/
theorem bellman_compact_functionals_subsequence {iota : Type*} [Countable iota]
    (Y : iota → Type*) [∀ i, TopologicalSpace (Y i)] [∀ i, CompactSpace (Y i)]
    [∀ i, SecondCountableTopology (Y i)] [∀ i, T2Space (Y i)]
    [∀ i, MeasurableSpace (Y i)]
    [∀ i, BorelSpace (Y i)] (mu : ℕ → ∀ i, Measure (Y i))
    [∀ n i, IsFiniteMeasure (mu n i)]
    (C : iota → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hm : ∀ n i, (mu n i).real univ ≤ C i) :
    ∃ k : ℕ → ℕ, StrictMono k ∧
      ∀ i, ∃ ell : C(Y i, ℝ) →L[ℝ] ℝ,
        ∀ f : C(Y i, ℝ), Tendsto (fun n => ∫ x, f x ∂mu (k n) i) atTop (𝓝 (ell f)) := by
  let B (i : iota) : Set (WeakDual ℝ C(Y i, ℝ)) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 (C i)
  have hb (i : iota) : IsCompact (B i) := WeakDual.isCompact_closedBall 0 (C i)
  let (i : iota) : CompactSpace (B i) := isCompact_iff_compactSpace.mp (hb i)
  let (i : iota) : TopologicalSpace.MetrizableSpace (B i) :=
    WeakDual.metrizable_of_isCompact ℝ C(Y i, ℝ) (B i) (hb i)
  let u (n : ℕ) : ∀ i, B i := fun i =>
    ⟨StrongDual.toWeakDual (bellmanCompactIntegral (mu n i)), by
      change dist (bellmanCompactIntegral (mu n i)) 0 ≤ C i
      have he : dist (bellmanCompactIntegral (mu n i)) 0 =
          ‖bellmanCompactIntegral (mu n i)‖ := by
        convert! dist_zero_right (bellmanCompactIntegral (mu n i)) using 1
      rw [he]
      exact bellmanCompactIntegral_norm_le _ _ (hC i) (hm n i)⟩
  obtain ⟨ell, k, hk, ht⟩ := CompactSpace.tendsto_subseq u
  refine ⟨k, hk, ?_⟩
  intro i
  refine ⟨WeakDual.toStrongDual (ell i).val, ?_⟩
  intro f
  have hi := (continuous_apply i).tendsto ell |>.comp ht
  have hv := continuous_subtype_val.tendsto (ell i) |>.comp hi
  convert! (WeakDual.eval_continuous f).tendsto (ell i).val |>.comp hv using 1

end HypoellipticAleksandrov.KineticAleksandrov

module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.VagueCompactnessDiagonal
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.VagueCompactnessRiesz
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Tactic

/-! # Compact exhaustion and simultaneous Radon reconstruction -/

@[expose] public section
noncomputable section
open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal CompactlySupported
namespace HypoellipticAleksandrov.KineticAleksandrov

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
/-- Restriction to a compact subtype has exactly the original compact mass. -/
theorem bellman_compact_comap_mass (K : Set X) (hK : IsCompact K) (mu : Measure X) :
    (Measure.comap (Subtype.val : K → X) mu) univ = mu K := by
  rw [(MeasurableEmbedding.subtype_coe hK.measurableSet).comap_apply]
  simp only [image_univ, Subtype.range_coe]

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
/-- A test supported in a compact set has the same integral on its compact carrier. -/
theorem bellman_compact_test_integral (K : Set X) (hK : IsCompact K)
    (mu : Measure X) (f : C_c(X, ℝ)) (hf : tsupport f ⊆ K) :
    (∫ x : K, f x.val ∂Measure.comap Subtype.val mu) = ∫ x, f x ∂mu := by
  rw [integral_subtype_comap hK.measurableSet]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  exact image_eq_zero_of_notMem_tsupport (fun h => hx (hf h))

/-- Countably many locally bounded Radon sequences have one simultaneous vague subsequence. -/
theorem bellman_radon_family_subsequence {iota : Type*} [Countable iota]
    (mu : iota → ℕ → Measure X) [∀ i n, IsFiniteMeasureOnCompacts (mu i n)]
    (hb : ∀ i, ∀ K : Set X, IsCompact K → ∃ C : ℝ≥0, ∀ n, mu i n K ≤ C) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∀ i, ∃ nu : Measure X,
      IsFiniteMeasureOnCompacts nu ∧ Measure.InnerRegular nu ∧
      ∀ f : C_c(X, ℝ), Tendsto (fun n => ∫ x, f x ∂mu i (k n)) atTop
        (𝓝 (∫ x, f x ∂nu)) := by
  let K := CompactExhaustion.choice X
  let Y (w : iota × ℕ) := {x : X // x ∈ K w.2}
  let (w : iota × ℕ) : CompactSpace (Y w) :=
    isCompact_iff_compactSpace.mp (K.isCompact w.2)
  let m (n : ℕ) (w : iota × ℕ) : Measure (Y w) := Measure.comap Subtype.val (mu w.1 n)
  have hm (n : ℕ) (w : iota × ℕ) : m n w univ = mu w.1 n (K w.2) :=
    bellman_compact_comap_mass _ (K.isCompact _) _
  let (n : ℕ) (w : iota × ℕ) : IsFiniteMeasure (m n w) :=
    ⟨by rw [hm]; exact (K.isCompact w.2).measure_lt_top⟩
  have hbound (w : iota × ℕ) := hb w.1 (K w.2) (K.isCompact w.2)
  choose C hC using hbound
  have hmreal (n : ℕ) (w : iota × ℕ) : (m n w).real univ ≤ (C w : ℝ) := by
    rw [measureReal_def, hm]
    have h := ENNReal.toReal_mono (by simp : (C w : ℝ≥0∞) ≠ ∞) (hC w n)
    simpa only [ENNReal.coe_toReal] using h
  obtain ⟨k, hk, ht⟩ := bellman_compact_functionals_subsequence Y m
    (fun w => (C w : ℝ)) (fun w => (C w).property) hmreal
  refine ⟨k, hk, ?_⟩
  intro i
  apply bellman_riesz_of_test_limits (fun n => mu i (k n))
  intro f
  obtain ⟨j, hj⟩ := K.exists_superset_of_isCompact f.hasCompactSupport
  obtain ⟨ell, hell⟩ := ht (i, j)
  let fc : C(Y (i, j), ℝ) := ⟨fun x => f x.val, f.continuous.comp continuous_subtype_val⟩
  refine ⟨ell fc, ?_⟩
  have he (n : ℕ) : (∫ x, fc x ∂m (k n) (i, j)) = ∫ x, f x ∂mu i (k n) :=
    bellman_compact_test_integral _ (K.isCompact j) _ f hj
  simpa only [he] using hell fc

end HypoellipticAleksandrov.KineticAleksandrov

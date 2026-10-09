module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialSobolevExtensionality
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Countable actual-test Galerkin spaces

This module chooses a countable family of genuine smooth compactly supported
zero-trace tests with dense image in the Hilbert realization of spatial
`H¹₀`.  Its finite initial spans supply the approximation spaces used by the
later finite-dimensional Galerkin ODE; no spectral theorem is assumed.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open Filter Set Module
open scoped ENNReal RealInnerProductSpace Topology

variable {d : ℕ} {Ω : Set (PDE.Vec d)}

/-- The H10 Hilbert carrier inherits a second countable topology from spatial L2. -/
noncomputable def h10HilbertGraphSecondCountableTopology
    (hΩ : IsOpen Ω) : SecondCountableTopology (H10HilbertGraph hΩ) := by
  letI : MeasureTheory.SFinite (PDE.volumeOn Ω) := by infer_instance
  letI : MeasurableSpace.CountablyGenerated (PDE.Vec d) := by infer_instance
  letI : MeasureTheory.IsSeparable (PDE.volumeOn Ω) := by infer_instance
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  letI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  letI : SecondCountableTopology (PDE.ScalarLp Ω (2 : ℝ≥0∞)) :=
    MeasureTheory.Lp.SecondCountableTopology
  letI : SecondCountableTopology (PDE.HilbertVectorLp Ω (2 : ℝ≥0∞)) :=
    MeasureTheory.Lp.SecondCountableTopology
  letI : SecondCountableTopology (PDE.H1HilbertAmbient Ω) :=
    WithLp.secondCountableTopology 2 _ _
  letI : SecondCountableTopology (PDE.H1HilbertGraph Ω) := by infer_instance
  exact by infer_instance

/-- The H10 Hilbert carrier is separable. -/
noncomputable instance instSeparableSpaceH10HilbertGraph
    (hΩ : IsOpen Ω) : TopologicalSpace.SeparableSpace (H10HilbertGraph hΩ) := by
  letI : SecondCountableTopology (H10HilbertGraph hΩ) :=
    h10HilbertGraphSecondCountableTopology hΩ
  exact TopologicalSpace.SecondCountableTopology.to_separableSpace

/-- The actual-test map, codomain-restricted to the H10 closure. -/
noncomputable def smoothCompactlySupportedH1HilbertGraphToH10LinearMap
    (hΩ : IsOpen Ω) :
    PDE.WeakTestFunction Ω →ₗ[ℝ] H10HilbertGraph hΩ :=
  (smoothCompactlySupportedH1HilbertGraphLinearMap hΩ).codRestrict
    (h10HilbertGraphClosedSubmodule hΩ).toSubmodule
    fun φ => subset_closure
      (LinearMap.mem_range_self (smoothCompactlySupportedH1HilbertGraphLinearMap hΩ) φ)

@[simp] theorem coe_smoothCompactlySupportedH1HilbertGraphToH10LinearMap_apply
    (hΩ : IsOpen Ω) (φ : PDE.WeakTestFunction Ω) :
    ((smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ :
        H10HilbertGraph hΩ) : PDE.H1HilbertGraph Ω) =
      smoothCompactlySupportedH1HilbertGraphLinearMap hΩ φ :=
  rfl

/-- Smooth approximations to the selected dense sequence in the H10 Hilbert carrier. -/
noncomputable def smoothApproximation
    (hΩ : IsOpen Ω) (m : ℕ) : ℕ → PDE.WeakTestFunction Ω :=
  Classical.choose (exists_tendsto_smooth hΩ (TopologicalSpace.denseSeq (H10HilbertGraph hΩ) m))

private theorem tendsto_smoothApproximation
    (hΩ : IsOpen Ω) (m : ℕ) :
    Tendsto
      (fun k => smoothCompactlySupportedH1HilbertGraphLinearMap hΩ
        (smoothApproximation hΩ m k))
      atTop (𝓝 ((TopologicalSpace.denseSeq (H10HilbertGraph hΩ) m :
        H10HilbertGraph hΩ) : PDE.H1HilbertGraph Ω)) :=
  Classical.choose_spec
    (exists_tendsto_smooth hΩ (TopologicalSpace.denseSeq (H10HilbertGraph hΩ) m))

/-- A countable sequence of genuine zero-trace smooth tests. -/
noncomputable def galerkinTestSequence
    (hΩ : IsOpen Ω) : ℕ → PDE.WeakTestFunction Ω :=
  fun n => smoothApproximation hΩ n.unpair.1 n.unpair.2

/-- Its images in the internally constructed H10 Hilbert carrier. -/
noncomputable def galerkinVector
    (hΩ : IsOpen Ω) : ℕ → H10HilbertGraph hΩ :=
  smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ ∘
    galerkinTestSequence hΩ

theorem denseRange_galerkinVector
    (hΩ : IsOpen Ω) : DenseRange (galerkinVector hΩ) := by
  let q : ℕ → H10HilbertGraph hΩ := TopologicalSpace.denseSeq (H10HilbertGraph hΩ)
  have hqDense : DenseRange q := TopologicalSpace.denseRange_denseSeq (H10HilbertGraph hΩ)
  have hqClosure : Set.range q ⊆ closure (Set.range (galerkinVector hΩ)) := by
    rintro _ ⟨m, rfl⟩
    have hT : Tendsto (fun k : ℕ => galerkinVector hΩ (Nat.pair m k)) atTop (𝓝 (q m)) := by
      apply tendsto_subtype_rng.mpr
      simpa only [q, galerkinVector, Function.comp_apply, galerkinTestSequence,
        Nat.unpair_pair,
        coe_smoothCompactlySupportedH1HilbertGraphToH10LinearMap_apply] using
        (tendsto_smoothApproximation hΩ m)
    apply mem_closure_of_tendsto hT
    filter_upwards with k
    exact ⟨Nat.pair m k, by simp [galerkinVector, galerkinTestSequence]⟩
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_forall
  intro u
  have hu : u ∈ closure (Set.range q) := by
    rw [hqDense.closure_range]
    exact Set.mem_univ u
  have hclosure : closure (Set.range q) ⊆ closure (Set.range (galerkinVector hΩ)) := by
    simpa only [closure_closure] using closure_mono hqClosure
  exact hclosure hu

/-- The span of the first `N` actual-test images; in particular `E 0 = ⊥`. -/
noncomputable def galerkinSpace
    (hΩ : IsOpen Ω) (N : ℕ) :
    Submodule ℝ (H10HilbertGraph hΩ) :=
  Submodule.span ℝ (Set.range fun i : Fin N => galerkinVector hΩ i)

@[simp] theorem galerkinSpace_zero (hΩ : IsOpen Ω) :
    galerkinSpace hΩ 0 = ⊥ := by
  simp [galerkinSpace]

theorem galerkinSpace_mono
    (hΩ : IsOpen Ω) {N M : ℕ} (hNM : N ≤ M) :
    galerkinSpace hΩ N ≤ galerkinSpace hΩ M := by
  rw [galerkinSpace, galerkinSpace]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  apply Submodule.subset_span
  exact ⟨⟨i, lt_of_lt_of_le i.isLt hNM⟩, rfl⟩

noncomputable instance galerkinSpace_finiteDimensional
    (hΩ : IsOpen Ω) (N : ℕ) :
    FiniteDimensional ℝ (galerkinSpace hΩ N) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

theorem dense_iUnion_galerkinSpace
    (hΩ : IsOpen Ω) :
    Dense (⋃ N : ℕ, (galerkinSpace hΩ N : Set (H10HilbertGraph hΩ))) := by
  apply Dense.mono _ (denseRange_galerkinVector hΩ)
  rintro _ ⟨n, rfl⟩
  refine Set.mem_iUnion.2 ⟨n + 1, ?_⟩
  change galerkinVector hΩ n ∈ Submodule.span ℝ
    (Set.range fun i : Fin (n + 1) => galerkinVector hΩ i)
  apply Submodule.subset_span
  exact ⟨⟨n, Nat.lt_succ_self n⟩, rfl⟩

/-- A coordinate basis for the finite ODE on `E N`; no global basis is chosen. -/
noncomputable def galerkinSpaceBasis
    (hΩ : IsOpen Ω) (N : ℕ) :
    Basis (Fin (Module.finrank ℝ (galerkinSpace hΩ N))) ℝ
      (galerkinSpace hΩ N) :=
  Module.finBasis ℝ (galerkinSpace hΩ N)

end HypoellipticAleksandrov.Parabolic.Dirichlet

module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.OriginalTimeSpacetimeTest
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.Separation.Regular

/-!
# Compact support geometry for separated spacetime tests

This module records the compact coordinate projections of a spacetime test
support, constructs a spatial cutoff inside the given open set, and encloses
compact spatial sets in a centered coordinate cube.
-/

@[expose] public section

open Filter Function Set Topology
open scoped Manifold Topology

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The compact time projection of a spacetime test support. -/
def spacetimeTestTimeSupportCompact
    {d : ℕ} {τ₁ τ₂ : ℝ} {O : Set (PDE.Vec d)} {hO : IsOpen O}
    (φ : TestFunction (originalTimeOpenCylinderOpens τ₁ τ₂ O hO) ℝ (⊤ : ℕ∞)) :
    TopologicalSpace.Compacts ℝ :=
  ⟨Prod.fst '' tsupport (φ : TimeVelocity d → ℝ),
    φ.hasCompactSupport.isCompact.image continuous_fst⟩

/-- The compact spatial projection of a spacetime test support. -/
def spacetimeTestSpatialSupportCompact
    {d : ℕ} {τ₁ τ₂ : ℝ} {O : Set (PDE.Vec d)} {hO : IsOpen O}
    (φ : TestFunction (originalTimeOpenCylinderOpens τ₁ τ₂ O hO) ℝ (⊤ : ℕ∞)) :
    TopologicalSpace.Compacts (PDE.Vec d) :=
  ⟨Prod.snd '' tsupport (φ : TimeVelocity d → ℝ),
    φ.hasCompactSupport.isCompact.image continuous_snd⟩

/-- A smooth compact spatial cutoff equal to one near the spatial support projection. -/
theorem exists_spacetimeTest_spatialCutoff
    {d : ℕ} {τ₁ τ₂ : ℝ} {O : Set (PDE.Vec d)} (hO : IsOpen O)
    (φ : TestFunction (originalTimeOpenCylinderOpens τ₁ τ₂ O hO) ℝ (⊤ : ℕ∞)) :
    ∃ χ : PDE.Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) χ ∧
      (∀ᶠ y in 𝓝ˢ (spacetimeTestSpatialSupportCompact φ : Set (PDE.Vec d)), χ y = 1) ∧
      IsCompact (tsupport χ) ∧ tsupport χ ⊆ O := by
  let K : Set (PDE.Vec d) :=
    spacetimeTestSpatialSupportCompact φ
  have hK : IsCompact K :=
    (spacetimeTestSpatialSupportCompact φ).isCompact
  have hKO : K ⊆ O := by
    rintro y ⟨z, hz, rfl⟩
    exact (φ.tsupport_subset hz).2
  obtain ⟨L, hLcompact, hLclosed, hKinterior, hLO⟩ :=
    exists_compact_closed_between hK hO hKO
  obtain ⟨χ, hχOne, hχZero, _hχRange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior
      (I := 𝓘(ℝ, PDE.Vec d)) hK.isClosed
      (by simpa only [interior_interior] using hKinterior)
  have hsupport : support (χ : PDE.Vec d → ℝ) ⊆ L := by
    intro y hy
    by_contra hyL
    exact (mem_support.mp hy) (hχZero y hyL)
  have htsupportL : tsupport χ ⊆ L :=
    closure_minimal hsupport hLclosed
  refine ⟨χ, χ.contMDiff.contDiff, hχOne, ?_, htsupportL.trans hLO⟩
  exact hLcompact.of_isClosed_subset (isClosed_tsupport χ) htsupportL

/-- Every compact set in the coordinate-function model lies in a nondegenerate cube. -/
theorem IsCompact.exists_subset_pi_Icc_vec {d : ℕ} {K : Set (PDE.Vec d)}
    (hK : IsCompact K) :
    ∃ R : ℝ, 0 < R ∧ K ⊆ Set.Icc (fun _ => -R) (fun _ => R) := by
  have hcoord : ∀ i : Fin d, ∃ M : ℝ, ∀ y ∈ K, |y i| ≤ M := by
    intro i
    obtain ⟨M, hM⟩ :=
      hK.exists_bound_of_continuousOn (continuous_apply i).continuousOn
    exact ⟨M, fun y hy => by simpa only [Real.norm_eq_abs] using hM y hy⟩
  choose M hM using hcoord
  let R : ℝ := 1 + ∑ i : Fin d, |M i|
  have hR : 0 < R := by
    dsimp only [R]
    positivity
  refine ⟨R, hR, ?_⟩
  intro y hy
  have hyR (i : Fin d) : |y i| ≤ R := by
    calc
      |y i| ≤ M i := hM i y hy
      _ ≤ |M i| := le_abs_self _
      _ ≤ ∑ j : Fin d, |M j| :=
        Finset.single_le_sum (fun j _ => abs_nonneg (M j)) (Finset.mem_univ i)
      _ ≤ R := by simp only [R]; linarith
  constructor <;> intro i
  · exact (abs_le.mp (hyR i)).1
  · exact (abs_le.mp (hyR i)).2

end HypoellipticAleksandrov.Parabolic.Dirichlet

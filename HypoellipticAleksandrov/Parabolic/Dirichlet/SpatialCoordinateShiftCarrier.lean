module

public import PDEFoundation.Ambient.Basis
public import PDEFoundation.Measure.AffineVolume

/-!
# Spatial coordinate-shift carriers

This module defines the finite union of signed coordinate shifts of a compact
spatial carrier and records its elementary membership and compactness API.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open Set

/-- The finite coordinate-shift carrier of `K` at signed radius `ρ`. -/
def spatialCoordinateShiftCarrier {d : ℕ}
    (K : Set (PDE.Vec d)) (ρ : ℝ) : Set (PDE.Vec d) :=
  ⋃ k : Fin d,
    (fun ys : PDE.Vec d × ℝ => ys.1 + ys.2 • PDE.basisVec k) ''
      (K ×ˢ Set.Icc (-ρ) ρ)

/-- Membership in the coordinate-shift carrier is witnessed by one coordinate
and one signed shift of the original carrier. -/
theorem mem_spatialCoordinateShiftCarrier_iff
    {d : ℕ} {K : Set (PDE.Vec d)} {ρ : ℝ} {x : PDE.Vec d} :
    x ∈ spatialCoordinateShiftCarrier K ρ ↔
      ∃ (y : PDE.Vec d) (k : Fin d) (s : ℝ),
        y ∈ K ∧ |s| ≤ ρ ∧ x = y + s • PDE.basisVec k := by
  unfold spatialCoordinateShiftCarrier
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨k, hx⟩
    rcases hx with ⟨ys, hys, hxy⟩
    rcases hys with ⟨hy, hs⟩
    exact ⟨ys.1, k, ys.2, hy, abs_le.mpr hs, hxy.symm⟩
  · rintro ⟨y, k, s, hy, hs, rfl⟩
    apply Set.mem_iUnion.mpr
    refine ⟨k, (y, s), ⟨hy, abs_le.mp hs⟩, rfl⟩

/-- A point of `K` shifted by an admissible signed amount in one coordinate
belongs to its coordinate-shift carrier. -/
theorem mem_spatialCoordinateShiftCarrier_of_mem_of_abs_le
    {d : ℕ} {K : Set (PDE.Vec d)} {ρ s : ℝ}
    {y : PDE.Vec d} {k : Fin d}
    (hy : y ∈ K) (hs : |s| ≤ ρ) :
    y + s • PDE.basisVec k ∈ spatialCoordinateShiftCarrier K ρ :=
  mem_spatialCoordinateShiftCarrier_iff.mpr ⟨y, k, s, hy, hs, rfl⟩

/-- A coordinate-shift carrier of a compact spatial set is compact. -/
theorem IsCompact.spatialCoordinateShiftCarrier
    {d : ℕ} {K : Set (PDE.Vec d)}
    (hK : IsCompact K) (ρ : ℝ) :
    IsCompact (spatialCoordinateShiftCarrier K ρ) := by
  change IsCompact (⋃ k : Fin d,
    (fun ys : PDE.Vec d × ℝ => ys.1 + ys.2 • PDE.basisVec k) ''
      (K ×ˢ Set.Icc (-ρ) ρ))
  refine isCompact_iUnion fun k => ?_
  have hcontinuous : Continuous (fun ys : PDE.Vec d × ℝ =>
      ys.1 + ys.2 • PDE.basisVec k) :=
    continuous_fst.add (continuous_snd.smul continuous_const)
  exact (hK.prod isCompact_Icc).image hcontinuous

/-- The ambient volume of a compact coordinate-shift carrier is finite. -/
theorem IsCompact.spatialCoordinateShiftCarrier_volume_lt_top
    {d : ℕ} {K : Set (PDE.Vec d)}
    (hK : IsCompact K) (ρ : ℝ) :
    MeasureTheory.volume
      (HypoellipticAleksandrov.Parabolic.Dirichlet.spatialCoordinateShiftCarrier K ρ) < ⊤ :=
  (IsCompact.spatialCoordinateShiftCarrier hK ρ).measure_lt_top

/-- In positive dimension, a nonnegative-radius coordinate-shift carrier
contains its original spatial set. -/
theorem subset_spatialCoordinateShiftCarrier
    {d : ℕ} {K : Set (PDE.Vec d)} {ρ : ℝ}
    (hd : 0 < d) (hρ : 0 ≤ ρ) :
    K ⊆ spatialCoordinateShiftCarrier K ρ := by
  intro y hy
  apply mem_spatialCoordinateShiftCarrier_iff.mpr
  refine ⟨y, ⟨0, hd⟩, 0, hy, ?_, ?_⟩
  · simpa only [abs_zero] using hρ
  · simp only [zero_smul, add_zero]

end HypoellipticAleksandrov.Parabolic.Dirichlet

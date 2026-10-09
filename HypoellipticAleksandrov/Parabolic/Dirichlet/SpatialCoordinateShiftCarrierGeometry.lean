module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialCoordinateShiftCarrier
public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientCollar
public import Mathlib.Analysis.Convex.Segment

/-!
# Geometry of spatial coordinate-shift carriers

This module gives the compact-open shift radius and the segment containment
facts for the literal finite coordinate-shift carrier used in spatial
difference-quotient arguments.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open Set
open scoped Convex

/-- A compact spatial carrier inside an open set has a positive common signed
coordinate-shift radius whose literal carrier stays in the open set. -/
theorem IsCompact.exists_spatialCoordinateShiftCarrier_subset_open
    {d : ℕ} {K Ω : Set (PDE.Vec d)}
    (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω) :
    ∃ δ : ℝ, 0 < δ ∧
      HypoellipticAleksandrov.Parabolic.Dirichlet.spatialCoordinateShiftCarrier K δ ⊆ Ω := by
  let K' : Set (TimeVelocity d) := ({0} : Set ℝ) ×ˢ K
  let U : Set (TimeVelocity d) := Set.univ ×ˢ Ω
  have hK' : IsCompact K' := isCompact_singleton.prod hK
  have hU : IsOpen U := isOpen_univ.prod hΩ
  have hK'U : K' ⊆ U := by
    intro z hz
    exact ⟨Set.mem_univ _, hKΩ hz.2⟩
  obtain ⟨δ, hδ, _hthickening, hshift⟩ :=
    IsCompact.exists_spatialShift_cthickening_collar hK' hU hK'U
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  rcases mem_spatialCoordinateShiftCarrier_iff.mp hx with ⟨y, k, s, hy, hs, rfl⟩
  exact (hshift k s hs (show (0, y) ∈ K' from ⟨by simp, hy⟩)).2

/-- Containment of the coordinate-shift carrier gives the corresponding
signed coordinate-shift map into the outer set. -/
theorem mapsTo_add_smul_basisVec_of_spatialCoordinateShiftCarrier_subset
    {d : ℕ} {K Ω : Set (PDE.Vec d)} {δ h : ℝ}
    (hcarrier : spatialCoordinateShiftCarrier K δ ⊆ Ω)
    (k : Fin d) (hh : |h| ≤ δ) :
    Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k) K Ω := by
  intro y hy
  exact hcarrier (mem_spatialCoordinateShiftCarrier_of_mem_of_abs_le hy hh)

/-- A time--velocity coordinate segment over `K` stays in the closed time slab
and the literal signed coordinate-shift carrier. -/
theorem segment_spatialShift_subset_Icc_prod_spatialCoordinateShiftCarrier
    {d : ℕ} {K : Set (PDE.Vec d)} {T δ h : ℝ}
    (k : Fin d) (z : TimeVelocity d)
    (hh : |h| ≤ δ) (hz : z ∈ Set.Icc 0 T ×ˢ K) :
    [z -[ℝ] spatialShift k h z] ⊆
      Set.Icc 0 T ×ˢ spatialCoordinateShiftCarrier K δ := by
  intro w hw
  rw [segment_eq_image_lineMap] at hw
  rcases hw with ⟨t, ht, rfl⟩
  have hline : AffineMap.lineMap z (spatialShift k h z) t =
      (z.1, z.2 + (t * h) • PDE.basisVec k) := by
    rcases z with ⟨r, y⟩
    ext <;> simp [AffineMap.lineMap_apply_module', spatialShift_apply, smul_smul,
      add_comm]
  rw [hline]
  refine ⟨hz.1, mem_spatialCoordinateShiftCarrier_of_mem_of_abs_le hz.2 ?_⟩
  calc
    |t * h| = t * |h| := by rw [abs_mul, abs_of_nonneg ht.1]
    _ ≤ 1 * |h| := mul_le_mul_of_nonneg_right ht.2 (abs_nonneg h)
    _ = |h| := one_mul _
    _ ≤ δ := hh

end HypoellipticAleksandrov.Parabolic.Dirichlet

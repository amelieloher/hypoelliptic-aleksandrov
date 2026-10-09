module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.GalerkinDense

/-!
# Dense range of actual smooth tests in spatial H¹₀

This module records that the existing inclusion of bundled smooth compactly
supported tests into the spatial `H¹₀` Hilbert graph has dense range.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open Filter Set
open scoped Topology

/-- The existing inclusion of bundled smooth compactly supported tests into
the spatial `H¹₀` Hilbert graph has dense range. -/
theorem denseRange_smoothCompactlySupportedH1HilbertGraphToH10LinearMap
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) :
    DenseRange
      (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ) := by
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_forall
  intro u
  rcases exists_tendsto_smooth hΩ u with ⟨φ, hφ⟩
  have hT : Tendsto
      (fun n => smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ (φ n))
      atTop (𝓝 u) := by
    apply tendsto_subtype_rng.mpr
    simpa only [coe_smoothCompactlySupportedH1HilbertGraphToH10LinearMap_apply] using hφ
  apply mem_closure_of_tendsto hT
  filter_upwards with n
  exact ⟨φ n, rfl⟩

end HypoellipticAleksandrov.Parabolic.Dirichlet

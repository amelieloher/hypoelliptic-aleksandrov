module

public import HypoellipticAleksandrov.Measure.LpProductRepresentative
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeProductMeasure

/-!
# Reverse-time product representatives

This module specializes the quotient-safe nested `L²` product representative
to reverse-time Bochner curves on an open spatial domain.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- A reverse-time spatial `L²` curve has a joint product `L²` representative
with the expected spatial slices for almost every reverse time. -/
theorem exists_reverseTimeL2H_product_representative
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (q : ReverseTimeL2H hΩ T) :
    ∃ Q : ℝ × PDE.Vec d → ℝ,
      MemLp Q (2 : ℝ≥0∞)
        ((reverseTimeVolume T).prod (PDE.volumeOn Ω)) ∧
      ∀ᵐ τ ∂reverseTimeVolume T,
        (fun y => Q (τ, y)) =ᵐ[PDE.volumeOn Ω] fun y => q τ y := by
  letI : SFinite (PDE.volumeOn Ω) := by infer_instance
  exact HypoellipticAleksandrov.exists_uncurry_memLp_two
    (reverseTimeVolume T) (PDE.volumeOn Ω) q

/-- A reverse-time `H¹₀` curve has a joint scalar value representative whose
spatial slices agree almost everywhere with its timewise spatial values. -/
theorem exists_reverseTimeL2V_value_product_representative
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (u : ReverseTimeL2V hΩ T) :
    ∃ U : TimeVelocity d → ℝ,
      MemLp U (2 : ℝ≥0∞)
        (timeVelocityVolumeOn (reverseTimeOpenInterval T ×ˢ Ω)) ∧
      ∀ᵐ τ ∂reverseTimeVolume T,
        (fun y => U (τ, y)) =ᵐ[PDE.volumeOn Ω]
          fun y => valueCLM hΩ (u τ) y := by
  obtain ⟨U, hU_memLp, hU_slice⟩ :=
    exists_reverseTimeL2H_product_representative hΩ T
      (reverseTimeValueCLM hΩ T u)
  refine ⟨U, ?_, ?_⟩
  · rw [← reverseTimeVolume_prod_volumeOn_eq_timeVelocityVolumeOn T Ω]
    exact hU_memLp
  filter_upwards [hU_slice, coeFn_reverseTimeValueCLM hΩ T u] with τ hU hvalue
  filter_upwards [hU] with y hy
  rw [hy, hvalue]

end HypoellipticAleksandrov.Parabolic.Dirichlet

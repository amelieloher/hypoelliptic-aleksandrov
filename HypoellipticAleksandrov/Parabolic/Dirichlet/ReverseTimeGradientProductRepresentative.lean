module

public import HypoellipticAleksandrov.Measure.LpProductRepresentative
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeBochner
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeProductMeasure

/-!
# Reverse-time gradient coordinate product representatives

This module gives scalar product representatives for the finitely many
coordinates of the quotient-valued spatial weak gradient of a reverse-time
Bochner curve.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The Bochner lift of one scalar coordinate of the spatial weak-gradient
map. -/
noncomputable def reverseTimeGradientCoordCLM
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (j : Fin d) :
    ReverseTimeL2V hΩ T →L[ℝ] ReverseTimeL2H hΩ T :=
  ((PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j).comp
    (gradientCLM hΩ)).compLpL (2 : ℝ≥0∞) (reverseTimeVolume T)

/-- The reverse-time gradient-coordinate lift agrees almost everywhere with
the corresponding timewise spatial coordinate map. -/
theorem coeFn_reverseTimeGradientCoordCLM
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (j : Fin d)
    (u : ReverseTimeL2V hΩ T) :
    reverseTimeGradientCoordCLM hΩ T j u =ᵐ[reverseTimeVolume T]
      fun τ => PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
        (gradientCLM hΩ (u τ)) :=
  ContinuousLinearMap.coeFn_compLpL
    ((PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j).comp (gradientCLM hΩ)) u

/-- The scalar coordinates of a reverse-time `H¹₀` gradient have joint
product representatives with a common almost-everywhere time-slice event. -/
theorem exists_reverseTimeL2V_gradient_coord_product_representatives
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (u : ReverseTimeL2V hΩ T) :
    ∃ G : Fin d → TimeVelocity d → ℝ,
      (∀ j, MemLp (G j) (2 : ℝ≥0∞)
        (timeVelocityVolumeOn (reverseTimeOpenInterval T ×ˢ Ω))) ∧
      ∀ᵐ τ ∂reverseTimeVolume T, ∀ j,
        (fun y => G j (τ, y)) =ᵐ[PDE.volumeOn Ω]
          fun y => gradientCLM hΩ (u τ) y j := by
  letI : SFinite (PDE.volumeOn Ω) := by infer_instance
  choose G hG_memLp hG_slice using fun j =>
    HypoellipticAleksandrov.exists_uncurry_memLp_two
      (reverseTimeVolume T) (PDE.volumeOn Ω)
      (reverseTimeGradientCoordCLM hΩ T j u)
  refine ⟨G, ?_, ?_⟩
  · intro j
    rw [← reverseTimeVolume_prod_volumeOn_eq_timeVelocityVolumeOn T Ω]
    exact hG_memLp j
  · apply ae_all_iff.mpr
    intro j
    filter_upwards [hG_slice j, coeFn_reverseTimeGradientCoordCLM hΩ T j u]
      with τ hG hcoord
    rw [hcoord] at hG
    exact hG.trans (PDE.coeFn_hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j
      (gradientCLM hΩ (u τ)))

end HypoellipticAleksandrov.Parabolic.Dirichlet

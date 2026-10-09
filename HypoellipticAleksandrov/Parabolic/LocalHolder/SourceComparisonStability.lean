module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementSource
import HypoellipticAleksandrov.Parabolic.ScalarDirichletComparison

/-! # Stability of signed source corrections

Equal boundary data reduce comparison of two corrections to the zero-boundary time barrier.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Set

/-- Corrections with the same boundary data differ by at most the time-integrated source error. -/
theorem abs_solution_sub_le_source_error {n : ℕ} {Ω : Set (PDE.Vec n)} {a T : ℝ}
    (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (haT : a < T)
    (A : CoefficientField n) (hAc : IsContinuousCoefficient A)
    (hApsd : ∀ t v, (A t v).PosSemidef)
    (F G : ℝ → PDE.Vec n → ℝ) (φ : PDE.Vec n → ℝ) (h : TimeVelocity n → ℝ)
    (u v : TimeVelocity n → ℝ)
    (hu : IsClassicalBackwardDirichletSolution a T Ω A
      (fun _ _ => 0) (fun _ _ => 0) F φ h u)
    (hv : IsClassicalBackwardDirichletSolution a T Ω A
      (fun _ _ => 0) (fun _ _ => 0) G φ h v)
    (M : ℝ) (hM : 0 ≤ M)
    (hFG : ∀ z ∈ scalarParabolicOpenCylinder a T Ω, |F z.1 z.2 - G z.1 z.2| ≤ M) :
    ∀ z ∈ scalarParabolicClosedCylinder a T Ω, |u z - v z| ≤ M * (T - z.1) := by
  have hsub := isClassicalBackwardDirichletSolution_sub hu hv
  have hzero : IsClassicalBackwardDirichletSolution a T Ω A
      (fun _ _ => 0) (fun _ _ => 0) (fun t y => F t y - G t y)
      (fun _ => 0) (fun _ => 0) (fun z => u z - v z) := by
    simpa only [sub_self] using hsub
  exact abs_zeroBoundary_solution_le_time hΩo hΩb haT A hAc hApsd
    (fun t y => F t y - G t y) M hM hFG (fun z => u z - v z) hzero

/-- A uniform source error gives a uniform finite-horizon correction error. -/
theorem abs_solution_sub_le_uniform_source_error {n : ℕ}
    {Ω : Set (PDE.Vec n)} {a T : ℝ}
    (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (haT : a < T)
    (A : CoefficientField n) (hAc : IsContinuousCoefficient A)
    (hApsd : ∀ t v, (A t v).PosSemidef)
    (F G : ℝ → PDE.Vec n → ℝ) (φ : PDE.Vec n → ℝ) (h : TimeVelocity n → ℝ)
    (u v : TimeVelocity n → ℝ)
    (hu : IsClassicalBackwardDirichletSolution a T Ω A
      (fun _ _ => 0) (fun _ _ => 0) F φ h u)
    (hv : IsClassicalBackwardDirichletSolution a T Ω A
      (fun _ _ => 0) (fun _ _ => 0) G φ h v)
    (M : ℝ) (hM : 0 ≤ M)
    (hFG : ∀ z ∈ scalarParabolicOpenCylinder a T Ω, |F z.1 z.2 - G z.1 z.2| ≤ M) :
    ∀ z ∈ scalarParabolicClosedCylinder a T Ω, |u z - v z| ≤ M * (T - a) := by
  intro z hz
  exact (abs_solution_sub_le_source_error hΩo hΩb haT A hAc hApsd F G φ h u v
    hu hv M hM hFG z hz).trans (mul_le_mul_of_nonneg_left (sub_le_sub_left hz.1.1 T) hM)

end HypoellipticAleksandrov.Parabolic.LocalHolder

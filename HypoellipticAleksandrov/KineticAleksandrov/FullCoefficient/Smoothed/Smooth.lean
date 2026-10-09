module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothed.Densities
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Coefficient
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Bounds

/-!
# Smoothness of `ρ`, `J`, `β_h` in `(τ, y)` and the `τ`-derivative of `ρ`

The smoothed equation: `ρ` and `J` are smooth jointly in `(τ, y)` (on all of
`ℝ × ℝ^{2d}`, hence on `(τ₁, τ₂) × ℝ^{2d}`), `∂_τ ρ` is obtained under the integral sign, and
`β_h = J / ρ` is smooth where `ρ > 0`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open MeasureTheory
open scoped MatrixOrder

variable {d : ℕ} {δ : ℝ} {η : ℝ → ℝ} {lam Lam : ℝ}
  (Φ : SmoothingKernelFamily d lam) {h : ℝ} {Γ' : Measure (ℝ × EvolutionAmbientState d)}
  [IsFiniteMeasure Γ'] {Bt : ℝ → EvolutionAmbientState d → PDE.Mat d}

/-- `ρ` is jointly smooth in `(τ, y)`. -/
theorem contDiff_smoothedDensity (hη : IsMollifier δ η) (hh : 0 < h) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × EvolutionAmbientState d =>
      smoothedDensity Φ η h Γ' p.1 p.2) := by
  have : (fun p : ℝ × EvolutionAmbientState d => smoothedDensity Φ η h Γ' p.1 p.2) =
      timeSmoothed Φ η h (fun _ => 1) Γ' :=
    funext fun p => smoothedDensity_eq Φ hη hh p.1 p.2
  rw [this]
  exact contDiff_timeSmoothed Φ hη hh measurable_const (Cf := 1) fun _ => by simp

/-- The `τ`-derivative of `ρ` is obtained under the integral sign. -/
theorem hasDerivAt_smoothedDensity (hη : IsMollifier δ η) (hh : 0 < h) (τ : ℝ)
    (y : EvolutionAmbientState d) :
    HasDerivAt (fun τ' => smoothedDensity Φ η h Γ' τ' y)
      (∫ a, deriv η (τ - a.1) * Φ.kernel h (y - a.2) ∂Γ') τ := by
  have h1 : (fun τ' => smoothedDensity Φ η h Γ' τ' y) =
      fun τ' => timeSmoothed Φ η h (fun _ => 1) Γ' (τ', y) :=
    funext fun τ' => smoothedDensity_eq Φ hη hh τ' y
  rw [h1]
  simpa using hasDerivAt_timeSmoothed Φ hη hh (f := fun _ => 1) measurable_const (Cf := 1)
    (fun _ => by simp) τ y

variable (hη : IsMollifier δ η) (hmarg : Γ'.map Prod.fst ≤ volume)
  (hBm : ∀ i j, Measurable fun q : ℝ × EvolutionAmbientState d => Bt q.1 q.2 i j)
  (hBb : ∀ t y i j, |Bt t y i j| ≤ Lam) (hLam : 0 ≤ Lam)
  (hBl : ∀ t y, lam • (1 : PDE.Mat d) ≤ Bt t y ∧ Bt t y ≤ Lam • (1 : PDE.Mat d))

include hη hmarg hBm hBb hLam hBl in
/-- The entries of `J` are jointly smooth in `(τ, y)`. -/
theorem contDiff_smoothedFlux (hh : 0 < h) (i j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × EvolutionAmbientState d =>
      smoothedFlux Φ η Bt Lam h Γ' p.1 p.2 i j) := by
  have : (fun p : ℝ × EvolutionAmbientState d => smoothedFlux Φ η Bt Lam h Γ' p.1 p.2 i j) =
      timeSmoothed Φ η h (fun a => Bt a.1 a.2 i j) Γ' :=
    funext fun p => smoothedFlux_apply_eq Φ hη hmarg hBm hBb hLam hBl hh i j p.2
  rw [this]
  exact contDiff_timeSmoothed Φ hη hh (hBm i j) (Cf := Lam) fun a => hBb _ _ i j

include hη hmarg hBm hBb hLam hBl in
/-- `β_h = J / ρ` is jointly smooth on the set `{ρ > 0}`. -/
theorem contDiffOn_smoothedBeta (hh : 0 < h) (i j : Fin d) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × EvolutionAmbientState d =>
      smoothedBeta Φ η Bt Lam h Γ' p.1 p.2 i j)
      {p | 0 < smoothedDensity Φ η h Γ' p.1 p.2} := by
  have hρ := contDiff_smoothedDensity Φ (Γ' := Γ') hη hh
  have hJ := contDiff_smoothedFlux Φ hη hmarg hBm hBb hLam hBl hh i j
  refine (hJ.contDiffOn.div hρ.contDiffOn fun p hp => hp.ne').congr fun p hp => ?_
  have hm : averagedSlice η p.1 Γ' ≠ 0 := by
    intro h0
    have : smoothedDensity Φ η h Γ' p.1 p.2 = 0 := by
      unfold smoothedDensity; rw [h0]; exact smoothDensity_zero Φ p.2
    exact absurd hp (by simp [this])
  unfold smoothedBeta
  rw [smoothCoefficient_of_ne_zero Φ _ hm]
  simp [smoothedFlux, smoothedDensity, div_eq_inv_mul, Pi.div_apply]

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

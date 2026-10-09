module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothed.Joint
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothed.Beta
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Defs

/-!
# The smoothed density `ρ`, flux `J` and coefficient `β_h`

The smoothed Green measure: `ρ(τ, y) = (ν^δ_τ)_h(y)`, `J(τ, y) = ((Bν)^δ_τ)_h(y)` and
`β_h = J / ρ` (`λ I` on zero slices).  They are defined through the smoothing package
(`smoothDensity`, `smoothFlux`, `smoothCoefficient`) applied to the averaged slice and the
averaged coefficient, and identified with the time-averaged integrals of `Smoothed/Joint.lean`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open MeasureTheory
open scoped MatrixOrder

variable {d : ℕ} {δ : ℝ} {η : ℝ → ℝ} {lam Lam : ℝ}

/-- The smoothed density `ρ(τ, y) = (ν^δ_τ)_h(y)`. -/
def smoothedDensity (Φ : SmoothingKernelFamily d lam) (η : ℝ → ℝ) (h : ℝ)
    (Γ' : Measure (ℝ × EvolutionAmbientState d)) (τ : ℝ) (y : EvolutionAmbientState d) : ℝ :=
  smoothDensity Φ h (averagedSlice η τ Γ') y

/-- The smoothed flux `J(τ, y) = ((Bν)^δ_τ)_h(y)`. -/
def smoothedFlux (Φ : SmoothingKernelFamily d lam) (η : ℝ → ℝ)
    (Bt : ℝ → EvolutionAmbientState d → PDE.Mat d) (Lam h : ℝ)
    (Γ' : Measure (ℝ × EvolutionAmbientState d)) (τ : ℝ) (y : EvolutionAmbientState d) :
    PDE.Mat d :=
  smoothFlux Φ h (averagedCoefficient η Bt lam Lam τ Γ') (averagedSlice η τ Γ') y

/-- The smoothed coefficient `β_h(τ, y) = J / ρ`, equal to `λ I` on zero slices. -/
def smoothedBeta (Φ : SmoothingKernelFamily d lam) (η : ℝ → ℝ)
    (Bt : ℝ → EvolutionAmbientState d → PDE.Mat d) (Lam h : ℝ)
    (Γ' : Measure (ℝ × EvolutionAmbientState d)) (τ : ℝ) (y : EvolutionAmbientState d) :
    PDE.Mat d :=
  smoothCoefficient Φ h (averagedCoefficient η Bt lam Lam τ Γ') (averagedSlice η τ Γ') y

variable (Φ : SmoothingKernelFamily d lam) {h τ : ℝ} {Γ' : Measure (ℝ × EvolutionAmbientState d)}
  [IsFiniteMeasure Γ'] {Bt : ℝ → EvolutionAmbientState d → PDE.Mat d}

theorem continuous_kernel_sub (hh : 0 < h) (y : EvolutionAmbientState d) :
    Continuous fun y' => Φ.kernel h (y - y') :=
  (Φ.contDiff hh).continuous.comp (continuous_const.sub continuous_id)

theorem abs_kernel_sub_le (hh : 0 < h) :
    ∃ C : ℝ, ∀ (y y' : EvolutionAmbientState d), |Φ.kernel h (y - y')| ≤ C := by
  obtain ⟨C, -, hC⟩ := Φ.exists_sup_bound (K := {h}) isCompact_singleton (by simpa using hh)
  exact ⟨C, fun y y' => by rw [abs_of_pos (Φ.pos hh _)]; exact hC h rfl _⟩

omit [IsFiniteMeasure Γ'] in
/-- `ρ` is the time-averaged smoothing of `Γ'`. -/
theorem smoothedDensity_eq (hη : IsMollifier δ η) (hh : 0 < h) (τ : ℝ)
    (y : EvolutionAmbientState d) :
    smoothedDensity Φ η h Γ' τ y = timeSmoothed Φ η h (fun _ => 1) Γ' (τ, y) := by
  unfold smoothedDensity smoothDensity timeSmoothed
  rw [integral_averagedSlice hη (continuous_kernel_sub Φ hh y).measurable]
  simp

variable (hη : IsMollifier δ η) (hmarg : Γ'.map Prod.fst ≤ volume)
  (hBm : ∀ i j, Measurable fun q : ℝ × EvolutionAmbientState d => Bt q.1 q.2 i j)
  (hBb : ∀ t y i j, |Bt t y i j| ≤ Lam) (hLam : 0 ≤ Lam)
  (hBl : ∀ t y, lam • (1 : PDE.Mat d) ≤ Bt t y ∧ Bt t y ≤ Lam • (1 : PDE.Mat d))

include hη hmarg hBm hBb hLam hBl in
/-- The entries of `J` are time-averaged smoothings of the entries of `B`. -/
theorem smoothedFlux_apply_eq (hh : 0 < h) (i j : Fin d) (y : EvolutionAmbientState d) :
    smoothedFlux Φ η Bt Lam h Γ' τ y i j =
      timeSmoothed Φ η h (fun a => Bt a.1 a.2 i j) Γ' (τ, y) := by
  obtain ⟨C, hC⟩ := abs_kernel_sub_le Φ hh
  unfold smoothedFlux smoothFlux smoothFluxEntry timeSmoothed
  simp only [Matrix.of_apply]
  have := integral_mul_averagedCoefficient hη hmarg hBm hBb hLam hBl (lam := lam) (τ := τ) i j
    (continuous_kernel_sub Φ hh y).measurable (fun y' => hC y y')
  rw [this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  simp only; ring

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

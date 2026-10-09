module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Absorb.DensityAbstract
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Absorb.DensityScaling
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Forward.Slices

/-!
# The Green density from the smoothed `L^q` bound

for the Green measure
of a point mass: if the smoothed slice densities `ρ_ε(τ, y) = (ν_τ)_ε(y)` of the Gaussian flow
family satisfy `∫∫ ρ_ε^q ≤ C₁ T^{1-2d(q-1)}` for every `ε > 0`, then the Green measure has a
Lebesgue density `G` with `‖G‖_{L^q} ≤ C₁^{1/q} T^{(1-2d(q-1))/q}`.  This is the form in which
the smoothing-time estimate of the absorption estimate is consumed.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open MeasureTheory ProbabilityTheory
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal

variable {d : ℕ}

/-- `(C₁ T^δ)^{1/q} = C₁^{1/q} T^{δ/q}` for `C₁ ≥ 0`, `T > 0`. -/
theorem rpow_mul_rpow_div {C₁ T δ q : ℝ} (hC : 0 ≤ C₁) (hT : 0 < T) :
    (C₁ * T ^ δ) ^ (1 / q) = C₁ ^ (1 / q) * T ^ (δ / q) := by
  rw [Real.mul_rpow hC (Real.rpow_pos_of_pos hT _).le, ← Real.rpow_mul hT.le]
  congr 2
  ring

/-- **The Green density from smoothed bounds**. -/
theorem greenDensity_of_smoothed_bound {lam : ℝ} (hl : 0 < lam) {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ) (σ₀ : ℝ) (p : EvolutionState Ω γ σ₀)
    {T : ℝ} (hT : 0 < T) (Γ : Measure (ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d))
    (hΓ : IsGreenMeasure K σ₀ (ENNReal.ofReal T) (Measure.dirac p) Γ) {q C₁ δ : ℝ}
    (hq : 1 < q) (hC₁ : 0 ≤ C₁)
    (hbound : ∀ ε : ℝ, 0 < ε →
      ∫⁻ x, ENNReal.ofReal
          (smoothDensity (flowKernelFamily (d := d) hl) ε (sliceMeasure K σ₀ p x.1) x.2 ^ q)
        ∂((elapsedVolume (ENNReal.ofReal T)).prod (volume : Measure (EvolutionAmbientState d))) ≤
        ENNReal.ofReal (C₁ * T ^ δ)) :
    ∃ G : ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState d → ℝ≥0∞, Measurable G ∧
      Γ = ((elapsedVolume (ENNReal.ofReal T)).prod
        (volume : Measure (EvolutionAmbientState d))).withDensity G ∧
      eLpNorm G (ENNReal.ofReal q) ((elapsedVolume (ENNReal.ofReal T)).prod
        (volume : Measure (EvolutionAmbientState d))) ≤
          ENNReal.ofReal (C₁ ^ (1 / q) * T ^ (δ / q)) := by
  have hq0 : 0 < q := by linarith
  have : IsFiniteMeasure Γ :=
    ⟨lt_of_le_of_lt (greenMeasure_mass_le K σ₀ T hT (Measure.dirac p) Γ hΓ)
      (by simp)⟩
  have hK : 0 ≤ C₁ ^ (1 / q) * T ^ (δ / q) :=
    mul_nonneg (Real.rpow_nonneg hC₁ _) (Real.rpow_nonneg hT.le _)
  refine exists_density_of_smoothed_bounds (flowKernelFamily_isApproxIdentity hl)
    (sliceKernel K σ₀ p (ENNReal.ofReal T)) Γ
    (green_eq_compProd K σ₀ (ENNReal.ofReal T) p Γ hΓ) hq hK ?_
  intro ε hε
  have hbase : 0 ≤ C₁ * T ^ δ := mul_nonneg hC₁ (Real.rpow_nonneg hT.le _)
  have : (C₁ ^ (1 / q) * T ^ (δ / q)) ^ q = C₁ * T ^ δ := by
    rw [← rpow_mul_rpow_div hC₁ hT, ← Real.rpow_mul hbase, one_div_mul_cancel hq0.ne',
      Real.rpow_one]
  rw [this]
  exact hbound ε hε

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

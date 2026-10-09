module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothed.Divergence
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Uniform

/-!
# The smoothing package on every averaged slice

The smoothing estimates apply on every slice.  Every averaged slice
`ν^δ_τ` is a finite measure of mass at most one and the averaged coefficient `β_τ` is an
admissible coefficient, so the uniform integrability package `package_uniform` of the smoothing
estimates holds for all `τ` with one constant, depending only on `(d, λ, Λ, q, K, Φ)`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open MeasureTheory

variable {d : ℕ} {δ : ℝ} {η : ℝ → ℝ} {lam Lam : ℝ} {τ : ℝ}
  {Γ' : Measure (ℝ × EvolutionAmbientState d)} {Bt : ℝ → EvolutionAmbientState d → PDE.Mat d}

/-- Every averaged slice is a finite measure. -/
theorem isFiniteMeasure_averagedSlice_of_datum (hη : IsMollifier δ η)
    (hD : IsSmoothingDatum lam Lam Bt Γ') : IsFiniteMeasure (averagedSlice η τ Γ') :=
  isFiniteMeasure_averagedSlice hη hD.marginal

/-- Every averaged slice has mass at most one. -/
theorem averagedSlice_real_univ_le_of_datum (hη : IsMollifier δ η)
    (hD : IsSmoothingDatum lam Lam Bt Γ') :
    (averagedSlice η τ Γ').real Set.univ ≤ 1 :=
  averagedSlice_real_univ_le hη hD.marginal

/-- The averaged coefficient is an admissible coefficient on every slice. -/
theorem isAdmissibleCoefficient_of_datum (hD : IsSmoothingDatum lam Lam Bt Γ') :
    IsAdmissibleCoefficient lam Lam (averagedCoefficient η Bt lam Lam τ Γ') :=
  isAdmissibleCoefficient_averagedCoefficient hD.symm hD.loewner

/-- **The smoothing estimates apply on every slice**, uniformly in `τ`: for `1 < q`, a compact
parameter
set `K ⊆ (0, ∞)`, there is one constant for all `h ∈ K` and all `τ`. -/
theorem smoothed_package_uniform (Φ : SmoothingKernelFamily d lam) (hη : IsMollifier δ η)
    (hD : IsSmoothingDatum lam Lam Bt Γ') {q : ℝ} (hq : 1 < q) {K : Set ℝ}
    (hK : IsCompact K) (hsub : K ⊆ Set.Ioi 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h ∈ K, ∀ τ : ℝ,
      PackageIntegrable Φ h (averagedCoefficient η Bt lam Lam τ Γ') (averagedSlice η τ Γ') q C := by
  obtain ⟨C, hC0, hC⟩ := package_uniform Φ hD.lam_pos hD.lam_le hq hK hsub (M := 1) zero_le_one
  exact ⟨C, hC0, fun h hh τ => hC h hh _ (isFiniteMeasure_averagedSlice_of_datum hη hD)
    (averagedSlice_real_univ_le_of_datum hη hD) _ (isAdmissibleCoefficient_of_datum hD)⟩

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

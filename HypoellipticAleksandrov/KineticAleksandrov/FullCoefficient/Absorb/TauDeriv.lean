module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Absorb.SliceMeas
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Absorb.TauGeneric

/-!
# The `h`-derivatives of the space-time quantities `E(h)` and `F(h)`

The time-integrated identities: for a smoothing datum and `0 < h`,
`E(s) = ∫_{(τ₁,τ₂)} ∫ ρ_s^q` and `F(s) = ∫_{(τ₁,τ₂)} ∫ ρ_s^q |β_s|²` are differentiable at `h`,
with derivatives the `τ`-integrals of the slice derivatives. The slice derivatives are
differentiated under the `τ`-integral using the uniform bounds of `SliceUniform`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ} {δ : ℝ} {η : ℝ → ℝ} {lam Lam : ℝ} (Φ : SmoothingKernelFamily d lam)
  {Bt : ℝ → EvolutionAmbientState d → PDE.Mat d} {Γ' : Measure (ℝ × EvolutionAmbientState d)}
  [IsFiniteMeasure Γ'] {h q τ₁ τ₂ : ℝ}

theorem closedBall_subset_Ioi (hh : 0 < h) :
    Metric.closedBall h (h / 2) ⊆ Set.Ioi 0 := fun s hs => by
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hs
  simp only [Set.mem_Ioi]; linarith [hs.1]

/-- The time-integrated identities: `E` is differentiable, with the `τ`-integral of the slice
derivative.
-/
theorem hasDerivAt_totalPow (hη : IsMollifier δ η) (hD : IsSmoothingDatum lam Lam Bt Γ')
    (hh : 0 < h) (hq : 1 < q) :
    Integrable (fun τ => ∫ y, integrandPowDeriv Φ h q (averagedSlice η τ Γ') y)
      (volume.restrict (Set.Ioo τ₁ τ₂)) ∧
    HasDerivAt (fun s => ∫ τ in Set.Ioo τ₁ τ₂, ∫ y, smoothedDensity Φ η s Γ' τ y ^ q)
      (∫ τ in Set.Ioo τ₁ τ₂, ∫ y, integrandPowDeriv Φ h q (averagedSlice η τ Γ') y) h := by
  have hKc : IsCompact (Metric.closedBall h (h / 2)) := isCompact_closedBall _ _
  have hKs := closedBall_subset_Ioi hh
  obtain ⟨C, hC0, hC⟩ := smoothed_package_uniform Φ hη hD hq hKc hKs
  obtain ⟨b, hb0, hb⟩ := exists_bound_powDeriv Φ hKc hKs hq (M := 1) zero_le_one
  have hhK : h ∈ Metric.closedBall h (h / 2) := Metric.mem_closedBall_self (by positivity)
  have hmeasF : ∀ s ∈ Metric.closedBall h (h / 2), AEStronglyMeasurable
      (fun τ => ∫ y, smoothedDensity Φ η s Γ' τ y ^ q) (volume.restrict (Set.Ioo τ₁ τ₂)) :=
    fun s hs => ((measurable_smoothedDensity_pow Φ hη (hKs hs)).stronglyMeasurable
      |>.integral_prod_right
      (f := fun τ y => smoothedDensity Φ η s Γ' τ y ^ q)).aestronglyMeasurable
  refine hasDerivAt_integral_const_bound (b := b)
    (F := fun s τ => ∫ y, smoothedDensity Φ η s Γ' τ y ^ q)
    (F' := fun s τ => ∫ y, integrandPowDeriv Φ s q (averagedSlice η τ Γ') y) hh hmeasF ?_ ?_ ?_ ?_
  · refine Integrable.of_bound (hmeasF h hhK) C (Filter.Eventually.of_forall fun τ => ?_)
    have := isFiniteMeasure_averagedSlice_of_datum (τ := τ) hη hD
    have hP := (hC h hhK τ).pow
    have hnn : 0 ≤ ∫ y, smoothedDensity Φ η h Γ' τ y ^ q :=
      integral_nonneg fun y => Real.rpow_nonneg (smoothDensity_nonneg Φ _ hh y) _
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact hP.2
  · exact ((measurable_integrandPowDeriv Φ hη hh).stronglyMeasurable.integral_prod_right
      (f := fun τ y => integrandPowDeriv Φ h q (averagedSlice η τ Γ') y)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun τ s hs => ?_
    have := isFiniteMeasure_averagedSlice_of_datum (τ := τ) hη hD
    exact (slice_pow Φ (averagedSlice η τ Γ') hD.lam_pos hD.lam_le
      (isAdmissibleCoefficient_of_datum hD) (hKs hs) hq (hC s hs τ)).1
  · refine Filter.Eventually.of_forall fun τ s hs => ?_
    have := isFiniteMeasure_averagedSlice_of_datum (τ := τ) hη hD
    exact hb _ (averagedSlice_real_univ_le_of_datum hη hD) s hs

theorem integrandPowBeta_nonneg {F : EvolutionAmbientState d → PDE.Mat d}
    (m : Measure (EvolutionAmbientState d)) (hh : 0 < h) [IsFiniteMeasure m]
    (y : EvolutionAmbientState d) : 0 ≤ integrandPowBeta Φ h F m q y :=
  mul_nonneg (Real.rpow_nonneg (smoothDensity_nonneg Φ m hh y) _)
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- The time-integrated identities: `F` is differentiable, with the `τ`-integral of the slice
derivative. -/
theorem hasDerivAt_totalPowBeta (hη : IsMollifier δ η) (hD : IsSmoothingDatum lam Lam Bt Γ')
    (hh : 0 < h) (hq : 1 < q) :
    Integrable (fun τ => ∫ y, integrandPowBetaDeriv Φ h
        (averagedCoefficient η Bt lam Lam τ Γ') (averagedSlice η τ Γ') q y)
      (volume.restrict (Set.Ioo τ₁ τ₂)) ∧
    HasDerivAt (fun s => ∫ τ in Set.Ioo τ₁ τ₂, ∫ y, integrandPowBeta Φ s
        (averagedCoefficient η Bt lam Lam τ Γ') (averagedSlice η τ Γ') q y)
      (∫ τ in Set.Ioo τ₁ τ₂, ∫ y, integrandPowBetaDeriv Φ h
        (averagedCoefficient η Bt lam Lam τ Γ') (averagedSlice η τ Γ') q y) h := by
  have hKc : IsCompact (Metric.closedBall h (h / 2)) := isCompact_closedBall _ _
  have hKs := closedBall_subset_Ioi hh
  obtain ⟨C, hC0, hC⟩ := smoothed_package_uniform Φ hη hD hq hKc hKs
  obtain ⟨b, hb0, hb⟩ := exists_bound_powBetaDeriv Φ hKc hKs hD.lam_pos hD.lam_le hq
    (M := 1) zero_le_one
  have hhK : h ∈ Metric.closedBall h (h / 2) := Metric.mem_closedBall_self (by positivity)
  have hmeasF : ∀ s ∈ Metric.closedBall h (h / 2), AEStronglyMeasurable
      (fun τ => ∫ y, integrandPowBeta Φ s (averagedCoefficient η Bt lam Lam τ Γ')
        (averagedSlice η τ Γ') q y) (volume.restrict (Set.Ioo τ₁ τ₂)) :=
    fun s hs => ((measurable_integrandPowBeta Φ hη hD (hKs hs) hq).stronglyMeasurable
      |>.integral_prod_right
      (f := fun τ y => integrandPowBeta Φ s (averagedCoefficient η Bt lam Lam τ Γ')
        (averagedSlice η τ Γ') q y)).aestronglyMeasurable
  refine hasDerivAt_integral_const_bound (b := b)
    (F := fun s τ => ∫ y, integrandPowBeta Φ s (averagedCoefficient η Bt lam Lam τ Γ')
      (averagedSlice η τ Γ') q y)
    (F' := fun s τ => ∫ y, integrandPowBetaDeriv Φ s (averagedCoefficient η Bt lam Lam τ Γ')
      (averagedSlice η τ Γ') q y) hh hmeasF ?_ ?_ ?_ ?_
  · refine Integrable.of_bound (hmeasF h hhK) C (Filter.Eventually.of_forall fun τ => ?_)
    have := isFiniteMeasure_averagedSlice_of_datum (τ := τ) hη hD
    have hP := (hC h hhK τ).powBeta
    have hnn : 0 ≤ ∫ y, integrandPowBeta Φ h (averagedCoefficient η Bt lam Lam τ Γ')
        (averagedSlice η τ Γ') q y :=
      integral_nonneg fun y => integrandPowBeta_nonneg Φ _ hh y
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact hP.2
  · exact ((measurable_integrandPowBetaDeriv Φ hη hD hh).stronglyMeasurable.integral_prod_right
      (f := fun τ y => integrandPowBetaDeriv Φ h (averagedCoefficient η Bt lam Lam τ Γ')
        (averagedSlice η τ Γ') q y)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun τ s hs => ?_
    have := isFiniteMeasure_averagedSlice_of_datum (τ := τ) hη hD
    exact hasDerivAt_integral_powBeta Φ (averagedSlice η τ Γ') hD.lam_pos hD.lam_le
      (isAdmissibleCoefficient_of_datum hD) (hKs hs) hq
  · refine Filter.Eventually.of_forall fun τ s hs => ?_
    have := isFiniteMeasure_averagedSlice_of_datum (τ := τ) hη hD
    exact hb _ _ (isAdmissibleCoefficient_of_datum hD)
      (averagedSlice_real_univ_le_of_datum hη hD) s hs

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

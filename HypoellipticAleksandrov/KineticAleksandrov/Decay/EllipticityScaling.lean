module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.FourierBounds

/-!
# Ellipticity normalization of the case-W decay

The source change of variables `σ̂ = λ^(1/3) σ`, `v̂ = λ^(-1/3) v`, `ẑ = z`.  This is not the
kinetic `r², r, r³` scaling.  This file proves the pointwise identities used by that
reduction: the normalized diffusion `B̂` has bounds `[1, κ]` when `B` has bounds `[λ, κλ]`,
the identity transport is unchanged, the frequency and the transported coordinate are
unchanged, and total variation is invariant under the velocity pushforward.  The identification
of the rescaled kernel by terminal-problem uniqueness is not part of this file.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

open MeasureTheory Set
open scoped ENNReal MatrixOrder

/-- The cube root `λ^(1/3)` of the ellipticity scale. -/
def lamCbrt (lam : ℝ) : ℝ := lam ^ (1 / 3 : ℝ)

theorem lamCbrt_pos {lam : ℝ} (hlam : 0 < lam) : 0 < lamCbrt lam :=
  Real.rpow_pos_of_pos hlam _

theorem lamCbrt_pow_three {lam : ℝ} (hlam : 0 ≤ lam) : lamCbrt lam ^ 3 = lam := by
  unfold lamCbrt
  rw [← Real.rpow_natCast, ← Real.rpow_mul hlam]
  norm_num

/-- The normalized diffusion `B̂(σ̂, v̂) = λ⁻¹ B(λ^(-1/3) σ̂, λ^(1/3) v̂)`. -/
def ellipticityScaledCoefficient {d : ℕ} (lam : ℝ) (B : CoefficientField d) :
    CoefficientField d :=
  fun τ y => lam⁻¹ • B ((lamCbrt lam)⁻¹ * τ) (lamCbrt lam • y)

/-- The transport after the change of variables, `b̂(v̂) = λ^(-1/3) b(λ^(1/3) v̂)`. -/
def ellipticityScaledDrift {d : ℕ} (lam : ℝ) (b : PDE.Vec d → PDE.Vec d) :
    PDE.Vec d → PDE.Vec d :=
  fun y => (lamCbrt lam)⁻¹ • b (lamCbrt lam • y)

/-- The identity transport is unchanged by the `λ^(1/3)` change of variables. -/
theorem ellipticityScaledDrift_identity {d : ℕ} {lam : ℝ} (hlam : 0 < lam) :
    ellipticityScaledDrift lam (identityDrift d) = identityDrift d := by
  funext y
  simp only [ellipticityScaledDrift, identityDrift, id_eq, smul_smul,
    inv_mul_cancel₀ (lamCbrt_pos hlam).ne', one_smul]

/-- The normalized diffusion is smooth in every entry. -/
theorem ellipticityScaledCoefficient_smooth {d : ℕ} {lam : ℝ} (B : CoefficientField d)
    (hsmooth : IsSmoothFullKineticCoefficient (zIndependentCoefficient B)) :
    IsSmoothFullKineticCoefficient
      (zIndependentCoefficient (ellipticityScaledCoefficient lam B)) := by
  intro i j
  have hcomp := (hsmooth i j).comp (by
    fun_prop : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : ℝ × (PDE.Vec d × PDE.Vec d) =>
        ((lamCbrt lam)⁻¹ * q.1, (lamCbrt lam • q.2.1, q.2.2))))
  have hmul := hcomp.const_smul lam⁻¹
  exact hmul

/-- Diffusion bounds `[λ, κλ]` become `[1, κ]` after the change of variables. -/
theorem ellipticityScaledCoefficient_sectionTwo {d : ℕ} (lam kappa : ℝ)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam (kappa * lam) B) :
    IsSectionTwoCoefficient 1 kappa (ellipticityScaledCoefficient lam B) := by
  rcases hB with ⟨hpos, hle, hsmooth, hsymm, hlower, hupper⟩
  have hinv : 0 ≤ lam⁻¹ := inv_nonneg.2 hpos.le
  have hkappa : 1 ≤ kappa := le_of_mul_le_mul_right (by linarith) hpos
  refine ⟨one_pos, hkappa, ellipticityScaledCoefficient_smooth B hsmooth, ?_, ?_, ?_⟩
  · intro τ y
    exact (hsymm _ _).smul lam⁻¹
  · intro τ y
    have h := smul_le_smul_of_nonneg_left (hlower ((lamCbrt lam)⁻¹ * τ) (lamCbrt lam • y)) hinv
    rw [smul_smul, inv_mul_cancel₀ hpos.ne'] at h
    exact h
  · intro τ y
    have h := smul_le_smul_of_nonneg_left (hupper ((lamCbrt lam)⁻¹ * τ) (lamCbrt lam • y)) hinv
    rw [smul_smul, show lam⁻¹ * (kappa * lam) = kappa by field_simp] at h
    exact h

/-- The velocity part of the pushforward, `v ↦ λ^(-1/3) v`, as a measurable equivalence. -/
def lamVelocityEquiv (d : ℕ) {lam : ℝ} (hlam : 0 < lam) : PDE.Vec d ≃ᵐ PDE.Vec d :=
  (Homeomorph.smulOfNeZero (lamCbrt lam)⁻¹ (inv_ne_zero (lamCbrt_pos hlam).ne')).toMeasurableEquiv

@[simp] theorem lamVelocityEquiv_apply (d : ℕ) {lam : ℝ} (hlam : 0 < lam) (v : PDE.Vec d) :
    lamVelocityEquiv d hlam v = (lamCbrt lam)⁻¹ • v :=
  rfl

/-- The ambient pushforward map: velocity scaled, transported coordinate unchanged. -/
def lamAmbientEquiv (d : ℕ) {lam : ℝ} (hlam : 0 < lam) :
    EvolutionAmbientState d ≃ᵐ EvolutionAmbientState d :=
  (lamVelocityEquiv d hlam).prodCongr (MeasurableEquiv.refl _)

@[simp] theorem lamAmbientEquiv_apply (d : ℕ) {lam : ℝ} (hlam : 0 < lam)
    (w : EvolutionAmbientState d) :
    lamAmbientEquiv d hlam w = ((lamCbrt lam)⁻¹ • w.1, w.2) :=
  rfl

/-- The Fourier phase depends only on the transported coordinate, which is unchanged. -/
theorem fourierPhase_lamAmbientEquiv {d : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (ξ z : PDE.Vec d) (w : EvolutionAmbientState d) :
    fourierPhase ξ z (lamAmbientEquiv d hlam w) = fourierPhase ξ z w :=
  rfl

/-- Pushforward of a complex measure by a measurable equivalence preserves total variation. -/
theorem variation_map_equiv_univ {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (ν : ComplexMeasure α) :
    (ν.map e).variation univ = ν.variation univ := by
  rw [e.measurableEmbedding.variation_map, Measure.map_apply e.measurable MeasurableSet.univ,
    preimage_univ]

/-- Real total variation of a complex measure on the velocity space. -/
def realTotalVariation {d : ℕ} (ν : ComplexMeasure (PDE.Vec d)) : ℝ :=
  (totalVariationNorm ν).toReal

/-- Velocity pushforward preserves the real total variation. -/
theorem realTotalVariation_map_lamVelocityEquiv {d : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (ν : ComplexMeasure (PDE.Vec d)) :
    realTotalVariation (ν.map (lamVelocityEquiv d hlam)) = realTotalVariation ν := by
  unfold realTotalVariation totalVariationNorm
  rw [variation_map_equiv_univ]

/-- If the rescaled master measure is the ambient pushforward of the original one, with the same
transported coordinate and frequency, the Fourier projections differ by the velocity pushforward
and have the same total variation. -/
theorem fourierProjection_lamScaled {d : ℕ} {lam : ℝ} (hlam : 0 < lam)
    {K K' : MovingFiberKernel (univ : Set (PDE.Vec d)) (fun _ => (0 : PDE.Vec d))}
    (q q' : EvolutionQuery (univ : Set (PDE.Vec d)) (fun _ => (0 : PDE.Vec d)))
    (hz : q'.1.2.2.2 = q.1.2.2.2)
    (hmaster : K'.master q' = (K.master q).map (lamAmbientEquiv d hlam))
    (ξ : PDE.Vec d) (ν ν' : ComplexMeasure (PDE.Vec d))
    (hν : IsFourierProjection K q ξ ν) (hν' : IsFourierProjection K' q' ξ ν') :
    ν' = ν.map (lamVelocityEquiv d hlam) ∧ realTotalVariation ν' = realTotalVariation ν := by
  have hmap : ν' = ν.map (lamVelocityEquiv d hlam) := by
    apply VectorMeasure.ext
    intro E hE
    rw [VectorMeasure.map_apply _ (lamVelocityEquiv d hlam).measurable hE, hν' E hE, hmaster,
      hz]
    have hpre : (lamAmbientEquiv d hlam) ⁻¹' (E ×ˢ (univ : Set (PDE.Vec d))) =
        ((lamVelocityEquiv d hlam) ⁻¹' E) ×ˢ (univ : Set (PDE.Vec d)) := by
      ext w
      simp only [mem_preimage, mem_prod, mem_univ, and_true, lamAmbientEquiv_apply,
        lamVelocityEquiv_apply]
    rw [MeasureTheory.setIntegral_map_equiv, hpre, hν _ ((lamVelocityEquiv d hlam).measurable hE)]
    rfl
  exact ⟨hmap, by rw [hmap, realTotalVariation_map_lamVelocityEquiv]⟩

/-- The rescaled time order is preserved: `σ < τ` gives `λ^(1/3) σ < λ^(1/3) τ`. -/
theorem lamCbrt_mul_lt {lam σ τ : ℝ} (hlam : 0 < lam) (h : σ < τ) :
    lamCbrt lam * σ < lamCbrt lam * τ :=
  mul_lt_mul_of_pos_left h (lamCbrt_pos hlam)

/-- Exponent bookkeeping: a unit-ellipticity decay bound on the rescaled time interval
`[λ^(1/3) σ, λ^(1/3) τ]` is the `λ^(1/3) (τ - σ) |ξ|^(2/3)` bound of the source display. -/
theorem ellipticityScaled_tv_bound {tv tv' C c lam σ τ n : ℝ} (htv : tv ≤ tv')
    (hb : tv' ≤ C * Real.exp (-c * (lamCbrt lam * τ - lamCbrt lam * σ) * n ^ (2 / 3 : ℝ))) :
    tv ≤ C * Real.exp (-c * lam ^ (1 / 3 : ℝ) * (τ - σ) * n ^ (2 / 3 : ℝ)) := by
  refine htv.trans (hb.trans (le_of_eq ?_))
  congr 2
  unfold lamCbrt
  ring

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

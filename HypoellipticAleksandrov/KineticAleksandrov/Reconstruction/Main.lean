module

public import HypoellipticAleksandrov.KineticAleksandrov.Reconstruction.FiberInversion

/-!
# Reconstruction from the marginal and the Fourier bounds

Lemma Lemma 5.2 of the kinetic Aleksandrov paper.  Let `m` be a σ-finite measure on a
measurable space `Y` (the paper takes a Borel subset of a Euclidean space; this is a special
case) and `Γ` a finite measure on `Y × ℝ^d` whose `Y`-marginal is `g dm`.  Let `1 < q < γ`,
`(q-1)/γ + 1/q₁ = 1`, `g ∈ L^{q₁}(m)`, and suppose that for every `ξ ∈ ℝ^d` the complex measure
`E ↦ ∫_{E × ℝ^d} e^{-i ξ·z} dΓ` has a density `k^ξ` with respect to `m`, such that
`𝖧 = (2π)^{-d} ∫ ‖k^ξ‖_{L^γ(m)} dξ < ∞`.  Then `Γ` has a density `G` with respect to
`m ⊗ Leb` and `∫ G^q ≤ 𝖧^{q-1} ‖g‖_{L^{q₁}(m)}`.

The statement does not need the hypothesis `k^ξ ∈ L^γ(m)` for *every* `ξ`: finiteness of `𝖧`
suffices, so the formal statement is slightly more general than the source.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set
open scoped ENNReal

namespace HypoellipticAleksandrov.KineticAleksandrov.Reconstruction

variable {Y : Type*} [MeasurableSpace Y] {d : ℕ}

/-- The final Hölder step: `∫ H^{q-1} g ≤ (∫ H^γ)^{(q-1)/γ} (∫ g^{q₁})^{1/q₁}`. -/
lemma lintegral_rpow_mul_le {m : Measure Y} {H g : Y → ℝ≥0∞} (hH : Measurable H)
    (hg : Measurable g) {q γ q₁ : ℝ} (hq : 1 < q) (hqγ : q < γ)
    (hq₁ : (q - 1) / γ + 1 / q₁ = 1) :
    ∫⁻ y, H y ^ (q - 1) * g y ∂m ≤
      (∫⁻ y, H y ^ γ ∂m) ^ ((q - 1) / γ) * (∫⁻ y, g y ^ q₁ ∂m) ^ (1 / q₁) := by
  have hq0 : 0 < q - 1 := by linarith
  have hγ0 : 0 < γ := by linarith
  set P : ℝ := γ / (q - 1) with hP
  have hP1 : 1 < P := by rw [hP, lt_div_iff₀ hq0]; linarith
  have hPinv : P⁻¹ = (q - 1) / γ := by rw [hP, inv_div]
  have hconj : P.HolderConjugate q₁ :=
    Real.holderConjugate_iff.2 ⟨hP1, by rw [hPinv, one_div] at *; exact hq₁⟩
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq m hconj (hH.pow_const (q - 1)).aemeasurable
    hg.aemeasurable
  have h2 : ∫⁻ y, (H y ^ (q - 1)) ^ P ∂m = ∫⁻ y, H y ^ γ ∂m := by
    refine lintegral_congr fun y => ?_
    rw [← ENNReal.rpow_mul, hP, mul_div_cancel₀ _ hq0.ne']
  simp only [Pi.mul_apply, h2] at h
  rwa [one_div, hPinv] at h


/-- Lemma Lemma 5.2 for a Borel-measurable density `g`. -/
theorem reconstruction_of_measurable {m : Measure Y} [SigmaFinite m]
    (Γ : Measure (Y × PDE.Vec d)) [IsFiniteMeasure Γ] {g : Y → ℝ≥0∞} (hg : Measurable g)
    (hΓ : Γ.fst = m.withDensity g) {q γ q₁ : ℝ} (hq : 1 < q) (hqγ : q < γ)
    (hq₁ : (q - 1) / γ + 1 / q₁ = 1) (hgL : eLpNorm g (ENNReal.ofReal q₁) m < ∞)
    (k : PDE.Vec d → Y → ℂ)
    (hk : ∀ ξ, Integrable (k ξ) m ∧ ∀ E, MeasurableSet E →
      ∫ y in E, k ξ y ∂m = ∫ p in E ×ˢ (univ : Set (PDE.Vec d)),
        cexp (-((PDE.vecDot ξ p.2 : ℝ) * I)) ∂Γ)
    (hH : ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) *
      ∫⁻ ξ, eLpNorm (k ξ) (ENNReal.ofReal γ) m < ∞) :
    ∃ G : Y × PDE.Vec d → ℝ≥0∞, Measurable G ∧ Γ = (m.prod volume).withDensity G ∧
      ∫⁻ p, G p ^ q ∂(m.prod volume) ≤
        (ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) *
          ∫⁻ ξ, eLpNorm (k ξ) (ENNReal.ofReal γ) m) ^ (q - 1) *
        eLpNorm g (ENNReal.ofReal q₁) m ∧
      ∫⁻ p, G p ^ q ∂(m.prod volume) < ∞ := by
  have hγ1 : 1 < γ := hq.trans hqγ
  have hγ0 : 0 < γ := by linarith
  have hq0 : 0 < q - 1 := by linarith
  have hq₁0 : 0 < q₁ := by
    by_contra hneg
    have h1 : 0 < (q - 1) / γ := by positivity
    have h2 : (q - 1) / γ < 1 := by rw [div_lt_one hγ0]; linarith
    have h3 : 1 / q₁ ≤ 0 := by rw [one_div]; exact inv_nonpos.2 (not_lt.1 hneg)
    linarith
  obtain ⟨hGm, hΓG, hfib⟩ := fiber_inversion Γ hg hΓ k hk hγ1 hq hH
  have hmink := (fiber_height_minkowski Γ hg hΓ k hk hγ1).1
  set κ := Γ.condKernel with hκ
  set H := fiberHeight g κ with hHdef
  have hHm : Measurable H := measurable_fiberHeight hg κ
  have hq1 : ∀ᵐ y ∂m, ∫⁻ z, fiberInversionDensity g κ (y, z) ^ q ≤ H y ^ (q - 1) * g y := by
    filter_upwards [hfib] with y hy using hy.2.2
  have hbound : ∫⁻ p, fiberInversionDensity g κ p ^ q ∂(m.prod volume) ≤
      (ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) *
        ∫⁻ ξ, eLpNorm (k ξ) (ENNReal.ofReal γ) m) ^ (q - 1) *
      eLpNorm g (ENNReal.ofReal q₁) m := by
   calc ∫⁻ p, fiberInversionDensity g κ p ^ q ∂(m.prod volume)
      = ∫⁻ y, ∫⁻ z, fiberInversionDensity g κ (y, z) ^ q ∂volume ∂m :=
        lintegral_prod _ (hGm.pow_const q).aemeasurable
    _ ≤ ∫⁻ y, H y ^ (q - 1) * g y ∂m := lintegral_mono_ae hq1
    _ ≤ (∫⁻ y, H y ^ γ ∂m) ^ ((q - 1) / γ) * (∫⁻ y, g y ^ q₁ ∂m) ^ (1 / q₁) :=
        lintegral_rpow_mul_le hHm hg hq hqγ hq₁
    _ ≤ _ := by
        have hp0 : ENNReal.ofReal γ ≠ 0 := by simpa using hγ0
        have hp1 : ENNReal.ofReal q₁ ≠ 0 := by simpa using hq₁0
        have hHnorm : eLpNorm H (ENNReal.ofReal γ) m = (∫⁻ y, H y ^ γ ∂m) ^ (1 / γ) := by
          rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top
            hHm.aestronglyMeasurable, ENNReal.toReal_ofReal hγ0.le]
          simp only [enorm_eq_self]
        have hgnorm : eLpNorm g (ENNReal.ofReal q₁) m = (∫⁻ y, g y ^ q₁ ∂m) ^ (1 / q₁) := by
          rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp1 ENNReal.ofReal_ne_top
            hg.aestronglyMeasurable, ENNReal.toReal_ofReal hq₁0.le]
          simp only [enorm_eq_self]
        rw [← hgnorm]
        refine mul_le_mul' ?_ le_rfl
        have : (∫⁻ y, H y ^ γ ∂m) ^ ((q - 1) / γ) = eLpNorm H (ENNReal.ofReal γ) m ^ (q - 1) := by
          rw [hHnorm, ← ENNReal.rpow_mul]
          congr 1
          field_simp
        rw [this]
        exact ENNReal.rpow_le_rpow hmink hq0.le
  exact ⟨_, hGm, hΓG, hbound, lt_of_le_of_lt hbound
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hq0.le hH.ne) hgL)⟩


/-- **Lemma Lemma 5.2** (Reconstruction from the marginal and the Fourier bounds).

Let `m` be a σ-finite measure on `Y`, `Γ` a finite measure on `Y × ℝ^d` whose `Y`-marginal is
`g dm`, `1 < q < γ`, `(q-1)/γ + 1/q₁ = 1` and `g ∈ L^{q₁}(m)`.  Suppose that for every
`ξ ∈ ℝ^d` the complex measure `E ↦ ∫_{E × ℝ^d} e^{-i ξ·z} dΓ` has the density `k ξ ∈ L^1(m)` with
respect to `m`, and that `𝖧 = (2π)^{-d} ∫ ‖k ξ‖_{L^γ(m)} dξ < ∞`.  Then `Γ` has a measurable
density `G` with respect to `m ⊗ Leb`, and `‖G‖_{L^q}^q = ∫ G^q ≤ 𝖧^{q-1} ‖g‖_{L^{q₁}(m)} < ∞`.

The paper's `Y` (a Borel subset of a Euclidean space with its Borel `σ`-algebra) is the special
case `Y = ↥S` of an arbitrary measurable space.  Here `ℝ^d` is `PDE.Vec d = Fin d → ℝ` with
product Lebesgue measure and `ξ·z = PDE.vecDot ξ z`.
The hypothesis that each `k ξ` lies in `L^γ(m)` is not needed beyond `𝖧 < ∞`. -/
theorem reconstruction {m : Measure Y} [SigmaFinite m]
    (Γ : Measure (Y × PDE.Vec d)) [IsFiniteMeasure Γ] {g : Y → ℝ≥0∞} (hgm : AEMeasurable g m)
    (hΓ : Γ.fst = m.withDensity g) {q γ q₁ : ℝ} (hq : 1 < q) (hqγ : q < γ)
    (hq₁ : (q - 1) / γ + 1 / q₁ = 1) (hgL : eLpNorm g (ENNReal.ofReal q₁) m < ∞)
    (k : PDE.Vec d → Y → ℂ)
    (hk : ∀ ξ, Integrable (k ξ) m ∧ ∀ E, MeasurableSet E →
      ∫ y in E, k ξ y ∂m = ∫ p in E ×ˢ (univ : Set (PDE.Vec d)),
        cexp (-((PDE.vecDot ξ p.2 : ℝ) * I)) ∂Γ)
    (hH : ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) *
      ∫⁻ ξ, eLpNorm (k ξ) (ENNReal.ofReal γ) m < ∞) :
    ∃ G : Y × PDE.Vec d → ℝ≥0∞, Measurable G ∧ Γ = (m.prod volume).withDensity G ∧
      ∫⁻ p, G p ^ q ∂(m.prod volume) ≤
        (ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) *
          ∫⁻ ξ, eLpNorm (k ξ) (ENNReal.ofReal γ) m) ^ (q - 1) *
        eLpNorm g (ENNReal.ofReal q₁) m ∧
      ∫⁻ p, G p ^ q ∂(m.prod volume) < ∞ := by
  have hae : g =ᵐ[m] hgm.mk g := hgm.ae_eq_mk
  have hnorm : eLpNorm g (ENNReal.ofReal q₁) m = eLpNorm (hgm.mk g) (ENNReal.ofReal q₁) m :=
    eLpNorm_congr_ae hae
  rw [hnorm] at hgL ⊢
  exact reconstruction_of_measurable Γ hgm.measurable_mk
    (hΓ.trans (withDensity_congr_ae hae)) hq hqγ hq₁ hgL k hk hH

end HypoellipticAleksandrov.KineticAleksandrov.Reconstruction

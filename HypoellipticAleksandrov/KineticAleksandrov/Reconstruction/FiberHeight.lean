module

public import HypoellipticAleksandrov.KineticAleksandrov.Reconstruction.FiberDisintegration
public import HypoellipticAleksandrov.KineticAleksandrov.Reconstruction.Minkowski

/-!
# Minkowski bound for the fibre height

Step Lemma 5.2 of the reconstruction lemma.  With the jointly
measurable representatives `k̃^ξ(y)` of `fiber_disintegration` and
`H(y) = (2π)^{-d} ∫ |k̃^ξ(y)| dξ`, Minkowski's integral inequality gives
`‖H‖_{L^γ(m)} ≤ 𝖧 = (2π)^{-d} ∫ ‖k^ξ‖_{L^γ(m)} dξ`.  If `𝖧 < ∞`, then `H(y) < ∞` for `m`-almost
every `y`, and `ξ ↦ k̃^ξ(y)` is integrable for almost every `y`.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set
open scoped ENNReal

namespace HypoellipticAleksandrov.KineticAleksandrov.Reconstruction

variable {Y : Type*} [MeasurableSpace Y] {d : ℕ}

/-- The `L^γ(m)` norm of the fibre height is the Minkowski integral of the `L^γ` norms of the
Fourier representatives, for any measurable `g` and Markov kernel `κ`. -/
lemma eLpNorm_fiberHeight_le {m : Measure Y} [SigmaFinite m] {g : Y → ℝ≥0∞}
    (hg : Measurable g) (κ : Kernel Y (PDE.Vec d)) [IsMarkovKernel κ] {γ : ℝ} (hγ : 1 < γ) :
    eLpNorm (fiberHeight g κ) (ENNReal.ofReal γ) m ≤
      ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) *
        ∫⁻ ξ, eLpNorm (fiberDensity g κ ξ) (ENNReal.ofReal γ) m := by
  have hγ0 : 0 < γ := by linarith
  have hp0 : ENNReal.ofReal γ ≠ 0 := by simpa using hγ0
  have hpT : ENNReal.ofReal γ ≠ ∞ := ENNReal.ofReal_ne_top
  set c : ℝ≥0∞ := ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) with hc
  set F : Y → PDE.Vec d → ℝ≥0∞ := fun y ξ => ‖fiberDensity g κ ξ y‖ₑ with hF
  have hFm : Measurable (Function.uncurry F) :=
    ((measurable_fiberDensity hg κ).comp measurable_swap).enorm
  have hmink := minkowski_integral (m := m) (ν := (volume : Measure (PDE.Vec d))) hγ hFm
  have hHm := measurable_fiberHeight hg κ
  have hnorm : ∀ ξ, eLpNorm (fiberDensity g κ ξ) (ENNReal.ofReal γ) m =
      (∫⁻ y, F y ξ ^ γ ∂m) ^ (1 / γ) := by
    intro ξ
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpT
      (measurable_fiberDensity_right hg κ ξ).aestronglyMeasurable, ENNReal.toReal_ofReal hγ0.le]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpT hHm.aestronglyMeasurable,
    ENNReal.toReal_ofReal hγ0.le]
  simp_rw [hnorm]
  have h1 : ∫⁻ y, ‖fiberHeight g κ y‖ₑ ^ γ ∂m =
      c ^ γ * ∫⁻ y, (∫⁻ ξ, F y ξ) ^ γ ∂m := by
    rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hγ0.le
      ENNReal.ofReal_ne_top)]
    refine lintegral_congr fun y => ?_
    rw [enorm_eq_self, fiberHeight, ENNReal.mul_rpow_of_nonneg _ _ hγ0.le]
  rw [h1, ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
    mul_one_div_cancel hγ0.ne', ENNReal.rpow_one]
  exact mul_le_mul_right hmink c


/-- A function in `L^γ` with `γ > 0` is finite almost everywhere. -/
lemma ae_lt_top_of_eLpNorm_lt_top {m : Measure Y} {H : Y → ℝ≥0∞} (hH : Measurable H) {γ : ℝ}
    (hγ : 0 < γ) (h : eLpNorm H (ENNReal.ofReal γ) m < ∞) : ∀ᵐ y ∂m, H y < ∞ := by
  have hp0 : ENNReal.ofReal γ ≠ 0 := by simpa using hγ
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 ENNReal.ofReal_ne_top
    hH.aestronglyMeasurable, ENNReal.toReal_ofReal hγ.le] at h
  have h2 := ae_lt_top (hH.enorm.pow_const γ) h.ne
  filter_upwards [h2] with y hy
  rw [enorm_eq_self] at hy
  by_contra hcon
  rw [not_lt, top_le_iff] at hcon
  rw [hcon, ENNReal.top_rpow_of_pos hγ] at hy
  exact lt_irrefl _ hy

/-- **Step Lemma 5.2.**  Under the hypotheses of
`fiber_disintegration`, Minkowski's integral inequality gives
`‖H‖_{L^γ(m)} ≤ 𝖧 = (2π)^{-d} ∫ ‖k ξ‖_{L^γ(m)} dξ`.  If `𝖧 < ∞` then `H(y) < ∞` and
`ξ ↦ k̃^ξ(y)` is integrable for `m`-almost every `y`. -/
theorem fiber_height_minkowski {m : Measure Y} [SigmaFinite m] (Γ : Measure (Y × PDE.Vec d))
    [IsFiniteMeasure Γ] {g : Y → ℝ≥0∞} (hg : Measurable g) (hΓ : Γ.fst = m.withDensity g)
    (k : PDE.Vec d → Y → ℂ)
    (hk : ∀ ξ, Integrable (k ξ) m ∧ ∀ E, MeasurableSet E →
      ∫ y in E, k ξ y ∂m = ∫ p in E ×ˢ (univ : Set (PDE.Vec d)),
        cexp (-((PDE.vecDot ξ p.2 : ℝ) * I)) ∂Γ)
    {γ : ℝ} (hγ : 1 < γ) :
    eLpNorm (fiberHeight g Γ.condKernel) (ENNReal.ofReal γ) m ≤
        ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) *
          ∫⁻ ξ, eLpNorm (k ξ) (ENNReal.ofReal γ) m ∧
      (ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) *
          ∫⁻ ξ, eLpNorm (k ξ) (ENNReal.ofReal γ) m < ∞ →
        ∀ᵐ y ∂m, fiberHeight g Γ.condKernel y < ∞ ∧
          Integrable (fun ξ => fiberDensity g Γ.condKernel ξ y)) := by
  obtain ⟨-, -, -, -, -, -, hnorm, hHm⟩ := fiber_disintegration Γ hg hΓ k hk
  have hle := eLpNorm_fiberHeight_le (m := m) hg Γ.condKernel hγ
  rw [hnorm (ENNReal.ofReal γ)] at hle
  refine ⟨hle, fun hfin => ?_⟩
  have hlt : eLpNorm (fiberHeight g Γ.condKernel) (ENNReal.ofReal γ) m < ∞ :=
    lt_of_le_of_lt hle hfin
  filter_upwards [ae_lt_top_of_eLpNorm_lt_top hHm (by linarith) hlt] with y hy
  refine ⟨hy, ⟨(continuous_const.mul (continuous_fiberFourier _ y)).aestronglyMeasurable, ?_⟩⟩
  have hc : ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) ≠ 0 := by
    have := Real.pi_pos
    simpa using (by positivity : (0 : ℝ) < ((2 * Real.pi) ^ d)⁻¹)
  have : ∫⁻ ξ, ‖fiberDensity g Γ.condKernel ξ y‖ₑ < ∞ := by
    unfold fiberHeight at hy
    rcases ENNReal.mul_lt_top_iff.1 hy with ⟨_, h⟩ | h | h
    · exact h
    · exact absurd h hc
    · rw [h]; exact ENNReal.zero_lt_top
  exact this

end HypoellipticAleksandrov.KineticAleksandrov.Reconstruction

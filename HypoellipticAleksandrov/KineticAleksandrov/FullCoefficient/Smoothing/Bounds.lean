module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Convolution
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Matrix
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Tonelli

/-!
# Positivity dichotomy, sup and mass bounds, Loewner bounds

The smoothing estimates: either `m = 0` and `r = m_h ≡ 0`, or `r > 0`
everywhere; `0 ≤ r ≤ c_{d,λ} h^{-2d} M`; `∫ r = m(ℝ^{2d}) ≤ M`; and `β = (Fm)_h / m_h` is
symmetric with `λ I ≤ β ≤ Λ I`, `|β|² ≤ d Λ²`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory
open scoped MatrixOrder

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ} {lam : ℝ} (Φ : SmoothingKernelFamily d lam) {h : ℝ}
  (m : Measure (EvolutionAmbientState d))

theorem smoothDensity_zero (y : EvolutionAmbientState d) :
    smoothDensity Φ h (0 : Measure (EvolutionAmbientState d)) y = 0 := by
  simp [smoothDensity]

variable [IsFiniteMeasure m]

theorem integrable_kernel_translate (hh : 0 < h) (y : EvolutionAmbientState d) :
    Integrable (fun a => Φ.kernel h (y - a)) m := by
  obtain ⟨C, hC⟩ := (Φ.isBoundedSmooth hh).bound_zero
  simpa using integrable_weighted_translate (Φ.isBoundedSmooth hh).contDiff.continuous
    (f := fun _ => (1 : ℝ)) measurable_const (Cf := 1) (fun _ => by simp) hC m y

omit [IsFiniteMeasure m] in
theorem smoothDensity_nonneg (hh : 0 < h) (y : EvolutionAmbientState d) :
    0 ≤ smoothDensity Φ h m y :=
  integral_nonneg fun _ => (Φ.pos hh _).le

/-- For `m ≠ 0` the smoothed density is strictly positive everywhere. -/
theorem smoothDensity_pos (hh : 0 < h) (hm : m ≠ 0) (y : EvolutionAmbientState d) :
    0 < smoothDensity Φ h m y := by
  unfold smoothDensity
  rw [integral_pos_iff_support_of_nonneg (fun a => (Φ.pos hh _).le)
    (integrable_kernel_translate Φ m hh y)]
  have : Function.support (fun a => Φ.kernel h (y - a)) = Set.univ :=
    Set.eq_univ_of_forall fun a => (Φ.pos hh _).ne'
  rw [this]
  exact Measure.measure_univ_pos.mpr hm

/-- The sup bound `0 ≤ r ≤ c_{d,λ} h^{-2d} M`. -/
theorem smoothDensity_le (hh : 0 < h) (y : EvolutionAmbientState d) :
    smoothDensity Φ h m y ≤ Φ.supConst * (h ^ (2 * d))⁻¹ * m.real Set.univ := by
  unfold smoothDensity
  calc ∫ a, Φ.kernel h (y - a) ∂m ≤ ∫ _a, Φ.supConst * (h ^ (2 * d))⁻¹ ∂m :=
        integral_mono (integrable_kernel_translate Φ m hh y) (integrable_const _)
          fun a => Φ.le_sup hh _
    _ = _ := by rw [integral_const, smul_eq_mul, mul_comm]

theorem continuous_smoothDensity (hh : 0 < h) : Continuous (smoothDensity Φ h m) := by
  rw [smoothDensity_eq]
  exact (contDiff_smoothWeighted (Cf := 1) hh measurable_const (fun _ => by simp)).continuous

/-- The `L¹` bound: `r` is integrable with `∫ r = m(ℝ^{2d})`. -/
theorem integrable_smoothDensity (hh : 0 < h) : Integrable (smoothDensity Φ h m) :=
  (integrable_smoothing_translate (Φ.integrable_kernel hh) (Φ.contDiff hh).continuous m).1

theorem integral_smoothDensity (hh : 0 < h) :
    ∫ y, smoothDensity Φ h m y = m.real Set.univ := by
  have := (integrable_smoothing_translate (Φ.integrable_kernel hh)
    (Φ.contDiff hh).continuous m).2
  rw [Φ.integral_eq_one hh, mul_one] at this
  exact this

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

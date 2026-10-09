module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Energy.Triple
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Package
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Uniform

/-!
# Integrability of `ρ^q |Dβ|²` for smoothed slices

The smoothing estimates: `r |Dβ|² ≤ 4 d² Λ² ∫ |DΦ_h|²/Φ_h(y - y') dm`,
hence `r^q |Dβ|² ≤ R^{q-1} · 4 d² Λ² C · (weight)` is integrable. This integrand is needed
(besides the ten integrands of the smoothing estimates) to integrate the coefficient term of the
energy inequality.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ} {lam Lam : ℝ} {Φ : SmoothingKernelFamily d lam} {h : ℝ}
  {F : EvolutionAmbientState d → PDE.Mat d} (m : Measure (EvolutionAmbientState d))
  [IsFiniteMeasure m] {q : ℝ}

theorem target_betaGradSq_le {C1 C2 Cfi R : ℝ} (hlam : 0 < lam)
    (hF : IsAdmissibleCoefficient lam Lam F) (hh : 0 < h) (hm : m ≠ 0)
    (hk : KernelConsts Φ h C1 C2 Cfi) (hq : 1 < q) (hR : ∀ y, smoothDensity Φ h m y ≤ R)
    (y : EvolutionAmbientState d) :
    smoothDensity Φ h m y ^ q * coefficientGradNormSq (smoothCoefficient Φ h F m) y ≤
      R ^ (q - 1) * ((4 * d ^ 2 * Lam ^ 2 * Cfi) * smoothWeight2 Φ h m y) := by
  have hr := smoothDensity_pos Φ m hh hm y
  obtain ⟨h1, h2, h3, -⟩ := rpow_density_aux hr (hR y) hq
  have hrG := density_mul_coefficientGradNormSq_le Φ m hlam hF hh hm y
  have hFi := fisherSmooth_le m hh hk y
  have hG0 := coefficientGradNormSq_nonneg (smoothCoefficient Φ h F m) y
  have hFi0 := fisherSmooth_nonneg (Φ := Φ) (h := h) m hh y
  set c : ℝ := 4 * d ^ 2 * Lam ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  calc smoothDensity Φ h m y ^ q * coefficientGradNormSq (smoothCoefficient Φ h F m) y
      = smoothDensity Φ h m y ^ (q - 1) *
          (smoothDensity Φ h m y * coefficientGradNormSq (smoothCoefficient Φ h F m) y) := by
        rw [h3]; ring
    _ ≤ R ^ (q - 1) * (c * fisherSmooth Φ h m y) :=
        mul_le_mul h1 hrG (mul_nonneg hr.le hG0) ((Real.rpow_nonneg hr.le _).trans h1)
    _ ≤ R ^ (q - 1) * ((c * Cfi) * smoothWeight2 Φ h m y) := by
        refine mul_le_mul_of_nonneg_left ?_ ((Real.rpow_nonneg hr.le _).trans h1)
        have := mul_le_mul_of_nonneg_left hFi hc0
        linarith

/-- `ρ^q |Dβ|²` is integrable for a smoothed non-zero slice, with a bound on the integral by the
mass of `m`. -/
theorem integrableBy_powBetaGradSq {C1 C2 Cfi R : ℝ} (hlam : 0 < lam)
    (hF : IsAdmissibleCoefficient lam Lam F) (hh : 0 < h) (hm : m ≠ 0)
    (hk : KernelConsts Φ h C1 C2 Cfi) (hq : 1 < q) (hR : ∀ y, smoothDensity Φ h m y ≤ R) :
    Integrable (fun y => smoothDensity Φ h m y ^ q *
      coefficientGradNormSq (smoothCoefficient Φ h F m) y) ∧
    ∫ y, smoothDensity Φ h m y ^ q * coefficientGradNormSq (smoothCoefficient Φ h F m) y ≤
      R ^ (q - 1) * (4 * d ^ 2 * Lam ^ 2 * Cfi) * (m.real Set.univ * ∫ z, weight2 Φ h z) := by
  have hr0 : ∀ y, 0 < smoothDensity Φ h m y := smoothDensity_pos Φ m hh hm
  have hβ : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun y => smoothCoefficient Φ h F m y i j) :=
    fun i j => contDiff_smoothCoefficient_entry Φ m hlam hF hh hm i j
  have hrc : Continuous (smoothDensity Φ h m) := continuous_smoothDensity Φ m hh
  have hpow : Continuous fun y => smoothDensity Φ h m y ^ q :=
    hrc.rpow_const fun y => Or.inl (hr0 y).ne'
  exact integrable_of_le_smoothWeight2 (T := fun y => smoothDensity Φ h m y ^ q *
      coefficientGradNormSq (smoothCoefficient Φ h F m) y) hh
    (hpow.mul (continuous_coefficientGradNormSq hβ))
    (fun y => mul_nonneg (Real.rpow_nonneg (hr0 y).le _) (coefficientGradNormSq_nonneg _ _))
    (A := R ^ (q - 1) * (4 * d ^ 2 * Lam ^ 2 * Cfi))
    (fun y => by
      have := target_betaGradSq_le m hlam hF hh hm hk hq hR y
      calc _ ≤ _ := this
        _ = _ := by ring)

/-- `ρ^q |Dβ|²` is integrable for a smoothed non-zero slice. -/
theorem integrable_powBetaGradSq {C1 C2 Cfi R : ℝ} (hlam : 0 < lam)
    (hF : IsAdmissibleCoefficient lam Lam F) (hh : 0 < h) (hm : m ≠ 0)
    (hk : KernelConsts Φ h C1 C2 Cfi) (hq : 1 < q) (hR : ∀ y, smoothDensity Φ h m y ≤ R) :
    Integrable fun y => smoothDensity Φ h m y ^ q *
      coefficientGradNormSq (smoothCoefficient Φ h F m) y :=
  (integrableBy_powBetaGradSq m hlam hF hh hm hk hq hR).1

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

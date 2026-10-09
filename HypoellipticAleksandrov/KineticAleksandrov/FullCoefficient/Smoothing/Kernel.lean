module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Coordinates

/-!
# Abstract smoothing kernel families

`SmoothingKernelFamily d lam` packages exactly the properties of the Gaussian flow kernel
`Φ_h` that the smoothing estimates use:
positivity, smoothness in the phase variable, unit mass, the sup bound, the heat equation in `h`
with generator `(lam/2) (2 h² Δ_z - 2 h ∇_z·∇_v + Δ_v)`, and the derivative, moment and
integrability bounds of the Gaussian flow, locally uniformly in `h` on compact subsets of `(0,∞)`.
Every smoothing estimate is then proved for an arbitrary such family.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

/-- The generator `M^h : D²F = (lam/2) (2 h² Δ_z F - 2 h ∇_z·∇_v F + Δ_v F)` of the flow. -/
def heatOperator (lam h : ℝ) (F : EvolutionAmbientState d → ℝ) (y : EvolutionAmbientState d) :
    ℝ :=
  lam / 2 * (2 * h ^ 2 * positionLaplacian F y - 2 * h * mixedDivergence F y +
    velocityLaplacian F y)

/-- An abstract family of smoothing kernels `Φ_h` on phase space, with the properties of
the Gaussian flow used by the smoothing estimates. -/
structure SmoothingKernelFamily (d : ℕ) (lam : ℝ) where
  /-- The kernel `Φ_h(y)`. -/
  kernel : ℝ → EvolutionAmbientState d → ℝ
  /-- The constant `c_{d,λ}` with `Φ_h ≤ c_{d,λ} h^{-2d}`. -/
  supConst : ℝ
  pos : ∀ {h : ℝ}, 0 < h → ∀ y, 0 < kernel h y
  contDiff : ∀ {h : ℝ}, 0 < h → ContDiff ℝ (⊤ : ℕ∞) (kernel h)
  integral_eq_one : ∀ {h : ℝ}, 0 < h → ∫ y, kernel h y = 1
  le_sup : ∀ {h : ℝ}, 0 < h → ∀ y, kernel h y ≤ supConst * (h ^ (2 * d))⁻¹
  hasDerivAt_heat : ∀ {h : ℝ}, 0 < h → ∀ y,
    HasDerivAt (fun s => kernel s y) (heatOperator lam h (kernel h) y) h
  deriv_bound : ∀ (k : ℕ) {K : Set ℝ}, IsCompact K → K ⊆ Set.Ioi 0 →
    ∃ C : ℝ, ∀ h ∈ K, ∀ y, ‖iteratedFDeriv ℝ k (kernel h) y‖ ≤ C * (1 + ‖y‖) ^ k * kernel h y
  weight_le : ∀ (k : ℕ) {K : Set ℝ}, IsCompact K → K ⊆ Set.Ioi 0 →
    ∃ C : ℝ, ∀ h ∈ K, ∀ y, (1 + ‖y‖) ^ k * kernel h y ≤ C
  weight_integrable : ∀ (k : ℕ) {h : ℝ}, 0 < h →
    Integrable (fun y => (1 + ‖y‖) ^ k * kernel h y)
  weight_integral_le : ∀ (k : ℕ) {K : Set ℝ}, IsCompact K → K ⊆ Set.Ioi 0 →
    ∃ C : ℝ, ∀ h ∈ K, ∫ y, (1 + ‖y‖) ^ k * kernel h y ≤ C
  /-- Joint continuity of `(h, y) ↦ Φ_h(y)` on `(0, ∞) × ℝ^{2d}`. -/
  joint : ContinuousOn (fun p : ℝ × EvolutionAmbientState d => kernel p.1 p.2)
    (Set.Ioi 0 ×ˢ Set.univ)
  /-- A single bounded continuous integrable function dominating the weighted kernels
  `(1 + ‖y‖)^k Φ_h`, uniformly for `h` in a compact subset of `(0, ∞)`. -/
  weight_dom : ∀ (k : ℕ) {K : Set ℝ}, IsCompact K → K ⊆ Set.Ioi 0 →
    ∃ (G : EvolutionAmbientState d → ℝ) (B : ℝ), Continuous G ∧ Integrable G ∧
      (∀ z, 0 ≤ G z ∧ G z ≤ B) ∧ ∀ h ∈ K, ∀ z, (1 + ‖z‖) ^ k * kernel h z ≤ G z

namespace SmoothingKernelFamily

variable {lam : ℝ} (Φ : SmoothingKernelFamily d lam)

theorem integrable_kernel {h : ℝ} (hh : 0 < h) : Integrable (Φ.kernel h) := by
  simpa using Φ.weight_integrable 0 hh

theorem measurable_kernel {h : ℝ} (hh : 0 < h) : Measurable (Φ.kernel h) :=
  (Φ.contDiff hh).continuous.measurable

theorem isBoundedSmooth {h : ℝ} (hh : 0 < h) : IsBoundedSmooth (Φ.kernel h) := by
  refine ⟨Φ.contDiff hh, fun k => ?_⟩
  have hK : IsCompact ({h} : Set ℝ) := isCompact_singleton
  have hsub : ({h} : Set ℝ) ⊆ Set.Ioi 0 := by simpa using hh
  obtain ⟨C, hC⟩ := Φ.deriv_bound k hK hsub
  obtain ⟨W, hW⟩ := Φ.weight_le k hK hsub
  refine ⟨|C| * W, fun x => ?_⟩
  have h1 := hC h rfl x
  have h2 := hW h rfl x
  have hp := Φ.pos hh x
  calc ‖iteratedFDeriv ℝ k (Φ.kernel h) x‖ ≤ C * (1 + ‖x‖) ^ k * Φ.kernel h x := h1
    _ ≤ |C| * ((1 + ‖x‖) ^ k * Φ.kernel h x) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * W := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)

/-- The sup constant is positive. -/
theorem supConst_pos : 0 < Φ.supConst := by
  have h := Φ.le_sup one_pos (0 : EvolutionAmbientState d)
  have hp := Φ.pos one_pos (0 : EvolutionAmbientState d)
  simp only [one_pow, inv_one, mul_one] at h
  exact hp.trans_le h

/-- A compact subset of `(0, ∞)` is bounded below by a positive number. -/
theorem exists_pos_le_of_isCompact {K : Set ℝ} (hK : IsCompact K) (hsub : K ⊆ Set.Ioi 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h ∈ K, δ ≤ h := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  · obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne continuous_id.continuousOn
    exact ⟨x, hsub hx, fun h hh => hmin hh⟩

/-- The uniform sup bound of the kernel on a compact subset of `(0, ∞)`. -/
theorem exists_sup_bound {K : Set ℝ} (hK : IsCompact K) (hsub : K ⊆ Set.Ioi 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h ∈ K, ∀ y, Φ.kernel h y ≤ C := by
  obtain ⟨δ, hδ, hle⟩ := exists_pos_le_of_isCompact hK hsub
  refine ⟨Φ.supConst * (δ ^ (2 * d))⁻¹, by have := Φ.supConst_pos; positivity, ?_⟩
  intro h hh y
  have hh0 : 0 < h := hsub hh
  refine (Φ.le_sup hh0 y).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ Φ.supConst_pos.le
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hδ.le (hle h hh) _)

end SmoothingKernelFamily

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

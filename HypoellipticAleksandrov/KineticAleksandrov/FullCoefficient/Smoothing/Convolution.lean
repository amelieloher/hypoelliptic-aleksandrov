module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Defs
public import HypoellipticAleksandrov.LinearAlgebra.LoewnerEntryBound

/-!
# Weighted smoothing of finite measures: differentiation in the phase variable

For a bounded measurable weight `f` and a finite measure `m` on phase space, the weighted
smoothing `y ↦ ∫ Φ_h(y - y') f(y') ∂m(y')` is smooth, and coordinate partial derivatives are taken
under the integral sign.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

theorem IsBoundedSmooth.coordPartial {G : EvolutionAmbientState d → ℝ} (hG : IsBoundedSmooth G)
    (c : Fin d ⊕ Fin d) : IsBoundedSmooth (coordPartial c G) :=
  hG.fderiv.apply_const (coordDir c)

theorem coordPartial_wconv {G : EvolutionAmbientState d → ℝ} (hG : IsBoundedSmooth G)
    {f : EvolutionAmbientState d → ℝ} (hf : Measurable f) {Cf : ℝ} (hfb : ∀ a, |f a| ≤ Cf)
    (m : Measure (EvolutionAmbientState d)) [IsFiniteMeasure m] (c : Fin d ⊕ Fin d) :
    coordPartial c (wconv G f m) = wconv (coordPartial c G) f m := by
  funext y
  have hG' := hG.fderiv
  obtain ⟨C0, hC0⟩ := hG'.bound_zero
  have hint := integrable_weighted_translate hG'.contDiff.continuous hf hfb hC0 m y
  unfold coordPartial
  rw [fderiv_wconv hG hf hfb m]
  unfold wconv
  rw [ContinuousLinearMap.integral_apply hint]
  rfl

variable {lam : ℝ} (Φ : SmoothingKernelFamily d lam)

/-- The `f`-weighted smoothing `y ↦ ∫ Φ_h(y - y') f(y') dm(y')`. -/
def smoothWeighted (h : ℝ) (f : EvolutionAmbientState d → ℝ)
    (m : Measure (EvolutionAmbientState d)) : EvolutionAmbientState d → ℝ :=
  wconv (Φ.kernel h) f m

theorem smoothDensity_eq (h : ℝ) (m : Measure (EvolutionAmbientState d)) :
    smoothDensity Φ h m = smoothWeighted Φ h (fun _ => 1) m := by
  funext y; simp [smoothDensity, smoothWeighted, wconv]

theorem smoothFluxEntry_eq (h : ℝ) (F : EvolutionAmbientState d → PDE.Mat d)
    (m : Measure (EvolutionAmbientState d)) (i j : Fin d) :
    smoothFluxEntry Φ h F m i j = smoothWeighted Φ h (fun a => F a i j) m := by
  funext y
  simp only [smoothFluxEntry, smoothWeighted, wconv, smul_eq_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun a => mul_comm _ _)

variable {Φ} {h : ℝ} {f : EvolutionAmbientState d → ℝ} {Cf : ℝ}
  {m : Measure (EvolutionAmbientState d)} [IsFiniteMeasure m]

theorem contDiff_smoothWeighted (hh : 0 < h) (hf : Measurable f) (hfb : ∀ a, |f a| ≤ Cf) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothWeighted Φ h f m) :=
  contDiff_wconv (Φ.isBoundedSmooth hh) hf hfb m

theorem coordPartial_smoothWeighted (hh : 0 < h) (hf : Measurable f) (hfb : ∀ a, |f a| ≤ Cf)
    (c : Fin d ⊕ Fin d) :
    coordPartial c (smoothWeighted Φ h f m) = wconv (coordPartial c (Φ.kernel h)) f m :=
  coordPartial_wconv (Φ.isBoundedSmooth hh) hf hfb m c

theorem coordPartial₂_smoothWeighted (hh : 0 < h) (hf : Measurable f)
    (hfb : ∀ a, |f a| ≤ Cf) (c c' : Fin d ⊕ Fin d) :
    coordPartial c' (coordPartial c (smoothWeighted Φ h f m)) =
      wconv (coordPartial c' (coordPartial c (Φ.kernel h))) f m := by
  rw [coordPartial_smoothWeighted hh hf hfb c]
  exact coordPartial_wconv ((Φ.isBoundedSmooth hh).coordPartial c) hf hfb m c'

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Absorb.FlowLIntegral
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Absorb.HeatUniform
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Main
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Energy.Family

/-!
# The slice identity for `∫ r_h^q`

The time-integrated identities for one slice measure `m`: the function
`h ↦ ∫ r_h^q dy` is differentiable with derivative `-q(q-1) ∫ r^{q-2} |Dr|²_{M^h}`.
This is the power identity (`power_identity`) integrated in `y`, the term `M^h : D²(r^q)`
integrating to
zero because `r^q ∈ W^{2,1}` (the smoothing estimates).
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ} {lam Lam : ℝ} (Φ : SmoothingKernelFamily d lam) {h q : ℝ}
  (m : Measure (EvolutionAmbientState d)) [IsFiniteMeasure m]

/-- The `h`-derivative integrand `q r^{q-1} (M^h : D² r)` of `r^q`. -/
def integrandPowDeriv (Φ : SmoothingKernelFamily d lam) (h q : ℝ)
    (m : Measure (EvolutionAmbientState d)) (y : EvolutionAmbientState d) : ℝ :=
  q * smoothDensity Φ h m y ^ (q - 1) * heatOperator lam h (smoothDensity Φ h m) y

theorem integrandPowDeriv_eq (hh : 0 < h) (hm : m ≠ 0) (y : EvolutionAmbientState d) :
    integrandPowDeriv Φ h q m y =
      flowL lam h (fun y => smoothDensity Φ h m y ^ q) y -
        q * (q - 1) * (smoothDensity Φ h m y ^ (q - 2) *
          flowGamma lam h (smoothDensity Φ h m) (smoothDensity Φ h m) y) := by
  have hpos : ∀ y', 0 < smoothDensity Φ h m y' := smoothDensity_pos Φ m hh hm
  have hr2 : ContDiff ℝ 2 (smoothDensity Φ h m) :=
    (contDiff_smoothDensity Φ m hh).of_le (by simp)
  have ht : HasDerivAt (fun s => smoothDensity Φ s m y)
      (flowL lam h (smoothDensity Φ h m) y) h := hasDerivAt_smoothDensity Φ m hh y
  have hpi := power_identity lam h q (fun s y => smoothDensity Φ s m y) hr2 hpos y ht
  have hT := ht.rpow_const (p := q) (Or.inl (hpos y).ne')
  have hd : deriv (fun s => smoothDensity Φ s m y ^ q) h =
      flowL lam h (smoothDensity Φ h m) y * q * smoothDensity Φ h m y ^ (q - 1) := hT.deriv
  rw [hd] at hpi
  unfold integrandPowDeriv
  rw [flowL_eq_heatOperator] at hpi ⊢
  simp only [flowL_eq_heatOperator] at hpi
  linarith

theorem continuous_integrandPowDeriv (hh : 0 < h) (hm : m ≠ 0) :
    Continuous (integrandPowDeriv Φ h q m) := by
  unfold integrandPowDeriv
  exact (continuous_const.mul ((continuous_smoothDensity Φ m hh).rpow_const fun y =>
    Or.inl (smoothDensity_pos Φ m hh hm y).ne')).mul
      (continuous_heatOperator (contDiff_smoothDensity Φ m hh) lam h)

theorem integrable_integrandPowDeriv (hh : 0 < h) (hm : m ≠ 0) (hq : 1 < q) :
    Integrable (integrandPowDeriv Φ h q m) := by
  have hKc : IsCompact ({h} : Set ℝ) := isCompact_singleton
  have hKs : ({h} : Set ℝ) ⊆ Set.Ioi 0 := by simpa using hh
  obtain ⟨D, A, R, hDi, hD0, hA0, hR0, hdom⟩ := exists_heat_dominator Φ hKc hKs m
  refine Integrable.mono' ((hDi.const_mul A).const_mul (q * R ^ (q - 1)))
    (continuous_integrandPowDeriv Φ m hh hm).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  exact abs_density_deriv_le Φ m hm hq hKs hR0 hdom (Set.mem_singleton h) y

/-- The time-integrated identities, first identity, for one slice: `h ↦ ∫ r_h^q` has derivative
`-q(q-1) ∫ r^{q-2} |Dr|²_{M^h}`, and the integrand of the latter is integrable. -/
theorem slice_pow {F : EvolutionAmbientState d → PDE.Mat d} {C : ℝ} (hlam : 0 < lam)
    (hLam' : lam ≤ Lam) (hF : IsAdmissibleCoefficient lam Lam F) (hh : 0 < h) (hq : 1 < q)
    (hP : PackageIntegrable Φ h F m q C) :
    HasDerivAt (fun s => ∫ y, smoothDensity Φ s m y ^ q)
      (∫ y, integrandPowDeriv Φ h q m y) h ∧
    Integrable (fun y => smoothDensity Φ h m y ^ (q - 2) *
      flowGamma lam h (smoothDensity Φ h m) (smoothDensity Φ h m) y) ∧
    ∫ y, integrandPowDeriv Φ h q m y = -(q * (q - 1)) * ∫ y, smoothDensity Φ h m y ^ (q - 2) *
      flowGamma lam h (smoothDensity Φ h m) (smoothDensity Φ h m) y := by
  by_cases hm : m = 0
  · subst hm
    have hr0 : smoothDensity Φ h (0 : Measure (EvolutionAmbientState d)) = fun _ => 0 :=
      funext fun y => smoothDensity_zero Φ y
    have hz : ∀ y, smoothDensity Φ h (0 : Measure (EvolutionAmbientState d)) y ^ (q - 2) *
        flowGamma lam h (smoothDensity Φ h (0 : Measure (EvolutionAmbientState d)))
          (smoothDensity Φ h (0 : Measure (EvolutionAmbientState d))) y = 0 := fun y => by
      rw [hr0]; simp [flowGamma_zero]
    have e1 : (fun s => ∫ y : EvolutionAmbientState d,
        smoothDensity Φ s (0 : Measure (EvolutionAmbientState d)) y ^ q) = fun _ => 0 := by
      funext s; simp [smoothDensity_zero, Real.zero_rpow (by linarith : q ≠ 0)]
    have e2 : ∀ y : EvolutionAmbientState d,
        integrandPowDeriv Φ h q (0 : Measure (EvolutionAmbientState d)) y = 0 := fun y => by
      simp [integrandPowDeriv, smoothDensity_zero, Real.zero_rpow (by linarith : q - 1 ≠ 0)]
    simp only [hz, e2, integral_zero, mul_zero, e1]
    exact ⟨hasDerivAt_const h 0, integrable_zero _ _ _, trivial⟩
  · have hder := hasDerivAt_integral_rpow_density Φ m hh hq
    have hW := (smoothW21_of_packageIntegrable hlam hLam' hq hF hh hP).1
    have hWf : SmoothW21 (fun y => smoothDensity Φ h m y ^ q) := hW
    have hX := integrable_integrandPowDeriv Φ m hh hm hq
    have hL := hWf.integrable_flowL lam h
    have hq1 : q - 1 ≠ 0 := (by linarith : (0 : ℝ) < q - 1).ne'
    have hq0 : q * (q - 1) ≠ 0 := mul_ne_zero (by linarith) hq1
    have hZ : Integrable (fun y => smoothDensity Φ h m y ^ (q - 2) *
        flowGamma lam h (smoothDensity Φ h m) (smoothDensity Φ h m) y) := by
      have h1 : Integrable (fun y => (q * (q - 1))⁻¹ *
          (flowL lam h (fun y => smoothDensity Φ h m y ^ q) y -
            integrandPowDeriv Φ h q m y)) := (hL.sub hX).const_mul _
      refine h1.congr (Filter.Eventually.of_forall fun y => ?_)
      simp only [integrandPowDeriv_eq Φ m hh hm]
      rw [sub_sub_cancel]
      field_simp
    refine ⟨hder, hZ, ?_⟩
    have hcalc : (fun y => integrandPowDeriv Φ h q m y) = fun y =>
        flowL lam h (fun y => smoothDensity Φ h m y ^ q) y -
          q * (q - 1) * (smoothDensity Φ h m y ^ (q - 2) *
            flowGamma lam h (smoothDensity Φ h m) (smoothDensity Φ h m) y) :=
      funext fun y => integrandPowDeriv_eq Φ m hh hm y
    rw [hcalc, integral_sub hL (hZ.const_mul _), integral_const_mul, hWf.integral_flowL]
    ring

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Absorb.SliceUniform
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Absorb.JointPartial
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothed.Smooth
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothed.SlicePackage

/-!
# Measurability in the slice time of the slice integrals

For a smoothing datum, the slice integrals of `r^q`, `q r^{q-1} (M^h : D² r)`, `r^q |β|²` and of
the `h`-derivative of `r^q |β|²` are measurable functions of the slice time `τ`, being integrals in
`y` of jointly measurable functions of `(τ, y)` (`ρ` and the flux entries `J` are jointly smooth).
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ} {δ : ℝ} {η : ℝ → ℝ} {lam Lam : ℝ} (Φ : SmoothingKernelFamily d lam)
  {Bt : ℝ → EvolutionAmbientState d → PDE.Mat d}
  {Γ' : Measure (ℝ × EvolutionAmbientState d)} [IsFiniteMeasure Γ']
  {h q : ℝ}

theorem contDiff_smoothedFlux_of_datum (hη : IsMollifier δ η)
    (hD : IsSmoothingDatum lam Lam Bt Γ') (hh : 0 < h) (i j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × EvolutionAmbientState d =>
      smoothedFlux Φ η Bt Lam h Γ' p.1 p.2 i j) := by
  exact contDiff_smoothedFlux Φ hη hD.marginal hD.measurable hD.abs_apply_le hD.lam_nonneg_Lam
    hD.loewner hh i j

theorem integrandPowBeta_eq_sum_all {F : EvolutionAmbientState d → PDE.Mat d}
    (m : Measure (EvolutionAmbientState d)) [IsFiniteMeasure m] (hh : 0 < h) (hq : 1 < q) :
    integrandPowBeta Φ h F m q = fun y => ∑ i, ∑ j,
      smoothDensity Φ h m y ^ (q - 2) * smoothFluxEntry Φ h F m i j y ^ 2 := by
  by_cases hm : m = 0
  · subst hm
    funext y
    simp [integrandPowBeta, smoothDensity_zero, smoothFluxEntry,
      Real.zero_rpow (by linarith : q ≠ 0)]
  · exact integrandPowBeta_eq_sum Φ m hh hm

theorem measurable_smoothedDensity_pow (hη : IsMollifier δ η) (hh : 0 < h) :
    Measurable fun p : ℝ × EvolutionAmbientState d =>
      smoothedDensity Φ η h Γ' p.1 p.2 ^ q :=
  (contDiff_smoothedDensity Φ (Γ' := Γ') hη hh).continuous.measurable.pow_const _

theorem measurable_integrandPowDeriv (hη : IsMollifier δ η) (hh : 0 < h) :
    Measurable fun p : ℝ × EvolutionAmbientState d =>
      integrandPowDeriv Φ h q (averagedSlice η p.1 Γ') p.2 := by
  have hρ := (contDiff_smoothedDensity Φ (Γ' := Γ') hη hh).continuous.measurable
  have hL := (continuous_heatOperator_slice (lam := lam) (h := h)
    (contDiff_smoothedDensity Φ (Γ' := Γ') hη hh)).measurable
  exact (measurable_const.mul (hρ.pow_const _)).mul hL

theorem measurable_integrandPowBeta (hη : IsMollifier δ η)
    (hD : IsSmoothingDatum lam Lam Bt Γ') (hh : 0 < h) (hq : 1 < q) :
    Measurable fun p : ℝ × EvolutionAmbientState d =>
      integrandPowBeta Φ h (averagedCoefficient η Bt lam Lam p.1 Γ')
        (averagedSlice η p.1 Γ') q p.2 := by
  have : (fun p : ℝ × EvolutionAmbientState d => integrandPowBeta Φ h
      (averagedCoefficient η Bt lam Lam p.1 Γ') (averagedSlice η p.1 Γ') q p.2) =
      fun p => ∑ i, ∑ j, smoothedDensity Φ η h Γ' p.1 p.2 ^ (q - 2) *
        smoothedFlux Φ η Bt Lam h Γ' p.1 p.2 i j ^ 2 := by
    funext p
    have : IsFiniteMeasure (averagedSlice η p.1 Γ') :=
      isFiniteMeasure_averagedSlice_of_datum hη hD
    have := integrandPowBeta_eq_sum_all Φ (F := averagedCoefficient η Bt lam Lam p.1 Γ')
      (averagedSlice η p.1 Γ') (q := q) hh hq
    have h2 := congrFun this p.2
    exact h2
  rw [this]
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  have hρ := (contDiff_smoothedDensity Φ (Γ' := Γ') hη hh).continuous.measurable
  have hJ := (contDiff_smoothedFlux_of_datum Φ hη hD hh i j).continuous.measurable
  exact (hρ.pow_const _).mul (hJ.pow_const 2)

theorem measurable_integrandPowBetaDeriv (hη : IsMollifier δ η)
    (hD : IsSmoothingDatum lam Lam Bt Γ') (hh : 0 < h) :
    Measurable fun p : ℝ × EvolutionAmbientState d =>
      integrandPowBetaDeriv Φ h (averagedCoefficient η Bt lam Lam p.1 Γ')
        (averagedSlice η p.1 Γ') q p.2 := by
  unfold integrandPowBetaDeriv
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  have hρ := (contDiff_smoothedDensity Φ (Γ' := Γ') hη hh).continuous.measurable
  have hJc := contDiff_smoothedFlux_of_datum Φ hη hD hh i j
  have hJ := hJc.continuous.measurable
  have hL := (continuous_heatOperator_slice (lam := lam) (h := h)
    (contDiff_smoothedDensity Φ (Γ' := Γ') hη hh)).measurable
  have hLJ := (continuous_heatOperator_slice (lam := lam) (h := h)
    (g := fun τ y => smoothedFlux Φ η Bt Lam h Γ' τ y i j) hJc).measurable
  exact (((measurable_const.mul (hρ.pow_const _)).mul hL).mul (hJ.pow_const 2)).add
    ((hρ.pow_const _).mul ((measurable_const.mul hJ).mul hLJ))

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

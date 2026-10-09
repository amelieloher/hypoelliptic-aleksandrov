module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Absorb.SlicePower
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Energy.Pointwise

/-!
# The slice inequality for `∫ r_h^q |β_h|²`

The time-integrated identities, second inequality, for one slice measure:
`h ↦ ∫ r_h^q |β_h|²` has derivative `G` with `∫ r^q |Dβ|²_{M^h} ≤ -G`. This is the coefficient
identity
(`coef_inequality`, summed over the `d²` entries) integrated in `y`, the terms
`M^h : D²(r^{q-2} J²)`
integrating to zero because each `r^{q-2} J_{ij}²` is `W^{2,1}` (the smoothing estimates).
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ} {lam Lam : ℝ} (Φ : SmoothingKernelFamily d lam) {h q : ℝ}
  (m : Measure (EvolutionAmbientState d)) [IsFiniteMeasure m]
  {F : EvolutionAmbientState d → PDE.Mat d}

/-- The `h`-derivative integrand of `r^q |β|² = ∑ᵢⱼ r^{q-2} Jᵢⱼ²`. -/
def integrandPowBetaDeriv (Φ : SmoothingKernelFamily d lam) (h : ℝ)
    (F : EvolutionAmbientState d → PDE.Mat d) (m : Measure (EvolutionAmbientState d)) (q : ℝ)
    (y : EvolutionAmbientState d) : ℝ :=
  ∑ i, ∑ j, ((q - 2) * smoothDensity Φ h m y ^ (q - 3) *
    heatOperator lam h (smoothDensity Φ h m) y * smoothFluxEntry Φ h F m i j y ^ 2 +
    smoothDensity Φ h m y ^ (q - 2) * (2 * smoothFluxEntry Φ h F m i j y *
      heatOperator lam h (smoothFluxEntry Φ h F m i j) y))

theorem continuous_flowGamma {F G : EvolutionAmbientState d → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (lam h : ℝ) :
    Continuous (flowGamma lam h F G) := by
  have hp : ∀ i, Continuous (positionPartial i F) := fun i => continuous_coordPartial hF (Sum.inr i)
  have hv : ∀ i, Continuous (velocityPartial i F) := fun i => continuous_coordPartial hF (Sum.inl i)
  have hp' : ∀ i, Continuous (positionPartial i G) := fun i =>
    continuous_coordPartial hG (Sum.inr i)
  have hv' : ∀ i, Continuous (velocityPartial i G) := fun i =>
    continuous_coordPartial hG (Sum.inl i)
  unfold flowGamma gradZZ gradZV gradVV
  fun_prop

theorem rpow_mul_div_sq {r J : ℝ} (hr : 0 < r) (q : ℝ) :
    r ^ q * (J / r) ^ 2 = r ^ (q - 2) * J ^ 2 := by
  rw [Real.rpow_sub hr, Real.rpow_two]
  field_simp

theorem hasDerivAt_powBeta_entry (hlam : 0 < lam)
    (hF : IsAdmissibleCoefficient lam Lam F) (hh : 0 < h) (hm : m ≠ 0) (i j : Fin d)
    (y : EvolutionAmbientState d) :
    HasDerivAt (fun s => smoothDensity Φ s m y ^ (q - 2) * smoothFluxEntry Φ s F m i j y ^ 2)
      ((q - 2) * smoothDensity Φ h m y ^ (q - 3) *
        heatOperator lam h (smoothDensity Φ h m) y * smoothFluxEntry Φ h F m i j y ^ 2 +
        smoothDensity Φ h m y ^ (q - 2) * (2 * smoothFluxEntry Φ h F m i j y *
          heatOperator lam h (smoothFluxEntry Φ h F m i j) y)) h := by
  have hr := smoothDensity_pos Φ m hh hm y
  have h1 := (hasDerivAt_smoothDensity Φ m hh y).rpow_const (p := q - 2) (Or.inl hr.ne')
  have h2 := (hasDerivAt_smoothFluxEntry Φ m hlam hF hh i j y).pow 2
  have h3 := h1.mul h2
  have e : q - 2 - 1 = q - 3 := by ring
  rw [e] at h3
  convert h3 using 1
  simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  ring

/-- Pointwise the coefficient identity, summed over the entries. -/
theorem powBeta_pointwise (hlam : 0 < lam)
    (hF : IsAdmissibleCoefficient lam Lam F) (hh : 0 < h) (hm : m ≠ 0) (hq1 : 1 < q)
    (hq2 : q ≤ 4 / 3) (y : EvolutionAmbientState d) :
    smoothDensity Φ h m y ^ q * coefficientGammaSum lam h (smoothCoefficient Φ h F m) y ≤
      -(integrandPowBetaDeriv Φ h F m q y - ∑ i, ∑ j, flowL lam h (fun y' =>
        smoothDensity Φ h m y' ^ (q - 2) * smoothFluxEntry Φ h F m i j y' ^ 2) y) := by
  have hpos : ∀ y', 0 < smoothDensity Φ h m y' := smoothDensity_pos Φ m hh hm
  have hr2 : ContDiff ℝ 2 (smoothDensity Φ h m) :=
    (contDiff_smoothDensity Φ m hh).of_le (by simp)
  have hentry : ∀ i j : Fin d, smoothDensity Φ h m y ^ q *
      flowGamma lam h (fun y' => smoothCoefficient Φ h F m y' i j)
        (fun y' => smoothCoefficient Φ h F m y' i j) y ≤
      -((q - 2) * smoothDensity Φ h m y ^ (q - 3) *
        heatOperator lam h (smoothDensity Φ h m) y * smoothFluxEntry Φ h F m i j y ^ 2 +
        smoothDensity Φ h m y ^ (q - 2) * (2 * smoothFluxEntry Φ h F m i j y *
          heatOperator lam h (smoothFluxEntry Φ h F m i j) y) -
        flowL lam h (fun y' => smoothDensity Φ h m y' ^ (q - 2) *
          smoothFluxEntry Φ h F m i j y' ^ 2) y) := by
    intro i j
    have hj2 : ContDiff ℝ 2 (smoothFluxEntry Φ h F m i j) :=
      (contDiff_smoothFluxEntry Φ m hlam hF hh i j).of_le (by simp)
    have htr : HasDerivAt (fun s => smoothDensity Φ s m y)
        (flowL lam h (smoothDensity Φ h m) y) h := hasDerivAt_smoothDensity Φ m hh y
    have htj : HasDerivAt (fun s => smoothFluxEntry Φ s F m i j y)
        (flowL lam h (smoothFluxEntry Φ h F m i j) y) h :=
      hasDerivAt_smoothFluxEntry Φ m hlam hF hh i j y
    have hci := coef_inequality hlam h q hq1 hq2 (fun s y => smoothDensity Φ s m y)
      (fun s y => smoothFluxEntry Φ s F m i j y) hr2 hj2 hpos y htr htj
    have hβ : (fun y' => smoothFluxEntry Φ h F m i j y' / smoothDensity Φ h m y') =
        fun y' => smoothCoefficient Φ h F m y' i j := by
      funext y'
      rw [smoothFluxEntry_eq_mul Φ m hh hm i j y']
      exact mul_div_cancel_left₀ _ (hpos y').ne'
    have hg : (fun y' => smoothDensity Φ h m y' ^ q *
        (smoothFluxEntry Φ h F m i j y' / smoothDensity Φ h m y') ^ 2) =
        fun y' => smoothDensity Φ h m y' ^ (q - 2) * smoothFluxEntry Φ h F m i j y' ^ 2 :=
      funext fun y' => rpow_mul_div_sq (hpos y') q
    have hev : (fun s => smoothDensity Φ s m y ^ q *
        (smoothFluxEntry Φ s F m i j y / smoothDensity Φ s m y) ^ 2) =ᶠ[nhds h]
        fun s => smoothDensity Φ s m y ^ (q - 2) * smoothFluxEntry Φ s F m i j y ^ 2 := by
      filter_upwards [Ioi_mem_nhds hh] with s hs
      exact rpow_mul_div_sq (smoothDensity_pos Φ m hs hm y) q
    have hd := (hasDerivAt_powBeta_entry Φ m hlam hF hh hm (q := q) i j y).deriv
    rw [hβ, hg, hev.deriv_eq, hd] at hci
    exact hci
  unfold coefficientGammaSum integrandPowBetaDeriv
  rw [Finset.mul_sum]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  exact Finset.sum_le_sum fun j _ => hentry i j

theorem continuous_integrandPowBetaDeriv (hlam : 0 < lam) (hF : IsAdmissibleCoefficient lam Lam F)
    (hh : 0 < h) (hm : m ≠ 0) :
    Continuous (integrandPowBetaDeriv Φ h F m q) := by
  unfold integrandPowBetaDeriv
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  have hr := continuous_smoothDensity Φ m hh
  have hJ := (contDiff_smoothFluxEntry Φ m hlam hF hh i j).continuous
  have hr' := continuous_heatOperator (contDiff_smoothDensity Φ m hh) lam h
  have hJ' := continuous_heatOperator (contDiff_smoothFluxEntry Φ m hlam hF hh i j) lam h
  refine Continuous.add ?_ ?_
  · exact ((continuous_const.mul (hr.rpow_const fun y =>
      Or.inl (smoothDensity_pos Φ m hh hm y).ne')).mul hr').mul (hJ.pow 2)
  · exact (hr.rpow_const fun y => Or.inl (smoothDensity_pos Φ m hh hm y).ne').mul
      ((continuous_const.mul hJ).mul hJ')

theorem integrable_integrandPowBetaDeriv (hlam : 0 < lam) (hLam' : lam ≤ Lam)
    (hF : IsAdmissibleCoefficient lam Lam F) (hh : 0 < h) (hm : m ≠ 0) (hq : 1 < q) :
    Integrable (integrandPowBetaDeriv Φ h F m q) := by
  have hKc : IsCompact ({h} : Set ℝ) := isCompact_singleton
  have hKs : ({h} : Set ℝ) ⊆ Set.Ioi 0 := by simpa using hh
  obtain ⟨D, A, R, hDi, hD0, hA0, hR0, hdom⟩ := exists_heat_dominator Φ hKc hKs m
  refine Integrable.mono' ((hDi.const_mul A).const_mul
    ((d : ℝ) ^ 2 * ((|q - 2| + 2) * Lam ^ 2 * R ^ (q - 1))))
    (continuous_integrandPowBetaDeriv Φ m hlam hF hh hm).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  exact abs_powBeta_deriv_le Φ m hlam hLam' hF hm hq hKs hdom (Set.mem_singleton h) y

theorem continuous_powBeta_gamma (hlam : 0 < lam) (hF : IsAdmissibleCoefficient lam Lam F)
    (hh : 0 < h) (hm : m ≠ 0) :
    Continuous fun y => smoothDensity Φ h m y ^ q *
      coefficientGammaSum lam h (smoothCoefficient Φ h F m) y := by
  refine ((continuous_smoothDensity Φ m hh).rpow_const fun y =>
    Or.inl (smoothDensity_pos Φ m hh hm y).ne').mul ?_
  unfold coefficientGammaSum
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  have := contDiff_smoothCoefficient_entry Φ m hlam hF hh hm i j
  exact continuous_flowGamma this this lam h

/-- The time-integrated identities, second inequality, for one slice: `h ↦ ∫ r_h^q |β_h|²` has
derivative `G`, with `∫ r^q |Dβ|²_{M^h} ≤ -G`. -/
theorem slice_powBeta {C : ℝ} (hlam : 0 < lam) (hLam' : lam ≤ Lam)
    (hF : IsAdmissibleCoefficient lam Lam F) (hh : 0 < h) (hq1 : 1 < q) (hq2 : q ≤ 4 / 3)
    (hP : PackageIntegrable Φ h F m q C) :
    HasDerivAt (fun s => ∫ y, integrandPowBeta Φ s F m q y)
      (∫ y, integrandPowBetaDeriv Φ h F m q y) h ∧
    Integrable (fun y => smoothDensity Φ h m y ^ q *
      coefficientGammaSum lam h (smoothCoefficient Φ h F m) y) ∧
    ∫ y, smoothDensity Φ h m y ^ q * coefficientGammaSum lam h (smoothCoefficient Φ h F m) y ≤
      -∫ y, integrandPowBetaDeriv Φ h F m q y := by
  have hder := hasDerivAt_integral_powBeta Φ m hlam hLam' hF hh hq1
  refine ⟨hder, ?_⟩
  by_cases hm : m = 0
  · subst hm
    have hq0 : q ≠ 0 := by linarith
    have e1 : ∀ y : EvolutionAmbientState d, smoothDensity Φ h
        (0 : Measure (EvolutionAmbientState d)) y ^ q *
        coefficientGammaSum lam h (smoothCoefficient Φ h F (0 : Measure
          (EvolutionAmbientState d))) y = 0 := fun y => by
      simp [smoothDensity_zero, Real.zero_rpow hq0]
    have e2 : ∀ y : EvolutionAmbientState d,
        integrandPowBetaDeriv Φ h F (0 : Measure (EvolutionAmbientState d)) q y = 0 :=
      fun y => by simp [integrandPowBetaDeriv, smoothFluxEntry]
    simp only [e1, e2, integral_zero, neg_zero]
    exact ⟨integrable_zero _ _ _, le_refl _⟩
  · have hpos : ∀ y, 0 < smoothDensity Φ h m y := smoothDensity_pos Φ m hh hm
    have hD := integrable_integrandPowBetaDeriv Φ m hlam hLam' hF hh hm hq1
    have hW : ∀ i j : Fin d, SmoothW21 (fun y => smoothDensity Φ h m y ^ (q - 2) *
        smoothFluxEntry Φ h F m i j y ^ 2) := fun i j =>
      smoothW21_entry hlam hLam' hF hh hm i j hP.pow.1 hP.grad.1 hP.hess.1 hP.fisher.1
        hP.fluxGrad.1 hP.fluxHess.1 hP.fluxFisher.1
    have hSi : Integrable (fun y => ∑ i, ∑ j, flowL lam h (fun y' =>
        smoothDensity Φ h m y' ^ (q - 2) * smoothFluxEntry Φ h F m i j y' ^ 2) y) :=
      integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
        (hW i j).integrable_flowL lam h
    have hS0 : ∫ y, ∑ i, ∑ j, flowL lam h (fun y' =>
        smoothDensity Φ h m y' ^ (q - 2) * smoothFluxEntry Φ h F m i j y' ^ 2) y = 0 := by
      rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
        (hW i j).integrable_flowL lam h]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [integral_finsetSum _ fun j _ => (hW i j).integrable_flowL lam h]
      exact Finset.sum_eq_zero fun j _ => (hW i j).integral_flowL lam h
    have hR : Integrable (fun y => -(integrandPowBetaDeriv Φ h F m q y - ∑ i, ∑ j,
        flowL lam h (fun y' => smoothDensity Φ h m y' ^ (q - 2) *
          smoothFluxEntry Φ h F m i j y' ^ 2) y)) := (hD.sub hSi).neg
    have hcont := continuous_powBeta_gamma Φ m (q := q) hlam hF hh hm
    have hnn : ∀ y, 0 ≤ smoothDensity Φ h m y ^ q *
        coefficientGammaSum lam h (smoothCoefficient Φ h F m) y := fun y =>
      mul_nonneg (Real.rpow_nonneg (hpos y).le _) (coefficientGammaSum_nonneg hlam _ _)
    have hle := fun y => powBeta_pointwise Φ m hlam hF hh hm hq1 hq2 y
    have hint : Integrable (fun y => smoothDensity Φ h m y ^ q *
        coefficientGammaSum lam h (smoothCoefficient Φ h F m) y) := by
      refine hR.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hnn y)]
      exact hle y
    refine ⟨hint, ?_⟩
    calc _ ≤ ∫ y, -(integrandPowBetaDeriv Φ h F m q y - ∑ i, ∑ j,
          flowL lam h (fun y' => smoothDensity Φ h m y' ^ (q - 2) *
            smoothFluxEntry Φ h F m i j y' ^ 2) y) := integral_mono hint hR hle
      _ = -∫ y, integrandPowBetaDeriv Φ h F m q y := by
          rw [integral_neg, integral_sub hD hSi, hS0]; ring

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.HeatDominator
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.W21Flux
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Differentiation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Differentiating `h ↦ ∫ r_h^q dy`

The derivative of the smoothing in `h` and its use in the energy identity: for a fixed
finite measure `m`, the maps `h ↦ ∫ r_h^q dy` and `h ↦ ∫ r_h^q |β_h|² dy` are differentiable on
`(0, ∞)` with derivative the integral of the pointwise `h`-derivative, which by the heat equation
is expressed through the heat operator `M^h : D²`. The integrated form (fundamental theorem of
calculus on `[ε, H]`) is also given.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

/-- Fundamental theorem of calculus for a function with a locally bounded derivative. -/
theorem integral_deriv_eq_sub_of_bounded {f f' : ℝ → ℝ} {ε H : ℝ} (hεH : ε ≤ H)
    (hd : ∀ s ∈ Set.Icc ε H, HasDerivAt f (f' s) s) (hb : ∃ c, ∀ s ∈ Set.Icc ε H, |f' s| ≤ c) :
    ∫ s in ε..H, f' s = f H - f ε := by
  obtain ⟨c, hc⟩ := hb
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hd s (by rwa [Set.uIcc_of_le hεH] at hs)) ?_
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hεH]
  have hmeas : Measurable (deriv f) := measurable_deriv f
  have heq : Set.EqOn f' (deriv f) (Set.Icc ε H) := fun s hs => (hd s hs).deriv.symm
  refine IntegrableOn.congr_fun ?_ (fun s hs => (heq (Set.Ioc_subset_Icc_self hs)).symm)
    measurableSet_Ioc
  refine Measure.integrableOn_of_bounded (M := c) (by simp) hmeas.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  exact Filter.Eventually.of_forall fun s hs => by
    rw [Real.norm_eq_abs, ← heq (Set.Ioc_subset_Icc_self hs)]
    exact hc s (Set.Ioc_subset_Icc_self hs)

theorem entry_deriv_bound {r r' J J' R AD Lam q : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hr' : |r'| ≤ AD) (hJ : |J| ≤ Lam * r) (hJ' : |J'| ≤ Lam * AD) (hLam : 0 ≤ Lam)
    (hq : 1 < q) :
    |(q - 2) * r ^ (q - 3) * r' * J ^ 2 + r ^ (q - 2) * (2 * J * J')| ≤
      (|q - 2| + 2) * Lam ^ 2 * R ^ (q - 1) * AD := by
  have hAD : 0 ≤ AD := (abs_nonneg _).trans hr'
  have hJ2 : J ^ 2 ≤ (Lam * r) ^ 2 := by
    rw [← sq_abs J]; exact pow_le_pow_left₀ (abs_nonneg _) hJ 2
  have h3 : r ^ (q - 3) * r ^ 2 = r ^ (q - 1) := by
    have := Real.rpow_add hr (q - 3) 2
    rw [show q - 3 + 2 = q - 1 by ring, Real.rpow_two] at this
    exact this.symm
  have h2 : r ^ (q - 2) * r = r ^ (q - 1) := by
    rw [← Real.rpow_add_one hr.ne']; ring_nf
  have hRq : r ^ (q - 1) ≤ R ^ (q - 1) := Real.rpow_le_rpow hr.le hrR (by linarith)
  have hp3 : 0 ≤ r ^ (q - 3) := Real.rpow_nonneg hr.le _
  have hp2 : 0 ≤ r ^ (q - 2) := Real.rpow_nonneg hr.le _
  have hp1 : 0 ≤ r ^ (q - 1) := Real.rpow_nonneg hr.le _
  have t1 : |(q - 2) * r ^ (q - 3) * r' * J ^ 2| ≤ |q - 2| * Lam ^ 2 * r ^ (q - 1) * AD := by
    have e : |(q - 2) * r ^ (q - 3) * r' * J ^ 2| = |q - 2| * r ^ (q - 3) * |r'| * J ^ 2 := by
      simp only [abs_mul, abs_of_nonneg hp3, abs_pow, sq_abs]
    rw [e]
    calc |q - 2| * r ^ (q - 3) * |r'| * J ^ 2 ≤ |q - 2| * r ^ (q - 3) * AD * (Lam * r) ^ 2 := by
          gcongr
      _ = |q - 2| * Lam ^ 2 * (r ^ (q - 3) * r ^ 2) * AD := by ring
      _ = _ := by rw [h3]
  have t2 : |r ^ (q - 2) * (2 * J * J')| ≤ 2 * Lam ^ 2 * r ^ (q - 1) * AD := by
    have e : |r ^ (q - 2) * (2 * J * J')| = r ^ (q - 2) * (2 * |J| * |J'|) := by
      simp only [abs_mul, abs_of_nonneg hp2, abs_two]
    rw [e]
    calc r ^ (q - 2) * (2 * |J| * |J'|) ≤ r ^ (q - 2) * (2 * (Lam * r) * (Lam * AD)) := by
          gcongr
      _ = 2 * Lam ^ 2 * (r ^ (q - 2) * r) * AD := by ring
      _ = _ := by rw [h2]
  refine (abs_add_le _ _).trans ?_
  have : (|q - 2| + 2) * Lam ^ 2 * R ^ (q - 1) * AD =
      |q - 2| * Lam ^ 2 * R ^ (q - 1) * AD + 2 * Lam ^ 2 * R ^ (q - 1) * AD := by ring
  rw [this]
  have hL2 : 0 ≤ Lam ^ 2 := sq_nonneg _
  exact add_le_add (t1.trans (by gcongr)) (t2.trans (by gcongr))

section Density

variable {d : ℕ} {lam Lam : ℝ} (Φ : SmoothingKernelFamily d lam) {h q : ℝ}
  (m : Measure (EvolutionAmbientState d)) [IsFiniteMeasure m]

theorem smoothDensity_pos_of_ball (hm : m ≠ 0) {s : ℝ} (hs : s ∈ Metric.closedBall h (h / 2))
    (hh : 0 < h) (y : EvolutionAmbientState d) : 0 < smoothDensity Φ s m y := by
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hs
  exact smoothDensity_pos Φ m (by linarith [hs.1]) hm y


theorem abs_density_deriv_le {K : Set ℝ} {D : EvolutionAmbientState d → ℝ} {A R : ℝ} (hm : m ≠ 0)
    (hq : 1 < q) (hKs : K ⊆ Set.Ioi 0) (hR0 : 0 ≤ R)
    (hdom : ∀ h ∈ K, (∀ y, smoothDensity Φ h m y ≤ R) ∧
      ∀ (f : EvolutionAmbientState d → ℝ) (Cf : ℝ), Measurable f → (∀ a, |f a| ≤ Cf) →
        ∀ y, |heatOperator lam h (smoothWeighted Φ h f m) y| ≤ Cf * A * D y)
    {s : ℝ} (hs : s ∈ K) (y : EvolutionAmbientState d) :
    |q * smoothDensity Φ s m y ^ (q - 1) * heatOperator lam s (smoothDensity Φ s m) y| ≤
      q * R ^ (q - 1) * (A * D y) := by
  have hs0 : 0 < s := hKs hs
  have hq0 : 0 ≤ q := by linarith
  obtain ⟨hR, hH⟩ := hdom s hs
  have h1 := hH (fun _ => 1) 1 measurable_const (fun _ => by simp) y
  rw [← smoothDensity_eq] at h1
  have hr := smoothDensity_pos Φ m hs0 hm y
  have hpw : smoothDensity Φ s m y ^ (q - 1) ≤ R ^ (q - 1) :=
    Real.rpow_le_rpow hr.le (hR y) (by linarith)
  rw [abs_mul, abs_mul, abs_of_nonneg hq0, abs_of_nonneg (Real.rpow_nonneg hr.le _)]
  calc q * smoothDensity Φ s m y ^ (q - 1) * |heatOperator lam s (smoothDensity Φ s m) y|
      ≤ q * R ^ (q - 1) * (1 * A * D y) := by gcongr
    _ = _ := by ring

/-- `h ↦ ∫ r_h^q dy` is differentiable on `(0, ∞)`, with derivative the integral of
`q r^{q-1} ∂_h r`, where `∂_h r = M^h : D² r` by the heat equation. -/
theorem hasDerivAt_integral_rpow_density (hh : 0 < h) (hq : 1 < q) :
    HasDerivAt (fun s => ∫ y, smoothDensity Φ s m y ^ q)
      (∫ y, q * smoothDensity Φ h m y ^ (q - 1) * heatOperator lam h (smoothDensity Φ h m) y)
      h := by
  by_cases hm : m = 0
  · subst hm
    have hq1 : q - 1 ≠ 0 := by linarith
    have hq0 : q ≠ 0 := by linarith
    have e1 : (fun s => ∫ y : EvolutionAmbientState d,
        smoothDensity Φ s (0 : Measure (EvolutionAmbientState d)) y ^ q) = fun _ => 0 := by
      funext s; simp [smoothDensity_zero, Real.zero_rpow hq0]
    have e2 : (∫ y : EvolutionAmbientState d, q * smoothDensity Φ h
        (0 : Measure (EvolutionAmbientState d)) y ^ (q - 1) *
        heatOperator lam h (smoothDensity Φ h (0 : Measure (EvolutionAmbientState d))) y) = 0 := by
      simp [smoothDensity_zero, Real.zero_rpow hq1]
    rw [e1, e2]
    exact hasDerivAt_const h 0
  · set K : Set ℝ := Metric.closedBall h (h / 2) with hKdef
    have hKc : IsCompact K := isCompact_closedBall _ _
    have hKs : K ⊆ Set.Ioi 0 := fun s hs => by
      rw [hKdef, Metric.mem_closedBall, Real.dist_eq, abs_le] at hs
      simp only [Set.mem_Ioi]; linarith [hs.1]
    have hhK : h ∈ K := Metric.mem_closedBall_self (by linarith)
    obtain ⟨D, A, R, hDi, hD0, hA0, hR0, hdom⟩ := exists_heat_dominator Φ hKc hKs m
    have hnhds : K ∈ nhds h := Metric.closedBall_mem_nhds h (by linarith)
    have hq0 : 0 ≤ q := by linarith
    have hRq : 0 ≤ R ^ (q - 1) := Real.rpow_nonneg hR0 _
    have hint0 : Integrable (fun y => smoothDensity Φ h m y ^ q) := by
      refine (integrable_of_le_smoothWeight2 (Φ := Φ) (m := m) hh
        ((continuous_smoothDensity Φ m hh).rpow_const fun y =>
          Or.inl (smoothDensity_pos Φ m hh hm y).ne')
        (fun y => Real.rpow_nonneg (smoothDensity_nonneg Φ m hh y) _) (A := R ^ (q - 1))
        (fun y => ?_)).1
      exact target_rpow_le m hh hm hq (hdom h hhK).1 y
    have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun s y => smoothDensity Φ s m y ^ q)
      (F' := fun s y => q * smoothDensity Φ s m y ^ (q - 1) *
        heatOperator lam s (smoothDensity Φ s m) y)
      (bound := fun y => q * R ^ (q - 1) * (A * D y)) (x₀ := h)
      (μ := (volume : Measure (EvolutionAmbientState d))) hnhds ?_ hint0 ?_ ?_
      ((hDi.const_mul A).const_mul (q * R ^ (q - 1))) ?_
    · exact hmain.2
    · refine Filter.eventually_of_mem hnhds fun s hs => ?_
      have hs0 : 0 < s := hKs hs
      exact ((continuous_smoothDensity Φ m hs0).rpow_const fun y =>
        Or.inl (smoothDensity_pos Φ m hs0 hm y).ne').aestronglyMeasurable
    · refine (continuous_const.mul ?_ |>.mul ?_).aestronglyMeasurable
      · exact (continuous_smoothDensity Φ m hh).rpow_const fun y =>
          Or.inl (smoothDensity_pos Φ m hh hm y).ne'
      · exact continuous_heatOperator (contDiff_smoothDensity Φ m hh) lam h
    · exact Filter.Eventually.of_forall fun y s hs => by
        rw [Real.norm_eq_abs]
        exact abs_density_deriv_le Φ m hm hq hKs hR0 hdom hs y
    · refine Filter.Eventually.of_forall fun y s hs => ?_
      have hs0 : 0 < s := hKs hs
      have hr := smoothDensity_pos Φ m hs0 hm y
      have h1 := hasDerivAt_smoothDensity Φ m hs0 y
      have := h1.rpow_const (p := q) (Or.inl hr.ne')
      convert this using 1
      ring

theorem integrandPowBeta_eq_sum {F : EvolutionAmbientState d → PDE.Mat d} (hh : 0 < h)
    (hm : m ≠ 0) :
    integrandPowBeta Φ h F m q = fun y => ∑ i, ∑ j,
      smoothDensity Φ h m y ^ (q - 2) * smoothFluxEntry Φ h F m i j y ^ 2 := by
  have hpos : ∀ y, 0 < smoothDensity Φ h m y := smoothDensity_pos Φ m hh hm
  funext y
  unfold integrandPowBeta frobeniusSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hJ : smoothFluxEntry Φ h F m i j y =
      smoothDensity Φ h m y * smoothCoefficient Φ h F m y i j :=
    smoothFluxEntry_eq_mul Φ m hh hm i j y
  have h2 : smoothDensity Φ h m y ^ (q - 2) * smoothDensity Φ h m y ^ 2 =
      smoothDensity Φ h m y ^ q := by
    have e := rpow_sub_one_mul_self (hpos y) q
    rw [← rpow_sub_two_mul_self (hpos y) q] at e
    rw [← e]; ring
  rw [hJ, mul_pow, ← mul_assoc, h2]

/-- Pointwise bound for the `h`-derivative of `r^q |β|²`, uniform over `h ∈ K`. -/
theorem abs_powBeta_deriv_le {F : EvolutionAmbientState d → PDE.Mat d} {K : Set ℝ}
    {D : EvolutionAmbientState d → ℝ} {A R : ℝ} (hlam : 0 < lam) (hLam' : lam ≤ Lam)
    (hF : IsAdmissibleCoefficient lam Lam F) (hm : m ≠ 0) (hq : 1 < q) (hKs : K ⊆ Set.Ioi 0)
    (hdom : ∀ h ∈ K, (∀ y, smoothDensity Φ h m y ≤ R) ∧
      ∀ (f : EvolutionAmbientState d → ℝ) (Cf : ℝ), Measurable f → (∀ a, |f a| ≤ Cf) →
        ∀ y, |heatOperator lam h (smoothWeighted Φ h f m) y| ≤ Cf * A * D y)
    {s : ℝ} (hs : s ∈ K) (y : EvolutionAmbientState d) :
    |∑ i, ∑ j, ((q - 2) * smoothDensity Φ s m y ^ (q - 3) *
        heatOperator lam s (smoothDensity Φ s m) y * smoothFluxEntry Φ s F m i j y ^ 2 +
        smoothDensity Φ s m y ^ (q - 2) * (2 * smoothFluxEntry Φ s F m i j y *
          heatOperator lam s (smoothFluxEntry Φ s F m i j) y))| ≤
      (d : ℝ) ^ 2 * ((|q - 2| + 2) * Lam ^ 2 * R ^ (q - 1)) * (A * D y) := by
  have hLam : 0 ≤ Lam := (hlam.trans_le hLam').le
  have hs0 : 0 < s := hKs hs
  obtain ⟨hR, hH⟩ := hdom s hs
  have h1 := hH (fun _ => 1) 1 measurable_const (fun _ => by simp) y
  rw [← smoothDensity_eq] at h1
  have hr := smoothDensity_pos Φ m hs0 hm y
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |∑ j, ((q - 2) * smoothDensity Φ s m y ^ (q - 3) *
        heatOperator lam s (smoothDensity Φ s m) y * smoothFluxEntry Φ s F m i j y ^ 2 +
        smoothDensity Φ s m y ^ (q - 2) * (2 * smoothFluxEntry Φ s F m i j y *
          heatOperator lam s (smoothFluxEntry Φ s F m i j) y))|
      ≤ ∑ _i : Fin d, ∑ _j : Fin d, (|q - 2| + 2) * Lam ^ 2 * R ^ (q - 1) * (A * D y) := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        have hJb : |smoothFluxEntry Φ s F m i j y| ≤ Lam * smoothDensity Φ s m y := by
          rw [smoothFluxEntry_eq_mul Φ m hs0 hm i j y, abs_mul, abs_of_pos hr, mul_comm]
          exact mul_le_mul_of_nonneg_right
            (abs_smoothCoefficient_le Φ m hlam hF hs0 y i j) hr.le
        have hJ' := hH (fun a => F a i j) Lam (hF.measurable i j)
          (fun a => hF.abs_apply_le hlam a i j) y
        rw [← smoothFluxEntry_eq] at hJ'
        refine entry_deriv_bound hr (hR y) ?_ hJb ?_ hLam hq
        · simpa using h1
        · calc _ ≤ _ := hJ'
            _ = Lam * (A * D y) := by ring
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- `h ↦ ∫ r_h^q |β_h|² dy` is differentiable on `(0, ∞)`, with derivative the integral of the
`h`-derivative of `∑ᵢⱼ r^{q-2} Jᵢⱼ²`, expressed by the heat operator on `r` and on the flux
entries `Jᵢⱼ`. -/
theorem hasDerivAt_integral_powBeta {F : EvolutionAmbientState d → PDE.Mat d} (hlam : 0 < lam)
    (hLam' : lam ≤ Lam) (hF : IsAdmissibleCoefficient lam Lam F) (hh : 0 < h) (hq : 1 < q) :
    HasDerivAt (fun s => ∫ y, integrandPowBeta Φ s F m q y)
      (∫ y, ∑ i, ∑ j, ((q - 2) * smoothDensity Φ h m y ^ (q - 3) *
        heatOperator lam h (smoothDensity Φ h m) y * smoothFluxEntry Φ h F m i j y ^ 2 +
        smoothDensity Φ h m y ^ (q - 2) * (2 * smoothFluxEntry Φ h F m i j y *
          heatOperator lam h (smoothFluxEntry Φ h F m i j) y))) h := by
  have hLam : 0 ≤ Lam := (hlam.trans_le hLam').le
  by_cases hm : m = 0
  · subst hm
    have e1 : ∀ s, integrandPowBeta Φ s F (0 : Measure (EvolutionAmbientState d)) q =
        fun _ => 0 := fun s => by
      funext y; simp [integrandPowBeta, smoothDensity_zero, Real.zero_rpow (by linarith : q ≠ 0)]
    have e2 : (∫ y : EvolutionAmbientState d, ∑ i : Fin d, ∑ j : Fin d,
        ((q - 2) * smoothDensity Φ h (0 : Measure (EvolutionAmbientState d)) y ^ (q - 3) *
        heatOperator lam h (smoothDensity Φ h (0 : Measure (EvolutionAmbientState d))) y *
        smoothFluxEntry Φ h F (0 : Measure (EvolutionAmbientState d)) i j y ^ 2 +
        smoothDensity Φ h (0 : Measure (EvolutionAmbientState d)) y ^ (q - 2) *
          (2 * smoothFluxEntry Φ h F (0 : Measure (EvolutionAmbientState d)) i j y *
          heatOperator lam h (smoothFluxEntry Φ h F (0 : Measure (EvolutionAmbientState d)) i j)
            y))) = 0 := by
      simp [smoothFluxEntry]
    simp only [e1]
    rw [e2]
    simpa using hasDerivAt_const h (0 : ℝ)
  · set K : Set ℝ := Metric.closedBall h (h / 2) with hKdef
    have hKc : IsCompact K := isCompact_closedBall _ _
    have hKs : K ⊆ Set.Ioi 0 := fun s hs => by
      rw [hKdef, Metric.mem_closedBall, Real.dist_eq, abs_le] at hs
      simp only [Set.mem_Ioi]; linarith [hs.1]
    have hhK : h ∈ K := Metric.mem_closedBall_self (by linarith)
    obtain ⟨D, A, R, hDi, hD0, hA0, hR0, hdom⟩ := exists_heat_dominator Φ hKc hKs m
    obtain ⟨C1, C2, Cfi, hCfi, hk⟩ := exists_kernelConsts (Φ := Φ) hKc hKs
    have hnhds : K ∈ nhds h := Metric.closedBall_mem_nhds h (by linarith)
    have hsum : ∀ s, 0 < s → integrandPowBeta Φ s F m q = fun y => ∑ i, ∑ j,
        smoothDensity Φ s m y ^ (q - 2) * smoothFluxEntry Φ s F m i j y ^ 2 :=
      fun s hs => integrandPowBeta_eq_sum Φ m hs hm
    have hint0 : Integrable (fun y => ∑ i, ∑ j,
        smoothDensity Φ h m y ^ (q - 2) * smoothFluxEntry Φ h F m i j y ^ 2) := by
      rw [← hsum h hh]
      exact (packageIntegrable_of_ne_zero hlam hLam' hF hh hm (hk h hhK) hq hCfi
        (hdom h hhK).1).powBeta.1
    set Bd : ℝ := (d : ℝ) ^ 2 * ((|q - 2| + 2) * Lam ^ 2 * R ^ (q - 1)) with hBd
    have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun s y => ∑ i, ∑ j,
        smoothDensity Φ s m y ^ (q - 2) * smoothFluxEntry Φ s F m i j y ^ 2)
      (F' := fun s y => ∑ i, ∑ j, ((q - 2) * smoothDensity Φ s m y ^ (q - 3) *
        heatOperator lam s (smoothDensity Φ s m) y * smoothFluxEntry Φ s F m i j y ^ 2 +
        smoothDensity Φ s m y ^ (q - 2) * (2 * smoothFluxEntry Φ s F m i j y *
          heatOperator lam s (smoothFluxEntry Φ s F m i j) y)))
      (bound := fun y => Bd * (A * D y)) (x₀ := h)
      (μ := (volume : Measure (EvolutionAmbientState d))) hnhds ?_ hint0 ?_ ?_
      (((hDi.const_mul A).const_mul Bd)) ?_
    · refine (hmain.2).congr_of_eventuallyEq ?_
      filter_upwards [hnhds] with s hs
      simp only [hsum s (hKs hs)]
    · refine Filter.eventually_of_mem hnhds fun s hs => ?_
      have hs0 : 0 < s := hKs hs
      refine (continuous_finsetSum _ fun i _ =>
        continuous_finsetSum _ fun j _ => ?_).aestronglyMeasurable
      exact ((continuous_smoothDensity Φ m hs0).rpow_const fun y =>
        Or.inl (smoothDensity_pos Φ m hs0 hm y).ne').mul
          ((contDiff_smoothFluxEntry Φ m hlam hF hs0 i j).continuous.pow 2)
    · refine (continuous_finsetSum _ fun i _ =>
        continuous_finsetSum _ fun j _ => ?_).aestronglyMeasurable
      have hr := continuous_smoothDensity Φ m hh
      have hJ := (contDiff_smoothFluxEntry Φ m hlam hF hh i j).continuous
      have hr' := continuous_heatOperator (contDiff_smoothDensity Φ m hh) lam h
      have hJ' := continuous_heatOperator (contDiff_smoothFluxEntry Φ m hlam hF hh i j) lam h
      refine Continuous.add ?_ ?_
      · exact ((continuous_const.mul (hr.rpow_const fun y =>
          Or.inl (smoothDensity_pos Φ m hh hm y).ne')).mul hr').mul (hJ.pow 2)
      · exact (hr.rpow_const fun y => Or.inl (smoothDensity_pos Φ m hh hm y).ne').mul
          ((continuous_const.mul hJ).mul hJ')
    · exact Filter.Eventually.of_forall fun y s hs => by
        rw [Real.norm_eq_abs]
        exact abs_powBeta_deriv_le Φ m hlam hLam' hF hm hq hKs hdom hs y
    · refine Filter.Eventually.of_forall fun y s hs => ?_
      have hs0 : 0 < s := hKs hs
      have hr := smoothDensity_pos Φ m hs0 hm y
      refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => ?_
      have h1 := (hasDerivAt_smoothDensity Φ m hs0 y).rpow_const (p := q - 2) (Or.inl hr.ne')
      have h2 := (hasDerivAt_smoothFluxEntry Φ m hlam hF hs0 i j y).pow 2
      have h3 := h1.mul h2
      have e : q - 2 - 1 = q - 3 := by ring
      rw [e] at h3
      convert h3 using 1
      simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
      ring

/-- Integrated form: for `0 < ε ≤ H`,
`∫ r_H^q - ∫ r_ε^q = ∫_ε^H ∫ q r_s^{q-1} (M^s : D² r_s) dy ds`. -/
theorem integral_rpow_density_sub (hq : 1 < q) {ε H : ℝ} (hε : 0 < ε) (hεH : ε ≤ H) :
    ∫ s in ε..H, (∫ y, q * smoothDensity Φ s m y ^ (q - 1) *
        heatOperator lam s (smoothDensity Φ s m) y) =
      (∫ y, smoothDensity Φ H m y ^ q) - ∫ y, smoothDensity Φ ε m y ^ q := by
  refine integral_deriv_eq_sub_of_bounded (f := fun s => ∫ y, smoothDensity Φ s m y ^ q) hεH
    (fun s hs => hasDerivAt_integral_rpow_density Φ m (lt_of_lt_of_le hε hs.1) hq) ?_
  by_cases hm : m = 0
  · subst hm
    refine ⟨0, fun s hs => ?_⟩
    have hq1 : q - 1 ≠ 0 := by linarith
    simp [smoothDensity_zero, Real.zero_rpow hq1]
  · have hKc : IsCompact (Set.Icc ε H) := isCompact_Icc
    have hKs : Set.Icc ε H ⊆ Set.Ioi 0 := fun s hs => lt_of_lt_of_le hε hs.1
    obtain ⟨D, A, R, hDi, hD0, hA0, hR0, hdom⟩ := exists_heat_dominator Φ hKc hKs m
    refine ⟨∫ y, q * R ^ (q - 1) * (A * D y), fun s hs => ?_⟩
    have := norm_integral_le_of_norm_le ((hDi.const_mul A).const_mul (q * R ^ (q - 1)))
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]; exact abs_density_deriv_le Φ m hm hq hKs hR0 hdom hs y)
    simpa [Real.norm_eq_abs] using this

/-- Integrated form for `r^q |β|²`: for `0 < ε ≤ H`, `∫ r_H^q|β_H|² - ∫ r_ε^q|β_ε|²` is the
integral over `[ε, H]` of the derivative of `hasDerivAt_integral_powBeta`. -/
theorem integral_powBeta_sub {F : EvolutionAmbientState d → PDE.Mat d} (hlam : 0 < lam)
    (hLam' : lam ≤ Lam) (hF : IsAdmissibleCoefficient lam Lam F) (hq : 1 < q) {ε H : ℝ}
    (hε : 0 < ε) (hεH : ε ≤ H) :
    ∫ s in ε..H, (∫ y, ∑ i, ∑ j, ((q - 2) * smoothDensity Φ s m y ^ (q - 3) *
        heatOperator lam s (smoothDensity Φ s m) y * smoothFluxEntry Φ s F m i j y ^ 2 +
        smoothDensity Φ s m y ^ (q - 2) * (2 * smoothFluxEntry Φ s F m i j y *
          heatOperator lam s (smoothFluxEntry Φ s F m i j) y))) =
      (∫ y, integrandPowBeta Φ H F m q y) - ∫ y, integrandPowBeta Φ ε F m q y := by
  refine integral_deriv_eq_sub_of_bounded
    (f := fun s => ∫ y, integrandPowBeta Φ s F m q y) hεH
    (fun s hs => hasDerivAt_integral_powBeta Φ m hlam hLam' hF (lt_of_lt_of_le hε hs.1) hq) ?_
  by_cases hm : m = 0
  · subst hm
    refine ⟨0, fun s hs => ?_⟩
    simp [smoothFluxEntry]
  · have hKc : IsCompact (Set.Icc ε H) := isCompact_Icc
    have hKs : Set.Icc ε H ⊆ Set.Ioi 0 := fun s hs => lt_of_lt_of_le hε hs.1
    obtain ⟨D, A, R, hDi, hD0, hA0, hR0, hdom⟩ := exists_heat_dominator Φ hKc hKs m
    refine ⟨∫ y, (d : ℝ) ^ 2 * ((|q - 2| + 2) * Lam ^ 2 * R ^ (q - 1)) * (A * D y), fun s hs => ?_⟩
    have := norm_integral_le_of_norm_le
      ((hDi.const_mul A).const_mul ((d : ℝ) ^ 2 * ((|q - 2| + 2) * Lam ^ 2 * R ^ (q - 1))))
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]
        exact abs_powBeta_deriv_le Φ m hlam hLam' hF hm hq hKs hdom hs y)
    simpa [Real.norm_eq_abs] using this

end Density

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

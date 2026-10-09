module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Convolution

/-!
# The heat equation for weighted smoothings

The smoothing estimates, `h`-part: the weighted smoothing
`(h, y) ↦ ∫ Φ_h(y - y') f(y') dm(y')` is differentiable in `h`, its `h`-derivative is obtained
under the integral sign, and it solves `∂_h u = M^h : D²u`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ} {lam : ℝ}

theorem abs_heatOperator_le {F : EvolutionAmbientState d → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (h : ℝ) (y : EvolutionAmbientState d) :
    |heatOperator lam h F y| ≤
      |lam| / 2 * (2 * h ^ 2 * d + 2 * |h| * d + d) * ‖iteratedFDeriv ℝ 2 F y‖ := by
  set N := ‖iteratedFDeriv ℝ 2 F y‖ with hN
  have hN0 : 0 ≤ N := norm_nonneg _
  have hpp : |positionLaplacian F y| ≤ d * N := by
    unfold positionLaplacian
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |positionPartial i (positionPartial i F) y| ≤ ∑ _i : Fin d, N :=
          Finset.sum_le_sum fun i _ => abs_coordPartial_coordPartial_le hF (Sum.inr i) (Sum.inr i) y
      _ = d * N := by simp
  have hmx : |mixedDivergence F y| ≤ d * N := by
    unfold mixedDivergence
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |positionPartial i (velocityPartial i F) y| ≤ ∑ _i : Fin d, N :=
          Finset.sum_le_sum fun i _ => abs_coordPartial_coordPartial_le hF (Sum.inr i) (Sum.inl i) y
      _ = d * N := by simp
  have hvv : |velocityLaplacian F y| ≤ d * N := by
    unfold velocityLaplacian
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |velocityPartial i (velocityPartial i F) y| ≤ ∑ _i : Fin d, N :=
          Finset.sum_le_sum fun i _ => abs_coordPartial_coordPartial_le hF (Sum.inl i) (Sum.inl i) y
      _ = d * N := by simp
  unfold heatOperator
  rw [abs_mul, abs_div, abs_two]
  have h1 : |2 * h ^ 2 * positionLaplacian F y - 2 * h * mixedDivergence F y +
      velocityLaplacian F y| ≤ (2 * h ^ 2 * d + 2 * |h| * d + d) * N := by
    refine (abs_add_le _ _).trans ?_
    refine (add_le_add (abs_sub _ _) hvv).trans ?_
    have e1 : |h ^ 2| = h ^ 2 := abs_of_nonneg (sq_nonneg h)
    simp only [abs_mul, abs_two, e1]
    nlinarith [mul_le_mul_of_nonneg_left hpp (by positivity : (0:ℝ) ≤ 2 * h ^ 2),
      mul_le_mul_of_nonneg_left hmx (by positivity : (0:ℝ) ≤ 2 * |h|)]
  calc |lam| / 2 * |2 * h ^ 2 * positionLaplacian F y - 2 * h * mixedDivergence F y +
        velocityLaplacian F y| ≤ |lam| / 2 * ((2 * h ^ 2 * d + 2 * |h| * d + d) * N) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring

theorem continuous_heatOperator {F : EvolutionAmbientState d → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (lam h : ℝ) : Continuous (heatOperator lam h F) := by
  have hc : ∀ c c', Continuous (coordPartial c (coordPartial c' F)) := fun c c' =>
    continuous_coordPartial (contDiff_coordPartial hF c') c
  unfold heatOperator positionLaplacian mixedDivergence velocityLaplacian
  refine continuous_const.mul ((((continuous_const.mul (continuous_finsetSum _ fun i _ => ?_)).sub
    (continuous_const.mul (continuous_finsetSum _ fun i _ => ?_))).add
    (continuous_finsetSum _ fun i _ => ?_)))
  · exact hc (Sum.inr i) (Sum.inr i)
  · exact hc (Sum.inr i) (Sum.inl i)
  · exact hc (Sum.inl i) (Sum.inl i)

section Measure

variable {G : EvolutionAmbientState d → ℝ} {f : EvolutionAmbientState d → ℝ} {Cf : ℝ}
  {m : Measure (EvolutionAmbientState d)} [IsFiniteMeasure m]

theorem coordPartial₂_wconv (hG : IsBoundedSmooth G) (hf : Measurable f)
    (hfb : ∀ a, |f a| ≤ Cf) (c c' : Fin d ⊕ Fin d) :
    coordPartial c' (coordPartial c (wconv G f m)) =
      wconv (coordPartial c' (coordPartial c G)) f m := by
  rw [coordPartial_wconv hG hf hfb m c]
  exact coordPartial_wconv (hG.coordPartial c) hf hfb m c'

theorem integrable_wconv_term (hG : IsBoundedSmooth G) (hf : Measurable f)
    (hfb : ∀ a, |f a| ≤ Cf) (c c' : Fin d ⊕ Fin d) (y : EvolutionAmbientState d) :
    Integrable (fun a => f a • coordPartial c' (coordPartial c G) (y - a)) m := by
  have h2 := (hG.coordPartial c).coordPartial c'
  obtain ⟨C0, hC0⟩ := h2.bound_zero
  exact integrable_weighted_translate h2.contDiff.continuous hf hfb hC0 m y

/-- The heat operator commutes with weighted convolution. -/
theorem heatOperator_wconv (hG : IsBoundedSmooth G) (hf : Measurable f)
    (hfb : ∀ a, |f a| ≤ Cf) (lam h : ℝ) (y : EvolutionAmbientState d) :
    heatOperator lam h (wconv G f m) y = wconv (heatOperator lam h G) f m y := by
  have hint := integrable_wconv_term (m := m) hG hf hfb
  have e : ∀ c c', coordPartial c' (coordPartial c (wconv G f m)) y =
      ∫ a, f a • coordPartial c' (coordPartial c G) (y - a) ∂m := fun c c' =>
    congrFun (coordPartial₂_wconv hG hf hfb c c') y
  have hpt : ∀ a, f a • heatOperator lam h G (y - a) = lam / 2 *
      (2 * h ^ 2 * ∑ i, f a • coordPartial (Sum.inr i) (coordPartial (Sum.inr i) G) (y - a) -
       2 * h * ∑ i, f a • coordPartial (Sum.inr i) (coordPartial (Sum.inl i) G) (y - a) +
       ∑ i, f a • coordPartial (Sum.inl i) (coordPartial (Sum.inl i) G) (y - a)) := by
    intro a
    simp only [heatOperator, positionLaplacian, mixedDivergence, velocityLaplacian,
      positionPartial_eq, velocityPartial_eq, smul_eq_mul, ← Finset.mul_sum]
    ring
  rw [show wconv (heatOperator lam h G) f m y = ∫ a, f a • heatOperator lam h G (y - a) ∂m
    from rfl]
  simp only [hpt]
  unfold heatOperator positionLaplacian mixedDivergence velocityLaplacian
  simp only [positionPartial_eq, velocityPartial_eq, e]
  rw [integral_const_mul, integral_add, integral_sub, integral_const_mul, integral_const_mul,
    integral_finsetSum, integral_finsetSum, integral_finsetSum]
  · exact fun i _ => hint _ _ _
  · exact fun i _ => hint _ _ _
  · exact fun i _ => hint _ _ _
  · exact (integrable_finsetSum _ fun i _ => hint _ _ _).const_mul _
  · exact (integrable_finsetSum _ fun i _ => hint _ _ _).const_mul _
  · exact ((integrable_finsetSum _ fun i _ => hint _ _ _).const_mul _).sub
      ((integrable_finsetSum _ fun i _ => hint _ _ _).const_mul _)
  · exact integrable_finsetSum _ fun i _ => hint _ _ _

end Measure

section KernelFamily

variable (Φ : SmoothingKernelFamily d lam) {f : EvolutionAmbientState d → ℝ} {Cf : ℝ}
  {m : Measure (EvolutionAmbientState d)} [IsFiniteMeasure m]

/-- The weighted smoothing satisfies the heat equation `∂_h u = M^h : D² u`, and the `h`-derivative
may be taken under the integral sign. -/
theorem hasDerivAt_smoothWeighted {h : ℝ} (hh : 0 < h) (hf : Measurable f)
    (hfb : ∀ a, |f a| ≤ Cf) (y : EvolutionAmbientState d) :
    HasDerivAt (fun s => smoothWeighted Φ s f m y)
      (heatOperator lam h (smoothWeighted Φ h f m) y) h := by
  set K : Set ℝ := Metric.closedBall h (h / 2) with hKdef
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKpos : ∀ s ∈ K, 0 < s ∧ s ≤ 3 * h / 2 := by
    intro s hs
    rw [hKdef, Metric.mem_closedBall, Real.dist_eq, abs_le] at hs
    constructor <;> linarith [hs.1, hs.2]
  have hsub : K ⊆ Set.Ioi 0 := fun s hs => (hKpos s hs).1
  obtain ⟨C2, hC2⟩ := Φ.deriv_bound 2 hK hsub
  obtain ⟨W, hW⟩ := Φ.weight_le 2 hK hsub
  have hWnn : 0 ≤ W := by
    have := hW h (Metric.mem_closedBall_self (by linarith))
      0
    have hp := Φ.pos hh 0
    exact le_trans (by positivity) this
  set Hmax : ℝ := |lam| / 2 * (2 * (3 * h / 2) ^ 2 * d + 2 * (3 * h / 2) * d + d) with hHmax
  have hHnn : 0 ≤ Hmax := by positivity
  have hbound : ∀ s ∈ K, ∀ z, |heatOperator lam s (Φ.kernel s) z| ≤ Hmax * (|C2| * W) := by
    intro s hs z
    obtain ⟨hs0, hs1⟩ := hKpos s hs
    have h1 := abs_heatOperator_le (lam := lam) (Φ.contDiff hs0) s z
    have h2 := hC2 s hs z
    have h3 := hW s hs z
    have hp := Φ.pos hs0 z
    have hit : ‖iteratedFDeriv ℝ 2 (Φ.kernel s) z‖ ≤ |C2| * W := by
      calc _ ≤ C2 * (1 + ‖z‖) ^ 2 * Φ.kernel s z := h2
        _ ≤ |C2| * ((1 + ‖z‖) ^ 2 * Φ.kernel s z) := by
            rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self C2) (by positivity)
        _ ≤ |C2| * W := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
    have hcoef : |lam| / 2 * (2 * s ^ 2 * d + 2 * |s| * d + d) ≤ Hmax := by
      rw [hHmax, abs_of_pos hs0]
      have : s ^ 2 ≤ (3 * h / 2) ^ 2 := pow_le_pow_left₀ hs0.le hs1 2
      gcongr
    calc _ ≤ _ := h1
      _ ≤ Hmax * (|C2| * W) := mul_le_mul hcoef hit (norm_nonneg _) hHnn
  have hmeasK : ∀ s ∈ K, AEStronglyMeasurable (fun a => f a • Φ.kernel s (y - a)) m := by
    intro s hs
    exact hf.aestronglyMeasurable.smul
      (((Φ.contDiff (hKpos s hs).1).continuous.comp
        (continuous_const.sub continuous_id)).aestronglyMeasurable)
  have hnhds : K ∈ nhds h := Metric.closedBall_mem_nhds h (by linarith)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s a => f a • Φ.kernel s (y - a))
    (F' := fun s a => f a • heatOperator lam s (Φ.kernel s) (y - a))
    (bound := fun _ => Cf * (Hmax * (|C2| * W))) (x₀ := h) (μ := m) hnhds
    (Filter.eventually_of_mem hnhds hmeasK)
    (integrable_weighted_translate (Φ.isBoundedSmooth hh).contDiff.continuous hf hfb
      (Φ.isBoundedSmooth hh).bound_zero.choose_spec m y)
    ?_ ?_ (integrable_const _) ?_
  · have hH := heatOperator_wconv (Φ.isBoundedSmooth hh) hf hfb (m := m) lam h y
    simpa only [smoothWeighted, hH, wconv] using hmain.2
  · exact hf.aestronglyMeasurable.smul
      (((continuous_heatOperator (Φ.contDiff hh) lam h).comp
        (continuous_const.sub continuous_id)).aestronglyMeasurable)
  · refine Filter.Eventually.of_forall fun a s hs => ?_
    rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul (hfb a) (hbound s hs _) (abs_nonneg _) ((abs_nonneg _).trans (hfb a))
  · refine Filter.Eventually.of_forall fun a s hs => ?_
    exact (Φ.hasDerivAt_heat (hKpos s hs).1 (y - a)).const_smul (f a)

end KernelFamily

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

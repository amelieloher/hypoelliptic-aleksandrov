module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Bounds
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.CauchySchwarz

/-!
# Fisher-type bounds for the smoothed density

The smoothing estimates, first half:
`|D r|² / r ≤ ∫ |DΦ_h|²/Φ_h (y - y') dm(y')`, more generally the weighted bound
`|D (f m)_h|² ≤ ‖f‖²_∞ r ∫ |DΦ_h|²/Φ_h (y - y') dm(y')`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ} {lam : ℝ} (Φ : SmoothingKernelFamily d lam)

/-- The Fisher kernel `|DΦ_h|² / Φ_h`. -/
def fisherKernel (h : ℝ) (z : EvolutionAmbientState d) : ℝ :=
  gradNormSq (Φ.kernel h) z / Φ.kernel h z

/-- The coordinate component `(∂_c Φ_h)² / Φ_h` of the Fisher kernel. -/
def fisherComp (h : ℝ) (c : Fin d ⊕ Fin d) (z : EvolutionAmbientState d) : ℝ :=
  coordPartial c (Φ.kernel h) z ^ 2 / Φ.kernel h z

/-- The Fisher smoothing `∫ |DΦ_h|²/Φ_h (y - y') dm(y')`. -/
def fisherSmooth (h : ℝ) (m : Measure (EvolutionAmbientState d)) (y : EvolutionAmbientState d) :
    ℝ :=
  ∫ a, fisherKernel Φ h (y - a) ∂m

variable {Φ} {h : ℝ}

theorem fisherKernel_eq_sum (z : EvolutionAmbientState d) :
    fisherKernel Φ h z = ∑ c, fisherComp Φ h c z := by
  unfold fisherKernel fisherComp gradNormSq
  rw [Finset.sum_div]

theorem fisherComp_nonneg (hh : 0 < h) (c : Fin d ⊕ Fin d) (z : EvolutionAmbientState d) :
    0 ≤ fisherComp Φ h c z :=
  div_nonneg (sq_nonneg _) (Φ.pos hh z).le

theorem fisherComp_le (hh : 0 < h) (c : Fin d ⊕ Fin d) (z : EvolutionAmbientState d) :
    fisherComp Φ h c z ≤ fisherKernel Φ h z := by
  rw [fisherKernel_eq_sum]
  exact Finset.single_le_sum (f := fun c => fisherComp Φ h c z)
    (fun c _ => fisherComp_nonneg hh c z) (Finset.mem_univ c)

theorem fisherKernel_nonneg (hh : 0 < h) (z : EvolutionAmbientState d) :
    0 ≤ fisherKernel Φ h z :=
  div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Φ.pos hh z).le

theorem continuous_fisherComp (hh : 0 < h) (c : Fin d ⊕ Fin d) :
    Continuous (fisherComp Φ h c) :=
  ((continuous_coordPartial (Φ.contDiff hh) c).pow 2).div (Φ.contDiff hh).continuous
    fun z => (Φ.pos hh z).ne'

theorem continuous_fisherKernel (hh : 0 < h) : Continuous (fisherKernel Φ h) := by
  have : fisherKernel Φ h = fun z => ∑ c, fisherComp Φ h c z := funext fisherKernel_eq_sum
  rw [this]
  exact continuous_finsetSum _ fun c _ => continuous_fisherComp hh c

/-- The Fisher kernel is dominated by the weighted kernel `(1 + |y|)² Φ_h`, locally uniformly in
`h`. -/
theorem exists_fisherKernel_le {K : Set ℝ} (hK : IsCompact K) (hsub : K ⊆ Set.Ioi 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h ∈ K, ∀ z, fisherKernel Φ h z ≤ C * ((1 + ‖z‖) ^ 2 * Φ.kernel h z) := by
  obtain ⟨C1, hC1⟩ := Φ.deriv_bound 1 hK hsub
  refine ⟨2 * d * C1 ^ 2, by positivity, fun h hh z => ?_⟩
  have hh0 : 0 < h := hsub hh
  have hp := Φ.pos hh0 z
  have h1 : ‖fderiv ℝ (Φ.kernel h) z‖ ≤ C1 * (1 + ‖z‖) ^ 1 * Φ.kernel h z := by
    simpa using hC1 h hh z
  have h2 : ‖fderiv ℝ (Φ.kernel h) z‖ ^ 2 ≤ (C1 * (1 + ‖z‖) ^ 1 * Φ.kernel h z) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  unfold fisherKernel
  rw [div_le_iff₀ hp]
  calc gradNormSq (Φ.kernel h) z ≤ 2 * d * ‖fderiv ℝ (Φ.kernel h) z‖ ^ 2 := gradNormSq_le _ _
    _ ≤ 2 * d * (C1 * (1 + ‖z‖) ^ 1 * Φ.kernel h z) ^ 2 := by gcongr
    _ = 2 * d * C1 ^ 2 * ((1 + ‖z‖) ^ 2 * Φ.kernel h z) * Φ.kernel h z := by ring

theorem exists_fisherKernel_bound (hh : 0 < h) : ∃ B : ℝ, ∀ z, fisherKernel Φ h z ≤ B := by
  have hK : IsCompact ({h} : Set ℝ) := isCompact_singleton
  have hsub : ({h} : Set ℝ) ⊆ Set.Ioi 0 := by simpa using hh
  obtain ⟨C, hC0, hC⟩ := exists_fisherKernel_le (Φ := Φ) hK hsub
  obtain ⟨W, hW⟩ := Φ.weight_le 2 hK hsub
  exact ⟨C * W, fun z => (hC h rfl z).trans (mul_le_mul_of_nonneg_left (hW h rfl z) hC0)⟩

theorem integrable_fisherKernel (hh : 0 < h) : Integrable (fisherKernel Φ h) := by
  have hK : IsCompact ({h} : Set ℝ) := isCompact_singleton
  have hsub : ({h} : Set ℝ) ⊆ Set.Ioi 0 := by simpa using hh
  obtain ⟨C, hC0, hC⟩ := exists_fisherKernel_le (Φ := Φ) hK hsub
  refine ((Φ.weight_integrable 2 hh).const_mul C).mono'
    (continuous_fisherKernel hh).aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (fisherKernel_nonneg hh z)]
  exact hC h rfl z

variable (m : Measure (EvolutionAmbientState d)) [IsFiniteMeasure m]

theorem integrable_fisherComp_translate (hh : 0 < h) (c : Fin d ⊕ Fin d)
    (y : EvolutionAmbientState d) :
    Integrable (fun a => fisherComp Φ h c (y - a)) m := by
  obtain ⟨B, hB⟩ := exists_fisherKernel_bound (Φ := Φ) hh
  refine Integrable.of_bound (C := B) ((continuous_fisherComp hh c).comp
    (continuous_const.sub continuous_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun a => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (fisherComp_nonneg hh c _)]
  exact (fisherComp_le hh c _).trans (hB _)

theorem integrable_fisherKernel_translate (hh : 0 < h) (y : EvolutionAmbientState d) :
    Integrable (fun a => fisherKernel Φ h (y - a)) m := by
  obtain ⟨B, hB⟩ := exists_fisherKernel_bound (Φ := Φ) hh
  refine Integrable.of_bound (C := B) ((continuous_fisherKernel hh).comp
    (continuous_const.sub continuous_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun a => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (fisherKernel_nonneg hh _)]
  exact hB _

omit [IsFiniteMeasure m] in
theorem fisherSmooth_nonneg (hh : 0 < h) (y : EvolutionAmbientState d) :
    0 ≤ fisherSmooth Φ h m y :=
  integral_nonneg fun _ => fisherKernel_nonneg hh _

theorem fisherSmooth_eq_sum (hh : 0 < h) (y : EvolutionAmbientState d) :
    fisherSmooth Φ h m y = ∑ c, ∫ a, fisherComp Φ h c (y - a) ∂m := by
  unfold fisherSmooth
  simp only [fisherKernel_eq_sum]
  exact integral_finsetSum _ fun c _ => integrable_fisherComp_translate m hh c y

variable {f : EvolutionAmbientState d → ℝ} {Cf : ℝ}

/-- Coordinatewise weighted Cauchy--Schwarz bound for the smoothed flux. -/
theorem sq_coordPartial_smoothWeighted_le (hh : 0 < h) (hf : Measurable f)
    (hfb : ∀ a, |f a| ≤ Cf) (c : Fin d ⊕ Fin d) (y : EvolutionAmbientState d) :
    coordPartial c (smoothWeighted Φ h f m) y ^ 2 ≤
      Cf ^ 2 * (∫ a, fisherComp Φ h c (y - a) ∂m) * smoothDensity Φ h m y := by
  have hdc : coordPartial c (smoothWeighted Φ h f m) y =
      ∫ a, f a * coordPartial c (Φ.kernel h) (y - a) ∂m := by
    rw [coordPartial_smoothWeighted hh hf hfb c]; rfl
  have hG := (Φ.isBoundedSmooth hh).coordPartial c
  obtain ⟨C0, hC0⟩ := hG.bound_zero
  have hu : Integrable (fun a => f a * coordPartial c (Φ.kernel h) (y - a)) m := by
    simpa using integrable_weighted_translate hG.contDiff.continuous hf hfb hC0 m y
  have hcont : Continuous (fun a => coordPartial c (Φ.kernel h) (y - a)) :=
    (continuous_coordPartial (Φ.contDiff hh) c).comp (continuous_const.sub continuous_id)
  have hfisher := integrable_fisherComp_translate (Φ := Φ) m hh c y
  have hpt : ∀ a, (f a * coordPartial c (Φ.kernel h) (y - a)) ^ 2 / Φ.kernel h (y - a) =
      f a ^ 2 * fisherComp Φ h c (y - a) := fun a => by
    simp only [fisherComp, mul_pow, mul_div_assoc]
  have hq : Integrable (fun a => (f a * coordPartial c (Φ.kernel h) (y - a)) ^ 2 /
      Φ.kernel h (y - a)) m := by
    simp only [hpt]
    refine (hfisher.const_mul (Cf ^ 2)).mono' ?_ (Filter.Eventually.of_forall fun a => ?_)
    · exact ((hf.pow_const 2).aestronglyMeasurable).mul
        ((continuous_fisherComp hh c).comp
          (continuous_const.sub continuous_id)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (fisherComp_nonneg hh c _))]
      refine mul_le_mul_of_nonneg_right ?_ (fisherComp_nonneg hh c _)
      rw [← sq_abs (f a)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hfb a) 2
  have hcs := sq_integral_le_mul (fun a => Φ.pos hh (y - a)) (integrable_kernel_translate Φ m hh y)
    hu hq
  rw [hdc]
  refine hcs.trans (mul_le_mul_of_nonneg_right ?_ (smoothDensity_nonneg Φ m hh y))
  simp only [hpt]
  rw [← integral_const_mul]
  refine integral_mono (by simpa [hpt] using hq) (hfisher.const_mul _) fun a => ?_
  refine mul_le_mul_of_nonneg_right ?_ (fisherComp_nonneg hh c _)
  rw [← sq_abs (f a)]
  exact pow_le_pow_left₀ (abs_nonneg _) (hfb a) 2

/-- The Fisher-type bound `|D (fm)_h|² ≤ ‖f‖²_∞ r ∫ |DΦ_h|²/Φ_h (y - y') dm`. -/
theorem gradNormSq_smoothWeighted_le (hh : 0 < h) (hf : Measurable f)
    (hfb : ∀ a, |f a| ≤ Cf) (y : EvolutionAmbientState d) :
    gradNormSq (smoothWeighted Φ h f m) y ≤
      Cf ^ 2 * smoothDensity Φ h m y * fisherSmooth Φ h m y := by
  unfold gradNormSq
  rw [fisherSmooth_eq_sum m hh, Finset.mul_sum]
  refine (Finset.sum_le_sum fun c _ => sq_coordPartial_smoothWeighted_le m hh hf hfb c y).trans
    (le_of_eq (Finset.sum_congr rfl fun c _ => by ring))

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

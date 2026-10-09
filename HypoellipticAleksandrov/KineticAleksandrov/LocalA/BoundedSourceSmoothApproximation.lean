module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceCutoffSequence
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Bounded smooth source approximation for actual finite measures

The approximation works for singular finite Borel measures as well as volume. A continuous
clamp preserves the source bound; smooth approximation and compact cutoffs preserve positivity.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open Set Filter MeasureTheory Function
open scoped Topology

/-- Nonnegative bounded Borel data have uniformly bounded positive smooth approximants
supported in an open domain, converging almost everywhere for the supplied finite measure. -/
theorem exists_boundedSourceSmoothApproximation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (U : Set E) (hU : IsOpen U)
    (F : E → ℝ) (hF : Measurable F) (M : ℝ) (hM : 0 ≤ M)
    (hFb : ∀ x, 0 ≤ F x ∧ F x ≤ M) (hFz : ∀ x ∉ U, F x = 0) :
    ∃ f : ℕ → E → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (f n) ∧ HasCompactSupport (f n) ∧ tsupport (f n) ⊆ U) ∧
      (∀ n x, 0 ≤ f n x ∧ f n x ≤ M + 2) ∧
      ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (F x)) := by
  classical
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hεp (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hε1 (n : ℕ) : ε n ≤ 1 := by
    dsimp [ε]
    rw [div_le_iff₀ (by positivity)]
    simp
  have hε0 : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
  have hmem : MemLp F 1 μ := by
    apply memLp_one_iff_integrable.mpr
    refine ⟨hF.aestronglyMeasurable, ?_⟩
    apply HasFiniteIntegral.of_bounded (C := M)
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hFb x).1]
      exact (hFb x).2
  have hex (n : ℕ) := hmem.exist_eLpNorm_sub_le (by norm_num) le_rfl (hεp n)
  choose g hgc hgs hge using hex
  have hnorm : Tendsto (fun n => eLpNorm (g n - F) 1 μ) atTop (𝓝 0) := by
    have hεe : Tendsto (fun n => ENNReal.ofReal (ε n)) atTop (𝓝 0) := by
      simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hε0
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hεe
      (fun _ => zero_le) (fun n => ?_)
    rw [eLpNorm_sub_comm]
    exact hge n
  obtain ⟨σ, hσ, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hnorm
    ).exists_seq_tendsto_ae
  let G (n : ℕ) (x : E) : ℝ := max 0 (min M (g (σ n) x))
  have hGc (n : ℕ) : Continuous (G n) :=
    continuous_const.max (continuous_const.min (hgs (σ n)).continuous)
  have hGb (n : ℕ) (x : E) : 0 ≤ G n x ∧ G n x ≤ M := by
    exact ⟨le_max_left _ _, max_le hM (min_le_left _ _)⟩
  have hGsup (n : ℕ) : support (G n) ⊆ support (g (σ n)) := by
    intro x hx
    contrapose! hx
    simp only [Function.mem_support, not_not] at hx ⊢
    change max 0 (min M (g (σ n) x)) = 0
    rw [hx, min_eq_right hM, max_self]
  have hGcompact (n : ℕ) : HasCompactSupport (G n) :=
    (hgc (σ n)).mono (hGsup n)
  have hsmooth (n : ℕ) := (hGc n).exists_contDiff_approx (⊤ : ℕ∞)
    (ε := fun _ => ε n) continuous_const (fun _ => hεp n)
  choose q hqs hqe hqsub using hsmooth
  have hqcompact (n : ℕ) : HasCompactSupport (q n) := (hGcompact n).mono (hqsub n)
  have hχex (n : ℕ) := exists_smooth_cutoff (hGcompact n) isOpen_univ
    (subset_univ (tsupport (G n)))
  choose χ hχs hχc hχsub hχb hχone using hχex
  obtain ⟨ρ, hρs, hρb, hρone⟩ := exists_boundedSourceCutoffSequence U hU
  let f (n : ℕ) (x : E) := ρ n x * (q n x + ε n * χ n x)
  refine ⟨f, ?_, ?_, ?_⟩
  · intro n
    exact ⟨(hρs n).1.mul ((hqs n).add (contDiff_const.mul (hχs n))),
      (hρs n).2.1.mul_right, tsupport_mul_subset_left.trans (hρs n).2.2⟩
  · intro n x
    have hdist : |q n x - G n x| < ε n := by
      simpa only [Real.dist_eq] using hqe n x
    have hpos : 0 ≤ q n x + ε n * χ n x := by
      by_cases hx : x ∈ tsupport (G n)
      · rw [hχone n x hx, mul_one]
        have hh := (abs_lt.mp hdist).1
        linarith [(hGb n x).1]
      · have hz : q n x = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          exact fun h => hx (closure_mono (hqsub n) h)
        rw [hz, zero_add]
        exact mul_nonneg (hεp n).le (hχb n x).1
    have hup : q n x + ε n * χ n x ≤ M + 2 := by
      have hh := (abs_lt.mp hdist).2
      have hχe := mul_le_mul_of_nonneg_left (hχb n x).2 (hεp n).le
      linarith [(hGb n x).2, hε1 n]
    exact ⟨mul_nonneg (hρb n x).1 hpos,
      (mul_le_mul_of_nonneg_right (hρb n x).2 hpos).trans (by simpa using hup)⟩
  · filter_upwards [hae] with x hx
    by_cases hxU : x ∈ U
    · have hGlim : Tendsto (fun n => G n x) atTop (𝓝 (F x)) := by
        have hMlim : Tendsto (fun _ : ℕ => M) atTop (𝓝 M) := tendsto_const_nhds
        have h0lim : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
        have hh := h0lim.max (hMlim.min hx)
        simpa only [G, min_eq_right (hFb x).2, max_eq_right (hFb x).1] using hh
      have herror : Tendsto (fun n => q n x - G n x) atTop (𝓝 0) := by
        apply squeeze_zero_norm (fun n => ?_) hε0
        simpa only [Real.norm_eq_abs, Real.dist_eq] using (hqe n x).le
      have hqlim : Tendsto (fun n => q n x) atTop (𝓝 (F x)) := by
        have hh := herror.add hGlim
        simpa only [zero_add, sub_add_cancel] using hh
      have hχlim : Tendsto (fun n => ε n * χ n x) atTop (𝓝 0) := by
        apply squeeze_zero (fun n => mul_nonneg (hεp n).le (hχb n x).1)
          (fun n => by simpa using
            mul_le_mul_of_nonneg_left (hχb n x).2 (hεp n).le) hε0
      have hlim := hqlim.add hχlim
      have heq : (fun n => f n x) =ᶠ[atTop] (fun n => q n x + ε n * χ n x) := by
        filter_upwards [hρone x hxU] with n hn
        simp only [f, hn, one_mul]
      have hlim' : Tendsto (fun n => q n x + ε n * χ n x) atTop (𝓝 (F x)) := by
        simpa only [add_zero] using hlim
      exact hlim'.congr' heq.symm
    · have hz (n : ℕ) : f n x = 0 := by
        have hρz : ρ n x = 0 := image_eq_zero_of_notMem_tsupport
          (fun h => hxU ((hρs n).2.2 h))
        simp only [f, hρz, zero_mul]
      simpa only [hz, hFz x hxU] using (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

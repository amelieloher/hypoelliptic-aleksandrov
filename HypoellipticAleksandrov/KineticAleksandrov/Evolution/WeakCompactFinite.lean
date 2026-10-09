module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.WeakCompactLocal
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Bounded weak subsequences for finite measures

Weak Hilbert convergence preserves pointwise bounds by testing measurable sets.
Density of simple functions then gives convergence against all integrable tests.
-/

@[expose] public section

open Filter MeasureTheory Topology
open scoped NNReal ENNReal

namespace HypoellipticAleksandrov.KineticAleksandrov

private theorem integral_mul_toLp {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  simp only [hx, hy, RCLike.inner_apply, starRingEnd_apply, star_trivial, mul_comm]

private theorem pairing_lipschitz {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} {C : ℝ≥0}
    (hf : AEStronglyMeasurable f μ) (hb : ∀ᵐ x ∂μ, |f x| ≤ C) :
    LipschitzWith C (fun ψ : Lp ℝ 1 μ => ∫ x, f x * ψ x ∂μ) := by
  apply LipschitzWith.of_dist_le_mul
  intro ψ φ
  have hψ : Integrable (fun x => f x * ψ x) μ :=
    (memLp_one_iff_integrable.mp (Lp.memLp ψ)).bdd_mul hf hb
  have hφ : Integrable (fun x => f x * φ x) μ :=
    (memLp_one_iff_integrable.mp (Lp.memLp φ)).bdd_mul hf hb
  rw [dist_eq_norm, ← integral_sub hψ hφ, dist_eq_norm, L1.norm_eq_integral_norm,
    ← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans ?_
  apply integral_mono_ae
  · exact (hψ.sub hφ).norm
  · exact ((memLp_one_iff_integrable.mp (Lp.memLp (ψ - φ))).norm).const_mul _
  filter_upwards [hb, Lp.coeFn_sub ψ φ] with x hx he
  rw [he, Pi.sub_apply, ← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

private theorem extend_integral_tests {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ]
    (v : ℕ → α → ℝ) (u : α → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hv : ∀ j, AEStronglyMeasurable (v j) μ)
    (hb : ∀ j, ∀ᵐ x ∂μ, |v j x| ≤ C)
    (hu : AEStronglyMeasurable u μ) (hub : ∀ᵐ x ∂μ, |u x| ≤ C)
    (ht : ∀ ψ : α → ℝ, MemLp ψ 2 μ →
      Tendsto (fun j => ∫ x, v j x * ψ x ∂μ) atTop (nhds (∫ x, u x * ψ x ∂μ))) :
    ∀ ψ : α → ℝ, Integrable ψ μ →
      Tendsto (fun j => ∫ x, v j x * ψ x ∂μ) atTop (nhds (∫ x, u x * ψ x ∂μ)) := by
  let K : ℝ≥0 := ⟨C, hC⟩
  let F (j : ℕ) (ψ : Lp ℝ 1 μ) := ∫ x, v j x * ψ x ∂μ
  let G (ψ : Lp ℝ 1 μ) := ∫ x, u x * ψ x ∂μ
  have hF : ∀ j, LipschitzWith K (F j) := fun j => pairing_lipschitz (hv j) (hb j)
  have hG : LipschitzWith K G := pairing_lipschitz hu hub
  have hclosed : IsClosed {ψ : Lp ℝ 1 μ | Tendsto (fun j => F j ψ) atTop (nhds (G ψ))} :=
    (LipschitzWith.uniformEquicontinuous F K hF).equicontinuous.isClosed_setOfPred_tendsto
      hG.continuous
  have hall : ∀ ψ : Lp ℝ 1 μ, Tendsto (fun j => F j ψ) atTop (nhds (G ψ)) := by
    intro ψ
    refine (Lp.simpleFunc.denseRange (E := ℝ) (μ := μ) (p := 1) (by simp)).induction_on
      (p := fun φ => Tendsto (fun j => F j φ) atTop (nhds (G φ))) ψ hclosed ?_
    intro f
    let φ : Lp ℝ 1 μ := f
    let s := Lp.simpleFunc.toSimpleFunc f
    have hs : MemLp s 2 μ := s.memLp_of_finite_measure_preimage 2
      (fun _ _ => measure_lt_top _ _)
    have he : (s : α → ℝ) =ᵐ[μ] φ := Lp.simpleFunc.toSimpleFunc_eq_toFun f
    have hvEq : ∀ j, (∫ x, v j x * s x ∂μ) = F j φ := by
      intro j
      apply integral_congr_ae
      filter_upwards [he] with x hx
      rw [hx]
    have huEq : (∫ x, u x * s x ∂μ) = G φ := by
      apply integral_congr_ae
      filter_upwards [he] with x hx
      rw [hx]
    simpa only [hvEq, huEq] using ht s hs
  intro ψ hψ
  let φ := (memLp_one_iff_integrable.mpr hψ).toLp ψ
  have he : ⇑φ =ᵐ[μ] ψ := MemLp.coeFn_toLp _
  have hvEq : ∀ j, F j φ = ∫ x, v j x * ψ x ∂μ := by
    intro j
    apply integral_congr_ae
    filter_upwards [he] with x hx
    rw [hx]
  have huEq : G φ = ∫ x, u x * ψ x ∂μ := by
    apply integral_congr_ae
    filter_upwards [he] with x hx
    rw [hx]
  simpa only [hvEq, huEq] using hall φ

/-- Uniformly bounded measurable functions on a finite separable measure space
have a subsequence converging against every integrable test. -/
theorem exists_finite_bounded_weak_subsequence
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    [MeasureTheory.IsSeparable μ]
    (v : ℕ → α → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hv : ∀ j, AEStronglyMeasurable (v j) μ)
    (hb : ∀ j, ∀ᵐ x ∂μ, |v j x| ≤ C) :
    ∃ (u : α → ℝ) (ν : ℕ → ℕ), StrictMono ν ∧ AEStronglyMeasurable u μ ∧
      (∀ᵐ x ∂μ, |u x| ≤ C) ∧
      ∀ ψ : α → ℝ, Integrable ψ μ →
        Tendsto (fun j => ∫ x, v (ν j) x * ψ x ∂μ)
          atTop (nhds (∫ x, u x * ψ x ∂μ)) := by
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let hm (j : ℕ) : MemLp (v j) 2 μ := MemLp.of_bound (hv j) C (hb j)
  let V (j : ℕ) : Lp ℝ 2 μ := (hm j).toLp (v j)
  let R : ℝ := ‖(memLp_const C : MemLp (fun _ : α => C) 2 μ).toLp (fun _ => C)‖
  have hV : ∀ j, ‖V j‖ ≤ R := by
    intro j
    change ‖(hm j).toLp (v j)‖ ≤ R
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(hm j).coeFn_toLp, (memLp_const C
      : MemLp (fun _ : α => C) 2 μ).coeFn_toLp, hb j] with x hx hy hb'
    simpa only [hx, hy, Real.norm_eq_abs, abs_of_nonneg hC] using hb'
  obtain ⟨u, ν, hν, ht⟩ := exists_hilbert_weak_subsequence V R hV
  have htest : ∀ ψ : α → ℝ, MemLp ψ 2 μ →
      Tendsto (fun j => ∫ x, v (ν j) x * ψ x ∂μ)
        atTop (nhds (∫ x, u x * ψ x ∂μ)) := by
    intro ψ hψ
    have h := ht (hψ.toLp ψ)
    have hu : inner ℝ u (hψ.toLp ψ) = ∫ x, u x * ψ x ∂μ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hψ.coeFn_toLp] with x hx
      simp only [hx, RCLike.inner_apply, starRingEnd_apply, star_trivial, mul_comm]
    simpa only [V, integral_mul_toLp, hu] using h
  have hui : Integrable (u : α → ℝ) μ := (Lp.memLp u).integrable (by norm_num)
  have hset (s : Set α) (hs : MeasurableSet s) :
      Tendsto (fun j => ∫ x in s, v (ν j) x ∂μ)
        atTop (nhds (∫ x in s, u x ∂μ)) := by
    have h := htest (s.indicator (fun _ => (1 : ℝ)))
      ((memLp_const 1).indicator hs)
    simpa only [← Set.indicator_mul_right, mul_one, integral_indicator hs] using h
  have hupper : ∀ᵐ x ∂μ, u x ≤ C := by
    apply ae_le_of_forall_setIntegral_le hui (integrable_const C)
    intro s hs _
    apply le_of_tendsto (hset s hs)
    filter_upwards with j
    apply integral_mono_ae
    · exact ((hm (ν j)).integrable (by norm_num)).integrableOn
    · exact integrable_const C
    exact (ae_restrict_of_ae (hb (ν j))).mono fun x hx => (le_abs_self _).trans hx
  have hlower : ∀ᵐ x ∂μ, -C ≤ u x := by
    apply ae_le_of_forall_setIntegral_le (integrable_const (-C)) hui
    intro s hs _
    apply ge_of_tendsto (hset s hs)
    filter_upwards with j
    apply integral_mono_ae
    · exact integrable_const (-C)
    · exact ((hm (ν j)).integrable (by norm_num)).integrableOn
    exact (ae_restrict_of_ae (hb (ν j))).mono fun x hx => (abs_le.mp hx).1
  have hub : ∀ᵐ x ∂μ, |u x| ≤ C := by
    filter_upwards [hlower, hupper] with x hx hy
    exact abs_le.mpr ⟨hx, hy⟩
  exact ⟨u, ν, hν, Lp.aestronglyMeasurable u, hub,
    extend_integral_tests (fun j => v (ν j)) u C hC (fun j => hv (ν j))
      (fun j => hb (ν j)) (Lp.aestronglyMeasurable u) hub htest⟩

end HypoellipticAleksandrov.KineticAleksandrov

module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Energy.Abstract
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Energy.DatumBeta
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothed.SlicePackage

/-!
# The energy inequality for a smoothing datum

The energy inequality: for the smoothed density `ρ`, flux `J` and
coefficient `β_h` of an abstract smoothing datum `(Γ', B_t)` (the smoothed Green measure), the
hypotheses of
`EnergySetting` hold, by the smoothing estimates (`Smoothing/*`) and the smoothed equation
(`Smoothed/*`).
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory
open scoped MatrixOrder

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ} {δ : ℝ} {η : ℝ → ℝ} {lam Lam : ℝ}

theorem exists_abs_deriv_le (hη : IsMollifier δ η) : ∃ B : ℝ, 0 ≤ B ∧ ∀ t, |deriv η t| ≤ B := by
  have hc : HasCompactSupport η :=
    HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) δ) fun t ht => by
      apply hη.support
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at ht
      exact ht.le
  have hcont : Continuous (deriv η) := hη.contDiff.continuous_deriv (by simp)
  obtain ⟨B, hB⟩ := hcont.bounded_above_of_compact_support hc.deriv
  exact ⟨max B 0, le_max_right _ _, fun t => (Real.norm_eq_abs _ ▸ hB t).trans (le_max_left _ _)⟩

variable {Bt : ℝ → EvolutionAmbientState d → PDE.Mat d}
  {Γ' : Measure (ℝ × EvolutionAmbientState d)}

/-- `|∂_τ ρ| ≤ ‖η'‖_∞ · (Γ'_2)_h`, the domination used for the time term. -/
theorem abs_deriv_smoothedDensity_le (Φ : SmoothingKernelFamily d lam) (hη : IsMollifier δ η)
    {h : ℝ} (hh : 0 < h) [IsFiniteMeasure Γ'] {B : ℝ} (hB : ∀ t, |deriv η t| ≤ B) (τ : ℝ)
    (y : EvolutionAmbientState d) :
    |deriv (fun τ' => smoothedDensity Φ η h Γ' τ' y) τ| ≤
      B * smoothDensity Φ h (Γ'.map Prod.snd) y := by
  rw [(hasDerivAt_smoothedDensity Φ hη hh τ y).deriv]
  have hcont : Continuous fun a : ℝ × EvolutionAmbientState d => Φ.kernel h (y - a.2) :=
    (Φ.contDiff hh).continuous.comp (continuous_const.sub continuous_snd)
  obtain ⟨C, hC⟩ := abs_kernel_sub_le Φ hh
  have hint : Integrable (fun a : ℝ × EvolutionAmbientState d => B * Φ.kernel h (y - a.2)) Γ' :=
    Integrable.of_bound (hcont.const_mul B).aestronglyMeasurable (|B| * C) (by
      refine Filter.Eventually.of_forall fun a => ?_
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul le_rfl (hC y a.2) (abs_nonneg _) (abs_nonneg _))
  have := norm_integral_le_of_norm_le
    (f := fun a : ℝ × EvolutionAmbientState d => deriv η (τ - a.1) * Φ.kernel h (y - a.2)) hint
    (Filter.Eventually.of_forall fun a => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Φ.pos hh _)]
    exact mul_le_mul_of_nonneg_right (hB _) (Φ.pos hh _).le)
  rw [Real.norm_eq_abs] at this
  refine this.trans (le_of_eq ?_)
  rw [integral_const_mul]
  congr 1
  unfold smoothDensity
  exact (integral_map (f := fun y' => Φ.kernel h (y - y')) measurable_snd.aemeasurable
    ((Φ.contDiff hh).continuous.comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable).symm

variable (Φ : SmoothingKernelFamily d lam) {h : ℝ}

/-- Measurability of the `y`-partials of `β_h` in `(τ, y)`. -/
theorem measurable_partial_smoothedBeta (hη : IsMollifier δ η) [IsFiniteMeasure Γ']
    (hmarg : Γ'.map Prod.fst ≤ volume)
    (hBm : ∀ i j, Measurable fun q : ℝ × EvolutionAmbientState d => Bt q.1 q.2 i j)
    (hBb : ∀ t y i j, |Bt t y i j| ≤ Lam) (hLam : 0 ≤ Lam)
    (hBl : ∀ t y, lam • (1 : PDE.Mat d) ≤ Bt t y ∧ Bt t y ≤ Lam • (1 : PDE.Mat d))
    (hh : 0 < h) (i j : Fin d) (c : Fin d ⊕ Fin d) :
    Measurable fun p : ℝ × EvolutionAmbientState d =>
      coordPartial c (fun y => smoothedBeta Φ η Bt Lam h Γ' p.1 y i j) p.2 := by
  classical
  set U : Set (ℝ × EvolutionAmbientState d) := {p | 0 < smoothedDensity Φ η h Γ' p.1 p.2}
    with hUdef
  have hU : IsOpen U :=
    isOpen_lt continuous_const (contDiff_smoothedDensity Φ (Γ' := Γ') hη hh).continuous
  have hβ := contDiffOn_smoothedBeta Φ hη hmarg hBm hBb hLam hBl hh i j
  have hg : Measurable fun p : ℝ × EvolutionAmbientState d =>
      fderiv ℝ (fun p : ℝ × EvolutionAmbientState d =>
        smoothedBeta Φ η Bt Lam h Γ' p.1 p.2 i j) p (0, coordDir c) :=
    measurable_fderiv_apply_const ℝ _ _
  have key : (fun p : ℝ × EvolutionAmbientState d =>
      coordPartial c (fun y => smoothedBeta Φ η Bt Lam h Γ' p.1 y i j) p.2) = fun p =>
      if p ∈ U then fderiv ℝ (fun p : ℝ × EvolutionAmbientState d =>
        smoothedBeta Φ η Bt Lam h Γ' p.1 p.2 i j) p (0, coordDir c) else 0 := by
    funext p
    by_cases hp : p ∈ U
    · simp only [hp, ite_true]
      exact coordPartial_slice_of_differentiableAt
        (g := fun τ y => smoothedBeta Φ η Bt Lam h Γ' τ y i j)
        ((hβ.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hp)) c
    · simp only [hp, ite_false]
      have hm : averagedSlice η p.1 Γ' = 0 := by
        by_contra hne
        have := isFiniteMeasure_averagedSlice (τ := p.1) hη hmarg
        exact hp (smoothDensity_pos Φ _ hh hne p.2)
      have hc : (fun y => smoothedBeta Φ η Bt Lam h Γ' p.1 y i j) =
          fun _ => (lam • (1 : PDE.Mat d)) i j := by
        funext y
        unfold smoothedBeta
        rw [hm, smoothCoefficient_of_eq_zero]
      rw [hc]
      simp [coordPartial]
  rw [key]
  exact Measurable.ite hU.measurableSet hg measurable_const

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

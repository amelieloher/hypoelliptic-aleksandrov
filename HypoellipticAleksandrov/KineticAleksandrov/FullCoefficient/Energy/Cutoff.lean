module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Energy.IBP
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# A velocity-only cut-off

The energy inequality: the cut-off `ζ_R(v) = ζ(v / R)` depends on the
velocity alone, so that the position derivatives of `ζ_R` vanish and the transport term is
integrated slice-wise.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory Filter Topology

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

/-- The velocity-only cut-off `y = (v, z) ↦ ζ(v / R)`. -/
def velocityCutoff (b : ContDiffBump (0 : PDE.Vec d)) (R : ℝ) (y : EvolutionAmbientState d) : ℝ :=
  b (R⁻¹ • y.1)

/-- The standard bump used for the cut-off. -/
def cutoffBump (d : ℕ) : ContDiffBump (0 : PDE.Vec d) := ⟨1, 2, one_pos, one_lt_two⟩

variable (b : ContDiffBump (0 : PDE.Vec d))

theorem contDiff_bump : ContDiff ℝ (⊤ : ℕ∞) b := b.contDiff

theorem contDiff_velocityCutoff (R : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (velocityCutoff b R) :=
  (contDiff_bump b).comp
    (contDiff_fst.const_smul R⁻¹ : ContDiff ℝ (⊤ : ℕ∞) fun y : EvolutionAmbientState d =>
      R⁻¹ • y.1)

theorem velocityCutoff_nonneg (R : ℝ) (y : EvolutionAmbientState d) : 0 ≤ velocityCutoff b R y :=
  b.nonneg

theorem velocityCutoff_le_one (R : ℝ) (y : EvolutionAmbientState d) : velocityCutoff b R y ≤ 1 :=
  b.le_one

theorem abs_velocityCutoff_le (R : ℝ) (y : EvolutionAmbientState d) :
    |velocityCutoff b R y| ≤ 1 := by
  rw [abs_of_nonneg (velocityCutoff_nonneg b R y)]
  exact velocityCutoff_le_one b R y

theorem tendsto_velocityCutoff (y : EvolutionAmbientState d) :
    Tendsto (fun n : ℕ => velocityCutoff b ((n : ℝ) + 1) y) atTop (𝓝 1) := by
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ • y.1) atTop (𝓝 ((0 : ℝ) • y.1)) :=
    (tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)).smul_const _
  rw [zero_smul] at h1
  have h2 := (b.continuous.tendsto 0).comp h1
  rw [show b 0 = 1 from b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)] at h2
  exact h2

theorem coordPartial_velocityCutoff_inr (R : ℝ) (i : Fin d) (y : EvolutionAmbientState d) :
    coordPartial (Sum.inr i) (velocityCutoff b R) y = 0 := by
  have hd : HasFDerivAt (velocityCutoff b R)
      ((fderiv ℝ b (R⁻¹ • y.1)).comp (R⁻¹ • ContinuousLinearMap.fst ℝ (PDE.Vec d) (PDE.Vec d))) y :=
    ((contDiff_bump b).differentiable (by simp) _).hasFDerivAt.comp y
      ((hasFDerivAt_fst).const_smul R⁻¹)
  rw [coordPartial, hd.fderiv]
  simp [coordDir]

/-- A bound on the derivative of the bump. -/
theorem exists_fderiv_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖fderiv ℝ b x‖ ≤ M := by
  have hc : HasCompactSupport (fderiv ℝ b) := b.hasCompactSupport.fderiv ℝ
  have hcont : Continuous (fderiv ℝ b) := (contDiff_bump b).continuous_fderiv (by simp)
  obtain ⟨M, hM⟩ := hcont.bounded_above_of_compact_support hc
  exact ⟨max M 0, le_max_right _ _, fun x => (hM x).trans (le_max_left _ _)⟩

theorem abs_coordPartial_velocityCutoff_le {M : ℝ} (hM : ∀ x, ‖fderiv ℝ b x‖ ≤ M) {R : ℝ}
    (hR : 0 < R) (i : Fin d) (y : EvolutionAmbientState d) :
    |coordPartial (Sum.inl i) (velocityCutoff b R) y| ≤ M / R := by
  have hd : HasFDerivAt (velocityCutoff b R)
      ((fderiv ℝ b (R⁻¹ • y.1)).comp (R⁻¹ • ContinuousLinearMap.fst ℝ (PDE.Vec d) (PDE.Vec d))) y :=
    ((contDiff_bump b).differentiable (by simp) _).hasFDerivAt.comp y
      ((hasFDerivAt_fst).const_smul R⁻¹)
  rw [coordPartial, hd.fderiv, ← Real.norm_eq_abs]
  simp only [coordDir, ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.coe_fst', map_smul, norm_smul, Real.norm_eq_abs]
  have h1 : ‖fderiv ℝ b (R⁻¹ • y.1) (Pi.single i 1)‖ ≤ M * ‖(Pi.single i 1 : PDE.Vec d)‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _))
  have h2 : ‖(Pi.single i 1 : PDE.Vec d)‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  rw [abs_of_pos (inv_pos.2 hR)]
  calc R⁻¹ * ‖fderiv ℝ b (R⁻¹ • y.1) (Pi.single i 1)‖ ≤ R⁻¹ * (M * 1) :=
        mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h2
          ((norm_nonneg _).trans (hM 0)))) (inv_pos.2 hR).le
    _ = M / R := by ring

/-- `ζ_R` is supported where `‖v‖ ≤ 2R`-ish: here for the bump of radius `rOut`. -/
theorem abs_velocityCutoff_mul_le (R : ℝ) (hR : 0 < R) (i : Fin d) (y : EvolutionAmbientState d) :
    |y.1 i * velocityCutoff b R y| ≤ b.rOut * R := by
  by_cases hs : velocityCutoff b R y = 0
  · rw [hs, mul_zero, abs_zero]
    exact mul_nonneg (b.rIn_pos.le.trans b.rIn_lt_rOut.le) hR.le
  · have hmem : R⁻¹ • y.1 ∈ Metric.ball (0 : PDE.Vec d) b.rOut := by
      have h0 : R⁻¹ • y.1 ∈ Function.support b := hs
      rw [b.support_eq] at h0
      simpa using h0
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR)] at hmem
    have hi : |y.1 i| ≤ ‖y.1‖ := by
      simpa using norm_le_pi_norm y.1 i
    have h3 : ‖y.1‖ < b.rOut * R := by
      have := (inv_mul_lt_iff₀ hR).1 hmem
      linarith
    rw [abs_mul, abs_of_nonneg (velocityCutoff_nonneg b R y)]
    calc |y.1 i| * velocityCutoff b R y ≤ |y.1 i| * 1 :=
          mul_le_mul_of_nonneg_left (velocityCutoff_le_one b R y) (abs_nonneg _)
      _ ≤ b.rOut * R := by linarith

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

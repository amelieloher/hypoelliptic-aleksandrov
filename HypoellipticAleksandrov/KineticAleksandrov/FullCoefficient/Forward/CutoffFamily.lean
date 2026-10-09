module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Forward.Cutoff
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.UniquenessMeasure

/-!
# The product cut-off family

The admissible test functions: for `R ≥ 1` the cut-off `ψ_R(v, z) = ζ(v/R) ζ(z/R²)` is smooth and
compactly supported, equals one on `{|v| ≤ R, |z| ≤ R²}`, and has velocity partials `O(1/R)`,
second velocity partials `O(1/R)` and transport error `v · ∇_z ψ_R = O(1/R)`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open Set Metric

variable {d : ℕ}

/-- The family of product cut-offs with uniform `1/R` derivative bounds. -/
theorem exists_cutoff_family :
    ∃ (M : ℝ) (ψ : ℝ → EvolutionAmbientState d → ℝ), 0 ≤ M ∧ ∀ R : ℝ, 1 ≤ R →
      ContDiff ℝ (⊤ : ℕ∞) (ψ R) ∧ HasCompactSupport (ψ R) ∧ (∀ y, 0 ≤ ψ R y ∧ ψ R y ≤ 1) ∧
      (∀ y, ‖y.1‖ ≤ R → ‖y.2‖ ≤ R ^ 2 → ψ R y = 1) ∧
      (∀ i y, |velocityPartial i (ψ R) y| ≤ M / R) ∧
      (∀ i j y, |velocityPartial i (velocityPartial j (ψ R)) y| ≤ M / R) ∧
      (∀ i y, |y.1 i * positionPartial i (ψ R) y| ≤ M / R) := by
  obtain ⟨ζ, hζ, hζc, hζV, hζ01, hζ1⟩ := SectionTwo.exists_smooth_cutoff
    (isCompact_closedBall (0 : PDE.Vec d) 1) (isOpen_ball (x := (0 : PDE.Vec d)) (ε := 2))
    (closedBall_subset_ball (by norm_num : (1 : ℝ) < 2))
  obtain ⟨M, hM0, hM1, hM2⟩ := exists_bump_bounds hζ hζc
  have hz0 : ∀ x : PDE.Vec d, 2 ≤ ‖x‖ → ζ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => by
      have := hζV h
      rw [mem_ball_zero_iff] at this
      linarith)
  refine ⟨2 * M, fun R y => ζ (R⁻¹ • y.1) * ζ ((R ^ 2)⁻¹ • y.2), by positivity, ?_⟩
  intro R hR
  have hR0 : 0 < R := by linarith
  have hR2 : 0 < R ^ 2 := by positivity
  set a : PDE.Vec d → ℝ := fun v => ζ (R⁻¹ • v) with ha
  set b : PDE.Vec d → ℝ := fun z => ζ ((R ^ 2)⁻¹ • z) with hb
  have hasm : ContDiff ℝ (⊤ : ℕ∞) a := hζ.comp (contDiff_const_smul _)
  have hbsm : ContDiff ℝ (⊤ : ℕ∞) b := hζ.comp (contDiff_const_smul _)
  have hadiff : Differentiable ℝ a := hasm.differentiable (by simp)
  have hbdiff : Differentiable ℝ b := hbsm.differentiable (by simp)
  have hnorm : ∀ (c : ℝ) (x : PDE.Vec d), 0 < c → ‖c • x‖ = c * ‖x‖ := fun c x hc => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (fun y : EvolutionAmbientState d => a y.1 * b y.2) :=
    (hasm.comp contDiff_fst).mul (hbsm.comp contDiff_snd)
  refine ⟨hψ, ?_, fun y => ⟨mul_nonneg (hζ01 _).1 (hζ01 _).1,
    by nlinarith [(hζ01 (R⁻¹ • y.1)).1, (hζ01 (R⁻¹ • y.1)).2, (hζ01 ((R ^ 2)⁻¹ • y.2)).1,
      (hζ01 ((R ^ 2)⁻¹ • y.2)).2]⟩, ?_, ?_, ?_, ?_⟩
  · refine HasCompactSupport.intro ((isCompact_closedBall (0 : PDE.Vec d) (2 * R)).prod
      (isCompact_closedBall (0 : PDE.Vec d) (2 * R ^ 2))) ?_
    intro y hy
    simp only [mem_prod, mem_closedBall_zero_iff, not_and_or, not_le] at hy
    rcases hy with hy | hy
    · have : a y.1 = 0 := hz0 _ (by
        rw [hnorm _ _ (inv_pos.2 hR0), inv_mul_eq_div, le_div_iff₀ hR0]; linarith)
      show a y.1 * b y.2 = 0
      rw [this, zero_mul]
    · have : b y.2 = 0 := hz0 _ (by
        rw [hnorm _ _ (inv_pos.2 hR2), inv_mul_eq_div, le_div_iff₀ hR2]; linarith)
      show a y.1 * b y.2 = 0
      rw [this, mul_zero]
  · intro y h1 h2
    have e1 : ζ (R⁻¹ • y.1) = 1 := hζ1 _ (by
      rw [mem_closedBall_zero_iff, hnorm _ _ (inv_pos.2 hR0), inv_mul_le_iff₀ hR0]; linarith)
    have e2 : ζ ((R ^ 2)⁻¹ • y.2) = 1 := hζ1 _ (by
      rw [mem_closedBall_zero_iff, hnorm _ _ (inv_pos.2 hR2), inv_mul_le_iff₀ hR2]; linarith)
    show a y.1 * b y.2 = 1
    simp only [ha, hb, e1, e2, mul_one]
  · intro i y
    rw [velocityPartial_mul_split a b hadiff hbdiff]
    rw [ha]
    rw [fderiv_comp_const_smul' ζ R⁻¹ _ _ (hζ.differentiable (by simp) _)]
    rw [abs_mul, abs_mul, abs_of_pos (inv_pos.2 hR0)]
    have := hM1 (R⁻¹ • y.1) i
    have h2 : |ζ ((R ^ 2)⁻¹ • y.2)| ≤ 1 := by
      rw [abs_of_nonneg (hζ01 _).1]; exact (hζ01 _).2
    calc R⁻¹ * |fderiv ℝ ζ (R⁻¹ • y.1) (Pi.single i 1)| * |ζ ((R ^ 2)⁻¹ • y.2)|
        ≤ R⁻¹ * M * 1 := by gcongr
      _ ≤ 2 * M / R := by rw [mul_one, inv_mul_eq_div]; gcongr; linarith
  · intro i j y
    rw [velocityPartial_velocityPartial_mul_split a b hasm hbdiff]
    have hinner : (fun v => fderiv ℝ a v (Pi.single j 1)) =
        fun v => R⁻¹ * fderiv ℝ ζ (R⁻¹ • v) (Pi.single j 1) := by
      funext v
      rw [ha]
      exact fderiv_comp_const_smul' ζ R⁻¹ v _ (hζ.differentiable (by simp) _)
    have hηd : Differentiable ℝ (fun x : PDE.Vec d => fderiv ℝ ζ x (Pi.single j 1)) :=
      (contDiff_fderiv_apply hζ _).differentiable (by simp)
    have hcomp : Differentiable ℝ (fun v : PDE.Vec d =>
        fderiv ℝ ζ (R⁻¹ • v) (Pi.single j 1)) := fun v =>
      (hηd (R⁻¹ • v)).comp v ((differentiableAt_id).const_smul R⁻¹)
    rw [hinner, fderiv_const_mul (hcomp y.1) R⁻¹]
    simp only [smul_apply, smul_eq_mul]
    rw [fderiv_comp_const_smul' (fun x : PDE.Vec d => fderiv ℝ ζ x (Pi.single j 1)) R⁻¹ _ _
      (hηd _)]
    have := hM2 (R⁻¹ • y.1) i j
    have h2 : |ζ ((R ^ 2)⁻¹ • y.2)| ≤ 1 := by
      rw [abs_of_nonneg (hζ01 _).1]; exact (hζ01 _).2
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (inv_pos.2 hR0)]
    calc R⁻¹ * (R⁻¹ * |fderiv ℝ (fun x : PDE.Vec d => fderiv ℝ ζ x (Pi.single j 1))
          (R⁻¹ • y.1) (Pi.single i 1)|) * |ζ ((R ^ 2)⁻¹ • y.2)|
        ≤ R⁻¹ * (R⁻¹ * M) * 1 := by gcongr
      _ ≤ R⁻¹ * (2 * M) := by
        have : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR
        have h3 : R⁻¹ * M ≤ 2 * M := by nlinarith
        rw [mul_one]
        exact mul_le_mul_of_nonneg_left h3 (inv_nonneg.2 hR0.le)
      _ = 2 * M / R := by ring
  · intro i y
    rw [positionPartial_mul_split a b hadiff hbdiff, hb]
    rw [fderiv_comp_const_smul' ζ (R ^ 2)⁻¹ _ _ (hζ.differentiable (by simp) _)]
    by_cases ha0 : a y.1 = 0
    · rw [ha0]
      simp only [zero_mul, mul_zero, abs_zero]
      positivity
    · have hlt : ‖R⁻¹ • y.1‖ < 2 := by
        by_contra h
        exact ha0 (hz0 _ (not_lt.1 h))
      rw [hnorm _ _ (inv_pos.2 hR0)] at hlt
      have hy1 : ‖y.1‖ < 2 * R := by
        rw [inv_mul_eq_div, div_lt_iff₀ hR0] at hlt
        exact hlt
      have hyi : |y.1 i| ≤ 2 * R := by
        have := norm_le_pi_norm y.1 i
        rw [Real.norm_eq_abs] at this
        exact this.trans hy1.le
      have h1 := hM1 ((R ^ 2)⁻¹ • y.2) i
      have ha1 : |a y.1| ≤ 1 := by
        rw [ha, abs_of_nonneg (hζ01 _).1]; exact (hζ01 _).2
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (inv_pos.2 hR2)]
      calc |y.1 i| * (|a y.1| * ((R ^ 2)⁻¹ *
            |fderiv ℝ ζ ((R ^ 2)⁻¹ • y.2) (Pi.single i 1)|))
          ≤ (2 * R) * (1 * ((R ^ 2)⁻¹ * M)) := by gcongr
        _ = 2 * M / R := by field_simp

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2ProfileSolver

/-! # The internally proved Appendix C profile in dimensions at least two -/

@[expose] public section

noncomputable section

open scoped MatrixOrder

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- The source profile with global measurable ellipticity and its pointwise equation. -/
theorem profile_ge_two (d : ℕ) (hd : 2 ≤ d)
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ lam Lam c C : ℝ,
      ∃ A : (PDE.Vec d × PDE.Vec d) → PDE.Mat d,
      ∃ H : (PDE.Vec d × PDE.Vec d) → ℝ,
        0 < lam ∧ lam ≤ Lam ∧ 0 < c ∧ 0 < C ∧
        (∀ i k, Measurable (fun q => A q i k)) ∧
        (∀ q, lam • (1 : PDE.Mat d) ≤ A q ∧
          A q ≤ Lam • (1 : PDE.Mat d)) ∧
        H 0 = 0 ∧
        ContDiffOn ℝ (⊤ : ℕ∞) H ({0}ᶜ) ∧
        (∀ r : ℝ, 0 < r → ∀ q,
          H (r ^ 3 • q.1, r • q.2) = Real.rpow r alpha * H q) ∧
        (∀ q, c * Real.rpow
          (Real.rpow (PDE.vecNormSq q.1 + (PDE.vecNormSq q.2) ^ 3) (1 / 6)) alpha
          ≤ H q ∧ H q ≤ C * Real.rpow
          (Real.rpow (PDE.vecNormSq q.1 + (PDE.vecNormSq q.2) ^ 3) (1 / 6)) alpha) ∧
        (∀ q, q ≠ 0 →
          matrixContraction (A q)
            (fun i k => fderiv ℝ
              (fun z => fderiv ℝ H z (0, Pi.single k 1)) q (0, Pi.single i 1)) =
            PDE.vecDot q.2 (fun i => fderiv ℝ H q (Pi.single i 1, 0))) ∧
        (∀ q, q ≠ 0 →
          PDE.vecEuclideanNorm (fun i => fderiv ℝ H q (0, Pi.single i 1)) ≤
            C * Real.rpow
              (Real.rpow (PDE.vecNormSq q.1 + (PDE.vecNormSq q.2) ^ 3) (1 / 6))
              (alpha - 1)) := by
  obtain ⟨C₀, sigma, R, lam, Lam, A, hC₀, hsigma, hR2, hlam, hlamLam,
    hmeas, helliptic, hsolve⟩ := exists_geometricProfile_elliptic_solver d hd alpha ha ha1
  have hR : 0 < R := lt_trans (by norm_num) hR2
  let H : XV d → ℝ := geometricProfile alpha C₀ sigma R
  obtain ⟨c, C₁, hc, _, hcompare⟩ := geometricProfile_comparison (d := d)
    alpha C₀ sigma R ha hC₀.le hsigma hR
  obtain ⟨C₂, hC₂, hgrad⟩ := geometricProfile_velocity_gradient_bound (d := d)
    alpha C₀ sigma R hsigma hR
  let C := max C₁ C₂
  have hC : 0 < C := lt_of_lt_of_le hC₂ (le_max_right _ _)
  refine ⟨lam, Lam, c, C, A, H, hlam, hlamLam, hc, hC, hmeas, helliptic,
    geometricProfile_zero d alpha C₀ sigma R ha,
    geometricProfile_smooth_off_origin alpha C₀ sigma R hsigma hR, ?_, ?_, ?_, ?_⟩
  · exact fun r hr q => geometricProfile_homogeneous alpha C₀ sigma R r hr q
  · intro q
    change c * Real.rpow (rho q) alpha ≤ H q ∧ H q ≤ C * Real.rpow (rho q) alpha
    refine ⟨(hcompare q).1, (hcompare q).2.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (rho_nonneg q) _)
  · exact hsolve
  · intro q hq
    change PDE.vecEuclideanNorm (dv H q) ≤ C * Real.rpow (rho q) (alpha - 1)
    exact (hgrad q hq).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Real.rpow_nonneg (rho_nonneg q) _))

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

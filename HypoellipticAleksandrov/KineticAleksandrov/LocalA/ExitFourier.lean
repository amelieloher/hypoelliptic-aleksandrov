module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitFourierShortTime
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitFourierOptimization

/-! # Optimized Fourier decay of the full local ball exit measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory SectionTwo Parabolic

/-- The actual exit measure retains time and velocity and has the source's optimized decay. -/
theorem ballExit_fourier_decay
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (d : ℕ) (hd : 1 ≤ d) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
        (v₀ : PDE.Vec d) (R : ℝ) (hR : 0 < R)
        (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t}),
      P.1.velocity ∈ PDE.euclideanBall v₀ (3 * R / 4) →
      T.1 - P.1.time = R ^ 2 / 8 →
      let ν := ballExit hH hLE hd hlam hLam B hB v₀ hR P T
      ∀ ξ : PDE.Vec d,
        ((exitFourier ν ξ).variation univ).toReal ≤
          C * Real.exp (-c * (R ^ 3 * PDE.vecEuclideanNorm ξ) ^ (1 / 3 : ℝ)) := by
  obtain ⟨C₀, c₀, hC₀, hc₀, htwo⟩ :=
    ballExit_fourier_two_exponentials hH hLE d hd lam Lam hlam hLam
  let c := c₀ / 16
  let A := 2 * C₀ + 1
  have hc : 0 < c := div_pos hc₀ (by norm_num)
  have hA : 1 ≤ A := by dsimp only [A]; linarith only [hC₀]
  have hec : 1 ≤ Real.exp c := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hc.le
  have hCf : 2 * C₀ ≤ A * Real.exp c := by
    calc
      2 * C₀ ≤ A := by dsimp only [A]; linarith
      _ ≤ A * Real.exp c := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hec (zero_le_one.trans hA)
  refine ⟨A * Real.exp c, c, mul_pos (zero_lt_one.trans_le hA) (Real.exp_pos _), hc, ?_⟩
  intro B hB v₀ R hR P T hv htime
  dsimp only
  intro ξ
  let n := PDE.vecEuclideanNorm ξ
  let y := (R ^ 3 * n) ^ (1 / 3 : ℝ)
  have hn : 0 ≤ n := PDE.vecEuclideanNorm_nonneg ξ
  by_cases hhigh : 1 ≤ R ^ 3 * n
  · let h := R ^ 2 / (16 * y)
    have hopt := exitFrequency_optimizing_step hR hn hhigh
    change 1 ≤ y ∧ 0 < h ∧ h < R ^ 2 / 8 ∧
      R ^ 2 / h = 16 * y ∧ h * n ^ (2 / 3 : ℝ) = y / 16 at hopt
    obtain ⟨hy, hh, hmax, hfirst, hsecond⟩ := hopt
    let H : {t : ℝ // P.1.time < t ∧ t < T.1} :=
      ⟨P.1.time + h, by constructor <;> linarith only [hh, hmax, htime]⟩
    have hdiff : H.1 - P.1.time = h := by dsimp only [H]; ring
    have hb := htwo B hB v₀ R hR P T H hv
      (by rw [hdiff]; exact hmax.le) ξ
    rw [hdiff] at hb
    have he := exitFrequency_exponential_pair hC₀.le hc₀.le (zero_le_one.trans hy)
      hfirst hsecond
    exact (hb.trans he).trans
      (mul_le_mul_of_nonneg_right hCf (Real.exp_pos (-(c₀ / 16) * y)).le)
  · have hy : y ≤ 1 := by
      simpa only [Real.one_rpow] using Real.rpow_le_rpow
        (mul_nonneg (pow_nonneg hR.le _) hn) (le_of_not_ge hhigh)
        (by norm_num : 0 ≤ (1 / 3 : ℝ))
    have hb := ENNReal.toReal_mono ENNReal.one_ne_top
      (ballExit_fourier_totalVariation_le_one hH hLE hd hlam hLam B hB v₀ hR P T ξ)
    simp only [ENNReal.toReal_one] at hb
    exact hb.trans (exitFrequency_low_bound hA hc.le hy)

end HypoellipticAleksandrov.KineticAleksandrov.LocalA

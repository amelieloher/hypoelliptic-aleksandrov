module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitFourierSplit

/-! # Uniform two-exponential bound for the actual full exit Fourier measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory SectionTwo Parabolic

/-- Combining loss and killed bounds only enlarges their structural prefactor. -/
theorem exitFourier_add_positive_bounds {A B X Y : ℝ} (hA : 0 ≤ A) (hY : 0 ≤ Y) :
    A * X + B * (X + Y) ≤ (A + B) * (X + Y) := by
  nlinarith only [mul_nonneg hA hY]

/-- Decreasing a nonnegative rate increases the corresponding exponential bound. -/
theorem exitFourier_exp_rate {a c x : ℝ} (hca : c ≤ a) (hx : 0 ≤ x) :
    Real.exp (-a * x) ≤ Real.exp (-c * x) :=
  Real.exp_le_exp.mpr (by
    simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_right hca hx))

/-- The actual exit Fourier measure has both short-time exponentials, uniformly over all data. -/
theorem ballExit_fourier_two_exponentials
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (d : ℕ) (hd : 1 ≤ d) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
        (v₀ : PDE.Vec d) (R : ℝ) (hR : 0 < R)
        (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t})
        (H : {t : ℝ // P.1.time < t ∧ t < T.1}),
      P.1.velocity ∈ PDE.euclideanBall v₀ (3 * R / 4) →
      H.1 - P.1.time ≤ R ^ 2 / 8 → ∀ ξ : PDE.Vec d,
      ((exitFourier (ballExit hH hLE hd hlam hLam B hB v₀ hR P T) ξ).variation univ).toReal ≤
        C * (Real.exp (-c * R ^ 2 / (H.1 - P.1.time)) +
          Real.exp (-c * (H.1 - P.1.time) * PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ))) := by
  obtain ⟨Cs, cs, hCs, hcs, hloss⟩ :=
    ballKernel_short_time_loss hH hLE d hd lam Lam hlam hLam
  obtain ⟨Ck, ck, hCk, hck, hkilled⟩ :=
    ballKernel_short_time_fourier hH hLE d hd lam Lam hlam hLam
  let c := min cs ck
  refine ⟨Cs + Ck, c, add_pos hCs hCk, lt_min hcs hck, ?_⟩
  intro B hB v₀ R hR P T H hv hsmall ξ
  let x := R ^ 2 / (H.1 - P.1.time)
  let y := (H.1 - P.1.time) * PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ)
  have hh : 0 < H.1 - P.1.time := sub_pos.mpr H.2.1
  have hx : 0 ≤ x := div_nonneg (sq_nonneg R) hh.le
  have hy : 0 ≤ y := mul_nonneg hh.le (Real.rpow_nonneg (PDE.vecEuclideanNorm_nonneg _) _)
  have hs := hloss B hB v₀ R hR P ⟨H.1, H.2.1⟩ hv hsmall
  have hk := hkilled B hB v₀ R hR P ⟨H.1, H.2.1⟩ hv hsmall ξ
    (ballEvolutionQuery P ⟨H.1, H.2.1⟩) rfl
  have es : -cs * R ^ 2 / (H.1 - P.1.time) = -cs * x := by dsimp only [x]; ring
  have ek : -ck * R ^ 2 / (H.1 - P.1.time) = -ck * x := by dsimp only [x]; ring
  have ey : -ck * (H.1 - P.1.time) * PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ) = -ck * y := by
    dsimp only [y]
    ring
  rw [es] at hs
  rw [ek, ey] at hk
  have hs' := hs.trans (mul_le_mul_of_nonneg_left
    (exitFourier_exp_rate (min_le_left cs ck) hx) hCs.le)
  have hk' := hk.trans (mul_le_mul_of_nonneg_left
    (add_le_add (exitFourier_exp_rate (min_le_right cs ck) hx)
      (exitFourier_exp_rate (min_le_right cs ck) hy)) hCk.le)
  have hb := (ballExit_fourier_short_strip_bound hH hLE hd hlam hLam B hB v₀ hR
    P T H ξ).trans (add_le_add hs' hk')
  have he := exitFourier_add_positive_bounds (B := Ck) (X := Real.exp (-c * x))
    hCs.le (Real.exp_pos (-c * y)).le
  have ee : -c * R ^ 2 / (H.1 - P.1.time) = -c * x := by dsimp only [x]; ring
  have ef : -c * (H.1 - P.1.time) * PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ) = -c * y := by
    dsimp only [y]
    ring
  rw [ee, ef]
  exact hb.trans he

end HypoellipticAleksandrov.KineticAleksandrov.LocalA

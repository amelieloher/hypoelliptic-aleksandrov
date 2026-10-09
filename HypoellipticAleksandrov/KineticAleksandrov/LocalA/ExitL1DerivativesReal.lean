module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitL1DerivativesBounds
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitL1InversionReal

/-! # Derivative contraction under the real-density projection -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic SectionTwo

/-- The real-part projection is a contraction in the complex norm. -/
theorem norm_exitRealPart_le_one : ‖exitRealPart‖ ≤ 1 := by
  apply exitRealPart.opNorm_le_bound (by norm_num)
  intro z
  simp only [exitRealPart, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    Complex.reCLM_apply, Complex.norm_real, one_mul]
  exact Complex.abs_re_le_norm z

/-- Projection does not increase any derivative of the actual smooth inverse. -/
theorem ballExitL1Density_derivative_le
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)
    (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t})
    (hv : P.1.velocity ∈ PDE.euclideanBall v₀ (3 * R / 4))
    (hT : T.1 - P.1.time = R ^ 2 / 8) (j : ℕ) (y : PDE.Vec d) :
    let ν := ballExit hH hLE hd hlam hLam B hB v₀ hR P T
    ‖iteratedFDeriv ℝ j (exitL1Density ν) y‖ ≤
      ‖iteratedFDeriv ℝ j (exitL1Inversion ν) y‖ := by
  dsimp only
  let ν := ballExit hH hLE hd hlam hLam B hB v₀ hR P T
  let L := exitRealPart.compLpL 1 (exitMarginal ν)
  have hs := ballExitL1Inversion_contDiff hH hLE hd hlam hLam B hB v₀ hR P T hv hT
  have he := L.iteratedFDeriv_comp_left
    ((hs.of_le (by simp : (j : WithTop ℕ∞) ≤ (⊤ : ℕ∞))).contDiffAt (x := y)) le_rfl
  change ‖iteratedFDeriv ℝ j (L ∘ exitL1Inversion ν) y‖ ≤ _
  rw [he]
  have hL : ‖L‖ ≤ 1 := exitRealPart.norm_compLpL_le.trans norm_exitRealPart_le_one
  exact (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans
    (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hL (norm_nonneg (iteratedFDeriv ℝ j (exitL1Inversion ν) y)))

end HypoellipticAleksandrov.KineticAleksandrov.LocalA

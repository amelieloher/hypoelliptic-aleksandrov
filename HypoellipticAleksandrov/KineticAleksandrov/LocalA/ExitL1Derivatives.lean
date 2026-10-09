module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitL1Inversion
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-! # All derivatives of the same exit-marginal inverse Fourier function -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic SectionTwo

/-- Every derivative is computed from the same inverse, rather than independent witnesses. -/
theorem ballExitL1Inversion_iteratedFDeriv
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)
    (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t})
    (hv : P.1.velocity ∈ PDE.euclideanBall v₀ (3 * R / 4))
    (hT : T.1 - P.1.time = R ^ 2 / 8) (j : ℕ) (y : PDE.Vec d) :
    let ν := ballExit hH hLE hd hlam hLam B hB v₀ hR P T
    iteratedFDeriv ℝ j (exitL1Inversion ν) y = ((2 * Real.pi) ^ d)⁻¹ •
      VectorFourier.fourierIntegral
        (E := ContinuousMultilinearMap ℝ (fun _ : Fin j => PDE.Vec d)
          (Lp ℂ 1 (exitMarginal ν))) Real.fourierChar volume
        (exitInversePairing d).toLinearMap₁₂
        (fun ξ => VectorFourier.fourierPowSMulRight
          (exitInversePairing d) (exitL1Fourier ν) ξ j) y := by
  dsimp only
  let ν := ballExit hH hLE hd hlam hLam B hB v₀ hR P T
  have hm (n : ℕ) (_hn : (n : ℕ∞) ≤ ⊤) :
      Integrable (fun ξ => ‖ξ‖ ^ n * ‖exitL1Fourier ν ξ‖) :=
    ballExitL1Fourier_integrable_moments hH hLE hd hlam hLam B hB v₀ hR P T hv hT n
  have hs := VectorFourier.contDiff_fourierIntegral (exitInversePairing d) hm
  change iteratedFDeriv ℝ j
    (fun y => ((2 * Real.pi) ^ d)⁻¹ •
      VectorFourier.fourierIntegral Real.fourierChar volume
        (exitInversePairing d).toLinearMap₁₂ (exitL1Fourier ν) y) y = _
  have hscalar := iteratedFDeriv_const_smul_apply' (𝕜 := ℝ)
    (a := (((2 * Real.pi) ^ d)⁻¹ : ℝ))
    (hf := (hs.of_le (by simp : (j : WithTop ℕ∞) ≤ (⊤ : ℕ∞))).contDiffAt (x := y))
  refine hscalar.trans ?_
  congr 1
  exact congrFun (VectorFourier.iteratedFDeriv_fourierIntegral (exitInversePairing d)
    hm (continuous_exitL1Fourier ν).aestronglyMeasurable
    (n := j) (by simp : (j : ℕ∞) ≤ ⊤)) y

end HypoellipticAleksandrov.KineticAleksandrov.LocalA

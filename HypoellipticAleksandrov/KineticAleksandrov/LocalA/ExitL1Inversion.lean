module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitL1FourierMoments
public import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-! # A single smooth inverse Fourier function in the exit-marginal `L¹` space -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic SectionTwo

/-- The native coordinate dot product, as a continuous bilinear map. -/
def exitDot (d : ℕ) : PDE.Vec d →L[ℝ] PDE.Vec d →L[ℝ] ℝ :=
  ∑ i : Fin d, (ContinuousLinearMap.proj i).smulRight (ContinuousLinearMap.proj i)

/-- This bilinear map uses the physical coordinate dot product. -/
theorem exitDot_apply {d : ℕ} (ξ y : PDE.Vec d) : exitDot d ξ y = PDE.vecDot ξ y := by
  simp [exitDot, PDE.vecDot]

/-- The bilinear Fourier pairing compensates for Mathlib's `2π` convention. -/
def exitInversePairing (d : ℕ) : PDE.Vec d →L[ℝ] PDE.Vec d →L[ℝ] ℝ :=
  (-(2 * Real.pi)⁻¹) • exitDot d

/-- The one inverse Fourier function used for every order of spatial differentiation. -/
def exitL1Inversion {d : ℕ} (ν : Measure (PDE.Vec d × TimeVelocity d)) [IsFiniteMeasure ν] :
    PDE.Vec d → Lp ℂ 1 (exitMarginal ν) :=
  fun y => ((2 * Real.pi) ^ d)⁻¹ •
    VectorFourier.fourierIntegral Real.fourierChar volume
      (exitInversePairing d).toLinearMap₁₂ (exitL1Fourier ν) y

/-- The actual Fourier decay yields one smooth `L¹`-valued inverse for all orders. -/
theorem ballExitL1Inversion_contDiff
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)
    (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t})
    (hv : P.1.velocity ∈ PDE.euclideanBall v₀ (3 * R / 4))
    (hT : T.1 - P.1.time = R ^ 2 / 8) :
    ContDiff ℝ (⊤ : ℕ∞)
      (exitL1Inversion (ballExit hH hLE hd hlam hLam B hB v₀ hR P T)) := by
  apply ContDiff.const_smul
  apply VectorFourier.contDiff_fourierIntegral
  intro n _hn
  exact ballExitL1Fourier_integrable_moments hH hLE hd hlam hLam B hB v₀ hR P T hv hT n

end HypoellipticAleksandrov.KineticAleksandrov.LocalA

module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitL1InversionTesting
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # A single real density with jointly measurable representatives -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic SectionTwo Reconstruction

/-- Projection to the real part, kept in the complex carrier for the downstream `L¹` API. -/
def exitRealPart : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.reCLM

/-- The one real inverse density in the complete complex `L¹` space. -/
def exitL1Density {d : ℕ} (ν : Measure (PDE.Vec d × TimeVelocity d)) [IsFiniteMeasure ν] :
    PDE.Vec d → Lp ℂ 1 (exitMarginal ν) :=
  fun y => exitRealPart.compLp (exitL1Inversion ν y)

/-- The real inverse has the same joint density representative at every position. -/
theorem ballExitL1Density_coe
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)
    (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t})
    (hv : P.1.velocity ∈ PDE.euclideanBall v₀ (3 * R / 4))
    (hT : T.1 - P.1.time = R ^ 2 / 8) (y : PDE.Vec d) :
    let ν := ballExit hH hLE hd hlam hLam B hB v₀ hR P T
    (exitL1Density ν y : TimeVelocity d → ℂ) =ᵐ[exitMarginal ν]
      fun z => (exitJointDensity ν (y, z) : ℂ) := by
  dsimp only
  let ν := ballExit hH hLE hd hlam hLam B hB v₀ hR P T
  have hi := ballExitL1Inversion_coe hH hLE hd hlam hLam B hB v₀ hR P T hv hT y
  change (exitRealPart.compLp (exitL1Inversion ν y) : TimeVelocity d → ℂ) =ᵐ[exitMarginal ν]
    fun z => (exitJointDensity ν (y, z) : ℂ)
  change (exitL1Inversion ν y : TimeVelocity d → ℂ) =ᵐ[exitMarginal ν]
    fun z => ((2 * Real.pi) ^ d)⁻¹ •
      vecInvIntegral (fun ξ => exitFourierRep ν ξ z) y at hi
  filter_upwards [exitRealPart.coeFn_compLp (exitL1Inversion ν y), hi] with z hz hz'
  rw [hz, hz']
  change Complex.ofReal (Complex.reCLM
    ((((2 * Real.pi) ^ d)⁻¹ : ℝ) • vecInvIntegral (fun ξ => exitFourierRep ν ξ z) y)) =
    Complex.ofReal (((2 * Real.pi) ^ d)⁻¹ *
      (vecInvIntegral (fun ξ => exitFourierRep ν ξ z) y).re)
  rw [map_smul]
  rfl

/-- One smooth real inverse function serves every derivative order simultaneously. -/
theorem ballExitL1Density_contDiff
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)
    (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t})
    (hv : P.1.velocity ∈ PDE.euclideanBall v₀ (3 * R / 4))
    (hT : T.1 - P.1.time = R ^ 2 / 8) :
    ContDiff ℝ (⊤ : ℕ∞)
      (exitL1Density (ballExit hH hLE hd hlam hLam B hB v₀ hR P T)) := by
  exact (exitRealPart.compLpL 1 _).contDiff.comp
    (ballExitL1Inversion_contDiff hH hLE hd hlam hLam B hB v₀ hR P T hv hT)

end HypoellipticAleksandrov.KineticAleksandrov.LocalA

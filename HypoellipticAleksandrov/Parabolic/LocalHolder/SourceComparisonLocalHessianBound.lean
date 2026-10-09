module

public import HypoellipticAleksandrov.Parabolic.WeakHessianDifferenceQuotientEnergy
public import HypoellipticAleksandrov.Parabolic.WeakDerivatives
public import HypoellipticAleksandrov.Coefficients.Ellipticity

/-! # Local Hessian energy for homogeneous replacement jets

The generic residual estimate is applied to the actual selected jet, with zero drift,
zero zeroth-order coefficient, and zero source.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open MeasureTheory Set
open scoped BigOperators MatrixOrder

/-- One constant controls Hessian energy of all homogeneous weak jets on the fixed collar. -/
theorem exists_local_homogeneous_hessian_constant {d : ℕ}
    (a T : ℝ) (O : Set (PDE.Vec d)) (hO : IsOpen O)
    (A : TimeVelocity d → PDE.Mat d)
    (hAm : AEStronglyMeasurable A (timeVelocityVolumeOn (Ioo a T ×ˢ O)))
    (hAs : ∀ t ∈ Ioo a T, ∀ i j, ContDiffOn ℝ 1 (fun y => A (t, y) i j) O)
    (lam Lam M : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam) (hM : 0 ≤ M)
    (hlo : ∀ z ∈ Ioo a T ×ˢ O, lam • (1 : PDE.Mat d) ≤ A z)
    (hhi : ∀ z ∈ Ioo a T ×ˢ O, A z ≤ Lam • (1 : PDE.Mat d))
    (hDA : ∀ z ∈ Ioo a T ×ˢ O, ∀ i j k,
      |spatialPartial k (fun y => A (z.1, y) i j) z.2| ≤ M)
    (η : PDE.Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hcη : HasCompactSupport η) (hsη : tsupport η ⊆ O)
    (hη0 : ∀ y, 0 ≤ η y) (hη1 : ∀ y, η y ≤ 1)
    (Kη : ℝ) (hKη : 0 ≤ Kη)
    (hdη : ∀ y ∈ O, ∀ i, |spatialPartial i η y| ≤ Kη)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hcζ : HasCompactSupport ζ) (hsζ : tsupport ζ ⊆ Ioo a T)
    (hζ0 : ∀ t, 0 ≤ ζ t) (hζ1 : ∀ t, ζ t ≤ 1)
    (Kζ : ℝ) (hKζ : 0 ≤ Kζ) (hdζ : ∀ t ∈ Ioo a T, |deriv ζ t| ≤ Kζ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ J : ParabolicW12Function d (Ioo a T ×ˢ O) 2,
      (∀ᵐ z ∂timeVelocityVolumeOn (Ioo a T ×ˢ O),
        J.timeDeriv z + ∑ i, ∑ j, A z i j * J.velocityHessian z j i = 0) →
      (∫ z in Ioo a T ×ˢ O,
        ζ z.1 * η z.2 ^ 2 * ∑ k, ∑ i, J.velocityHessian z k i ^ 2) ≤
      C * ((eLpNorm J.toFun 2 (timeVelocityVolumeOn (Ioo a T ×ˢ O))).toReal ^ 2 +
        ∑ j, (eLpNorm (fun z => J.velocityGrad z j) 2
          (timeVelocityVolumeOn (Ioo a T ×ˢ O))).toReal ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := exists_weakHessian_energy_le_of_residual
    d lam Lam M Kη Kζ hlam hlamLam hM hKη hKζ
  refine ⟨C, hC, ?_⟩
  intro J heq
  have hpde : ∀ᵐ z ∂timeVelocityVolumeOn (Ioo a T ×ˢ O),
      J.timeDeriv z + (∑ i, ∑ j, A z i j * J.velocityHessian z j i) +
        (∑ j, (0 : PDE.Vec d) j * J.velocityGrad z j) + 0 * J.toFun z = 0 := by
    filter_upwards [heq] with z hz
    simpa using hz
  have hb := hbound a T O hO A (fun _ => 0) (fun _ => 0)
    J.toFun J.timeDeriv (fun _ => 0) J.velocityGrad J.velocityHessian hAm
    aestronglyMeasurable_const aestronglyMeasurable_const hAs hlo hhi hDA
    (fun _ _ _ => by simpa using hM) (fun _ _ => by simpa using hM)
    J.memLp J.timeDeriv_memLp J.velocityGrad_memLp J.velocityHessian_memLp
    MemLp.zero' J.hasWeakTimeDeriv J.hasWeakVelocityPartialDeriv
    J.hasWeakVelocitySecondPartialDeriv hpde η hη hcη hsη hη0 hη1 hdη
    ζ hζ hcζ hsζ hζ0 hζ1 hdζ
  simpa using hb

end HypoellipticAleksandrov.Parabolic.LocalHolder

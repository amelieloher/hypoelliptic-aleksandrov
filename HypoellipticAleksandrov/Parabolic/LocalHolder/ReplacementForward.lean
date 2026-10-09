module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementContinuousBoundary
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonForward
public import HypoellipticAleksandrov.KineticAleksandrov.ClassicalInputs

/-! # The forward homogeneous replacement and sharp source comparison

Continuous boundary approximation and internal local energy regularity construct the
backward replacement. Time reflection gives the prescribed initial and lateral traces;
the signed comparison estimate gives the exact finite-horizon error bound.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Set
open scoped Matrix.Norms.Elementwise

/-- The planned forward replacement has the exact initial/lateral traces and source error. -/
theorem exists_parabolic_homogeneous_replacement
    (hLE : KineticAleksandrov.LiebermanEllipsoidDirichletStatement)
    {N : ℕ} (hN : 1 ≤ N) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : CoefficientField N) (hA : IsSmoothCoefficient A)
    (hs : IsSymmetricCoefficient A) (hlo : HasLowerEllipticity lam A)
    (hhi : HasUpperEllipticity Lam A)
    (a T : ℝ) (haT : a < T) (v₀ : PDE.Vec N) (r : ℝ) (hr : 0 < r)
    (w : TimeVelocity N → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hw : IsScalarC12On w (scalarParabolicOpenCylinder a T (PDE.euclideanBall v₀ r)))
    (hc : ContinuousOn w (scalarParabolicClosedCylinder a T (PDE.euclideanBall v₀ r)))
    (hf : ∀ z ∈ scalarParabolicOpenCylinder a T (PDE.euclideanBall v₀ r),
      |scalarTimeDerivative w z - matrixContraction (coefficientAt A z)
        (scalarSpatialHessian w z)| ≤ M) :
    ∃ v : TimeVelocity N → ℝ,
      IsScalarC12On v (scalarParabolicOpenCylinder a T (PDE.euclideanBall v₀ r)) ∧
      ContinuousOn v (scalarParabolicClosedCylinder a T (PDE.euclideanBall v₀ r)) ∧
      EqOn v w ((({a} : Set ℝ) ×ˢ closure (PDE.euclideanBall v₀ r)) ∪
        (Icc a T ×ˢ frontier (PDE.euclideanBall v₀ r))) ∧
      (∀ z ∈ scalarParabolicOpenCylinder a T (PDE.euclideanBall v₀ r),
        scalarTimeDerivative v z = matrixContraction (coefficientAt A z)
          (scalarSpatialHessian v z)) ∧
      ∀ z ∈ scalarParabolicClosedCylinder a T (PDE.euclideanBall v₀ r),
        |w z - v z| ≤ M * (T - a) := by
  let Ω := PDE.euclideanBall v₀ r
  let B := timeReflectedCoefficient A
  have hBs : IsSmoothCoefficient B := by
    have hR : ContDiff ℝ (⊤ : ℕ∞) (@timeReflection N) :=
      (contDiff_const.sub contDiff_fst).prodMk contDiff_snd
    exact hA.comp hR
  have hBl : HasLowerEllipticity lam B := fun t y => hlo (1 - t) y
  have hBu : HasUpperEllipticity Lam B := fun t y => hhi (1 - t) y
  have hwr : ContinuousOn (timeReflectedScalar w)
      (scalarParabolicClosedCylinder (1 - T) (1 - a) Ω) :=
    hc.comp continuous_timeReflection.continuousOn
      (fun z hz => (timeReflection_mem_closedCylinder_iff a T Ω z).mpr hz)
  obtain ⟨u, hu⟩ := exists_continuous_backward_homogeneous_replacement
    (lt_of_lt_of_le Nat.zero_lt_one hN) v₀ r hr (1 - T) (1 - a)
    (by linarith only [haT]) lam Lam hlam hLam B hBs hBl hBu
    (timeReflectedScalar w) hwr
  have hopen : MapsTo timeReflection (scalarParabolicOpenCylinder a T Ω)
      (scalarParabolicOpenCylinder (1 - T) (1 - a) Ω) := by
    intro z hz
    exact ⟨⟨by dsimp [timeReflection]; linarith only [hz.1.2],
      by dsimp [timeReflection]; linarith only [hz.1.1]⟩, hz.2⟩
  have hclosed : MapsTo timeReflection (scalarParabolicClosedCylinder a T Ω)
      (scalarParabolicClosedCylinder (1 - T) (1 - a) Ω) := by
    intro z hz
    exact ⟨⟨by dsimp [timeReflection]; linarith only [hz.1.2],
      by dsimp [timeReflection]; linarith only [hz.1.1]⟩, hz.2⟩
  let v := timeReflectedScalar u
  have hv12 : IsScalarC12On v (scalarParabolicOpenCylinder a T Ω) :=
    scalarC12On_mono (isScalarC12On_timeReflectedScalar hu.2.1) hopen
  have hvc : ContinuousOn v (scalarParabolicClosedCylinder a T Ω) :=
    hu.1.comp continuous_timeReflection.continuousOn hclosed
  have htrace : EqOn v w (({a} ×ˢ closure Ω) ∪ (Icc a T ×ˢ frontier Ω)) := by
    intro z hz
    rcases hz with hz | hz
    · have ht : z.1 = a := mem_singleton_iff.mp hz.1
      have he := hu.2.2.2.1 z.2 hz.2
      simpa only [v, timeReflectedScalar, timeReflection, ← ht, sub_sub_cancel,
        Prod.mk.eta] using he
    · have hrz : timeReflection z ∈ scalarParabolicLateralFace (1 - T) (1 - a) Ω :=
        ⟨⟨by dsimp [timeReflection]; linarith only [hz.1.2],
          by dsimp [timeReflection]; linarith only [hz.1.1]⟩, hz.2⟩
      have he := hu.2.2.2.2 (timeReflection z) hrz
      simpa only [v, timeReflectedScalar, timeReflection, sub_sub_cancel, Prod.mk.eta] using he
  have hve : ∀ z ∈ scalarParabolicOpenCylinder a T Ω,
      scalarTimeDerivative v z =
        matrixContraction (coefficientAt A z) (scalarSpatialHessian v z) := by
    intro z hz
    have he := hu.2.2.1 (timeReflection z) (hopen hz)
    simp only [scalarParabolicZeroOrderOperator_apply, PDE.vecDot, Pi.zero_apply,
      zero_mul, Finset.sum_const_zero, add_zero, B, timeReflectedCoefficient,
      timeReflection, sub_sub_cancel] at he
    rw [scalarTimeDerivative_timeReflectedScalar_C12 hu.2.1 (hopen hz),
      scalarSpatialHessian_timeReflectedScalar_C12]
    change -scalarTimeDerivative u (timeReflection z) =
      matrixContraction (A z.1 z.2) (scalarSpatialHessian u (timeReflection z))
    change scalarTimeDerivative u (timeReflection z) +
      matrixContraction (A z.1 z.2) (scalarSpatialHessian u (timeReflection z)) = 0 at he
    linarith only [he]
  refine ⟨v, hv12, hvc, htrace, hve, ?_⟩
  exact abs_forward_replacement_error_le_horizon (PDE.isOpen_euclideanBall v₀ r)
    (KineticAleksandrov.Occupation.isBounded_euclideanBall v₀ hr) haT A hA.continuous
    (KineticAleksandrov.Occupation.posSemidef_of_lower_loewner hlam hlo)
    w v hw hv12 hc hvc htrace hve M hM hf

end HypoellipticAleksandrov.Parabolic.LocalHolder

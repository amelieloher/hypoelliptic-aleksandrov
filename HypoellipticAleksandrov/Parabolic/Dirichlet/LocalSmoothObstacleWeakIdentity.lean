module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTime
public import HypoellipticAleksandrov.Parabolic.Dirichlet.WeakTestFunctionSobolevJet
public import HypoellipticAleksandrov.Parabolic.LocalCompactSupportIntegrationByParts

/-!
# Local smooth-obstacle weak identity

This module records the compactly supported spatial integration-by-parts
identity for a classical scalar obstacle on an arbitrary open spatial set.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace HypoellipticAleksandrov.Parabolic

private theorem spatialPartial_mul_local
    {d : ℕ} {D : Set (PDE.Vec d)} (hD : IsOpen D) (i : Fin d)
    {f g : PDE.Vec d → ℝ} (hf : ContDiffOn ℝ 1 f D)
    (hg : ContDiffOn ℝ 1 g D) {y : PDE.Vec d} (hy : y ∈ D) :
    spatialPartial i (fun x ↦ f x * g x) y =
      spatialPartial i f y * g y + f y * spatialPartial i g y := by
  rw [spatialPartial, fderiv_fun_mul
    ((hf.contDiffAt (hD.mem_nhds hy)).differentiableAt (by norm_num))
    ((hg.contDiffAt (hD.mem_nhds hy)).differentiableAt (by norm_num))]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    spatialPartial]
  ring

private theorem integrable_mul_of_right_compactSupport
    {d : ℕ} {D : Set (PDE.Vec d)} {f g : PDE.Vec d → ℝ}
    (hf : ContinuousOn f D) (hg : Continuous g)
    (hgcompact : HasCompactSupport g) (hgsupport : tsupport g ⊆ D) :
    Integrable (fun y ↦ f y * g y) := by
  have hcontinuous : ContinuousOn (fun y ↦ f y * g y) (tsupport g) :=
    (hf.mono hgsupport).mul hg.continuousOn
  have hon : IntegrableOn (fun y ↦ f y * g y) (tsupport g) :=
    hcontinuous.integrableOn_compact hgcompact
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hon
  exact (Function.support_mul_subset_right f g).trans (subset_tsupport g)

/-- The lower-order remainder in the generic reverse-time classical identity
is integrable against a bundled smooth compactly supported test function. -/
theorem integrableOn_reverseTimeClassicalRemainder_weakTest
    {d : ℕ} {D : Set (PDE.Vec d)} (hD : IsOpen D)
    (r₁ τ : ℝ)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (p : TimeVelocity d → ℝ)
    (ψ : PDE.WeakTestFunction D)
    (ha : ∀ i j : Fin d,
      ContDiffOn ℝ 1 (fun y ↦ a (r₁ - τ) y i j) D)
    (hb : ∀ j : Fin d,
      ContinuousOn (fun y ↦ b (r₁ - τ) y j) D)
    (hc : ContinuousOn (fun y ↦ c (r₁ - τ) y) D)
    (hp : IsScalarC12On p ({r₁ - τ} ×ˢ D)) :
    IntegrableOn
      (fun y ↦
        (-scalarTimeDerivative p (r₁ - τ, y)) * ψ y +
          (∑ j : Fin d,
            reverseTimeDivergenceDrift r₁ a b τ y j *
              scalarSpatialGradient p (r₁ - τ, y) j * ψ y) -
          c (r₁ - τ) y * p (r₁ - τ, y) * ψ y)
      D := by
  have hpair : Continuous (fun y : PDE.Vec d ↦ (r₁ - τ, y)) :=
    continuous_const.prodMk continuous_id
  have hpairMem : MapsTo (fun y : PDE.Vec d ↦ (r₁ - τ, y)) D
      ({r₁ - τ} ×ˢ D) := fun y hy ↦ ⟨Set.mem_singleton _, hy⟩
  have htime : ContinuousOn
      (fun y ↦ scalarTimeDerivative p (r₁ - τ, y)) D :=
    hp.continuousOn_scalarTimeDerivative.comp hpair.continuousOn hpairMem
  have hpvalue : ContinuousOn (fun y ↦ p (r₁ - τ, y)) D :=
    hp.continuousOn.comp hpair.continuousOn hpairMem
  have hgradient (j : Fin d) : ContinuousOn
      (fun y ↦ scalarSpatialGradient p (r₁ - τ, y) j) D :=
    ((continuous_apply j).comp_continuousOn hp.continuousOn_scalarSpatialGradient).comp
      hpair.continuousOn hpairMem
  have hcoeffPartial (i j : Fin d) : ContinuousOn
      (spatialPartial i (fun y ↦ a (r₁ - τ) y i j)) D := by
    exact ((ha i j).fderiv_of_isOpen hD (m := 0) (by norm_num)).clm_apply
      contDiffOn_const |>.continuousOn
  have hdivergence (j : Fin d) : ContinuousOn
      (fun y ↦ scalarSpatialCoefficientDivergence a (r₁ - τ, y) j) D := by
    unfold scalarSpatialCoefficientDivergence
    simpa only [spatialPartial] using
      (continuousOn_finset_sum Finset.univ fun i _ ↦ hcoeffPartial i j)
  have hdrift (j : Fin d) : ContinuousOn
      (fun y ↦ reverseTimeDivergenceDrift r₁ a b τ y j) D := by
    simpa only [reverseTimeDivergenceDrift,
      scalarSpatialCoefficientDivergence_reverseTimeCoefficient, reverseTimeMap_apply,
      reverseTimeVectorCoefficient_apply, Pi.sub_apply, Pi.sub_def] using (hdivergence j).sub (hb j)
  let amplitude : PDE.Vec d → ℝ := fun y ↦
    -scalarTimeDerivative p (r₁ - τ, y) +
      (∑ j : Fin d,
        reverseTimeDivergenceDrift r₁ a b τ y j *
          scalarSpatialGradient p (r₁ - τ, y) j) -
      c (r₁ - τ) y * p (r₁ - τ, y)
  have hamp : ContinuousOn amplitude D :=
    htime.neg.add
      (continuousOn_finset_sum Finset.univ fun j _ ↦ (hdrift j).mul (hgradient j)) |>.sub
        (hc.mul hpvalue)
  have hint : Integrable (fun y ↦ amplitude y * ψ y) :=
    integrable_mul_of_right_compactSupport hamp ψ.contDiff.continuous
      ψ.hasCompactSupport ψ.tsupport_subset
  apply hint.integrableOn.congr_fun
  · intro y _hy
    dsimp only [amplitude]
    ring_nf
    rw [Finset.sum_mul]
    ring_nf
  · exact hD.measurableSet

/-- Generic integrable predecessor: the reverse-time local spatial form of a
classical scalar field equals the negative original-time operator against each
bundled smooth compactly supported test function.  A source-facing obstacle
consumer must derive the stated lower-order remainder integrability. -/
theorem integral_reverseTimeClassicalResidual_weakTest_eq_neg_operator
    {d : ℕ} {D : Set (PDE.Vec d)} (hD : IsOpen D)
    (r₁ τ : ℝ)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ) (ell : TimeVelocity d → ℝ)
    (ψ : PDE.WeakTestFunction D)
    (ha : ∀ i j : Fin d, ContDiffOn ℝ 1 (fun y ↦ a (r₁ - τ) y i j) D)
    (hell : IsScalarC12On ell ({r₁ - τ} ×ˢ D))
    (hremainder : IntegrableOn (fun y ↦
      (-scalarTimeDerivative ell (r₁ - τ, y)) * ψ y +
        (∑ j : Fin d,
          reverseTimeDivergenceDrift r₁ a b τ y j *
            scalarSpatialGradient ell (r₁ - τ, y) j * ψ y) -
        c (r₁ - τ) y * ell (r₁ - τ, y) * ψ y) D) :
    (∫ y in D,
      (-scalarTimeDerivative ell (r₁ - τ, y)) * ψ y +
        (∑ i : Fin d, ∑ j : Fin d,
          a (r₁ - τ) y i j * scalarSpatialGradient ell (r₁ - τ, y) j *
            ψ.partialDeriv i y) +
        (∑ j : Fin d,
          reverseTimeDivergenceDrift r₁ a b τ y j *
            scalarSpatialGradient ell (r₁ - τ, y) j * ψ y) -
        c (r₁ - τ) y * ell (r₁ - τ, y) * ψ y ∂volume) =
      ∫ y in D,
        (-scalarParabolicZeroOrderOperator a b c ell (r₁ - τ, y)) * ψ y ∂volume := by
  let u : PDE.Vec d → ℝ := fun y ↦ ell (r₁ - τ, y)
  have hu2 : ContDiffOn ℝ 2 u D := by
    intro y hy
    exact (hell.spatialSlice_contDiffAt
      (show (r₁ - τ, y) ∈ ({r₁ - τ} ×ˢ D) from ⟨Set.mem_singleton _, hy⟩)).contDiffWithinAt
  have hgrad (j : Fin d) : ContDiffOn ℝ 1 (spatialPartial j u) D :=
    ContDiffOn.spatialPartial hu2 hD j
  have hpsi1 : ContDiffOn ℝ 1 ψ D := ψ.contDiff.contDiffOn.of_le (by simp)
  have hgradient_eq (y : PDE.Vec d) (j : Fin d) :
      scalarSpatialGradient ell (r₁ - τ, y) j = spatialPartial j u y := by
    rfl
  have hhessian_eq (y : PDE.Vec d) (hy : y ∈ D) (i j : Fin d) :
      scalarSpatialHessian ell (r₁ - τ, y) i j =
        spatialPartial i (spatialPartial j u) y := by
    have hdu : DifferentiableAt ℝ (fun x ↦ PDE.classicalGradient u x) y := by
      apply differentiableAt_pi.2
      intro k
      exact ((hu2.contDiffAt (hD.mem_nhds hy)).fderiv_right (m := 1) (by norm_num)).differentiableAt
        (by norm_num) |>.clm_apply (differentiableAt_const (c := PDE.basisVec k))
    unfold scalarSpatialHessian spatialPartial u
    rw [fderiv_pi (fun k ↦ (differentiableAt_pi.mp hdu) k)]
    rfl
  have hflux (i j : Fin d) :
      ContDiffOn ℝ 1
        (fun y ↦ a (r₁ - τ) y i j * scalarSpatialGradient ell (r₁ - τ, y) j) D := by
    simpa only [hgradient_eq] using (ha i j).mul (hgrad j)
  have hibp (i j : Fin d) :
      (∫ y in D,
        a (r₁ - τ) y i j * scalarSpatialGradient ell (r₁ - τ, y) j *
          ψ.partialDeriv i y ∂volume) =
        -∫ y in D,
          (spatialPartial i (fun x ↦ a (r₁ - τ) x i j) y *
              scalarSpatialGradient ell (r₁ - τ, y) j +
            a (r₁ - τ) y i j * scalarSpatialHessian ell (r₁ - τ, y) i j) *
            ψ y ∂volume := by
    have h := setIntegral_mul_spatialPartial_eq_neg_spatialPartial_mul_of_right
      D hD i
      (fun y ↦ a (r₁ - τ) y i j * scalarSpatialGradient ell (r₁ - τ, y) j)
      ψ (hflux i j) hpsi1 ψ.hasCompactSupport ψ.tsupport_subset
    calc
      _ = ∫ y in D,
          (a (r₁ - τ) y i j * scalarSpatialGradient ell (r₁ - τ, y) j) *
            spatialPartial i ψ y ∂volume := by
          apply setIntegral_congr_fun hD.measurableSet
          intro y _hy
          rfl
      _ = -∫ y in D,
          spatialPartial i
            (fun y ↦ a (r₁ - τ) y i j * scalarSpatialGradient ell (r₁ - τ, y) j) y *
            ψ y ∂volume := h
      _ = _ := by
        congr 1
        apply setIntegral_congr_fun hD.measurableSet
        intro y hy
        change spatialPartial i
          (fun x ↦ a (r₁ - τ) x i j * spatialPartial j u x) y * ψ y = _
        rw [spatialPartial_mul_local hD i (ha i j) (hgrad j) hy]
        rw [← hgradient_eq y j, ← hhessian_eq y hy i j]
  let p : PDE.Vec d → ℝ := fun y ↦
    ∑ i : Fin d, ∑ j : Fin d,
      a (r₁ - τ) y i j * scalarSpatialGradient ell (r₁ - τ, y) j *
        ψ.partialDeriv i y
  let q : PDE.Vec d → ℝ := fun y ↦
    ∑ i : Fin d, ∑ j : Fin d,
      -((spatialPartial i (fun x ↦ a (r₁ - τ) x i j) y *
          scalarSpatialGradient ell (r₁ - τ, y) j +
        a (r₁ - τ) y i j * scalarSpatialHessian ell (r₁ - τ, y) i j) * ψ y)
  let r : PDE.Vec d → ℝ := fun y ↦
    (-scalarTimeDerivative ell (r₁ - τ, y)) * ψ y +
      (∑ j : Fin d,
        reverseTimeDivergenceDrift r₁ a b τ y j *
          scalarSpatialGradient ell (r₁ - τ, y) j * ψ y) -
      c (r₁ - τ) y * ell (r₁ - τ, y) * ψ y
  have hpartialSupport (i : Fin d) : tsupport (spatialPartial i ψ) ⊆ D := by
    apply (closure_minimal ?_ (isClosed_tsupport ψ)).trans ψ.tsupport_subset
    intro y hy
    by_contra hnot
    apply hy
    unfold spatialPartial
    rw [fderiv_of_notMem_tsupport ℝ hnot]
    simp only [ContinuousLinearMap.zero_apply]
  have hpij (i j : Fin d) : Integrable (fun y ↦
      a (r₁ - τ) y i j * scalarSpatialGradient ell (r₁ - τ, y) j *
        ψ.partialDeriv i y) := by
    apply integrable_mul_of_right_compactSupport (f := fun y ↦
      a (r₁ - τ) y i j * scalarSpatialGradient ell (r₁ - τ, y) j)
      (g := spatialPartial i ψ) (hflux i j).continuousOn
    · exact (ψ.contDiff.continuous_fderiv (by norm_num)).clm_apply continuous_const
    · exact ψ.hasCompactSupport.fderiv_apply ℝ (PDE.basisVec i)
    · exact hpartialSupport i
  have hp : Integrable p :=
    integrable_finset_sum Finset.univ fun i _ ↦
      integrable_finset_sum Finset.univ fun j _ ↦ hpij i j
  have hcoeffPartial (i j : Fin d) : ContinuousOn
      (spatialPartial i (fun x ↦ a (r₁ - τ) x i j)) D := by
    exact ((ha i j).fderiv_of_isOpen hD (m := 0) (by norm_num)).clm_apply
      contDiffOn_const |>.continuousOn
  have hhessianContinuous (i j : Fin d) : ContinuousOn
      (fun y ↦ scalarSpatialHessian ell (r₁ - τ, y) i j) D := by
    have hentry : ContinuousOn (fun z ↦ scalarSpatialHessian ell z i j)
        ({r₁ - τ} ×ˢ D) :=
      (continuous_apply j).comp_continuousOn
        ((continuous_apply i).comp_continuousOn hell.continuousOn_scalarSpatialHessian)
    exact hentry.comp (continuous_const.prodMk continuous_id).continuousOn
      fun y hy ↦ ⟨Set.mem_singleton _, hy⟩
  have hqij (i j : Fin d) : Integrable (fun y ↦
      -((spatialPartial i (fun x ↦ a (r₁ - τ) x i j) y *
          scalarSpatialGradient ell (r₁ - τ, y) j +
        a (r₁ - τ) y i j * scalarSpatialHessian ell (r₁ - τ, y) i j) * ψ y)) := by
    apply (integrable_mul_of_right_compactSupport (g := ψ)
      (((hcoeffPartial i j).mul (hgrad j).continuousOn).add
        ((ha i j).continuousOn.mul (hhessianContinuous i j)))
      ψ.contDiff.continuous ψ.hasCompactSupport ψ.tsupport_subset).neg
  have hq : Integrable q :=
    integrable_finset_sum Finset.univ fun i _ ↦
      integrable_finset_sum Finset.univ fun j _ ↦ hqij i j
  have hpq : (∫ y in D, p y ∂volume) = ∫ y in D, q y ∂volume := by
    dsimp only [p, q]
    rw [integral_finset_sum Finset.univ (fun i _ ↦
      integrable_finset_sum Finset.univ fun j _ ↦ (hpij i j).integrableOn)]
    simp_rw [integral_finset_sum Finset.univ (fun j _ ↦ (hpij _ j).integrableOn)]
    rw [integral_finset_sum Finset.univ (fun i _ ↦
      integrable_finset_sum Finset.univ fun j _ ↦ (hqij i j).integrableOn)]
    simp_rw [integral_finset_sum Finset.univ (fun j _ ↦ (hqij _ j).integrableOn),
      integral_neg, hibp]
  have hcommon : (∫ x in D, r x + p x ∂volume) =
      ∫ x in D, r x + q x ∂volume := by
    rw [integral_add hremainder hp.integrableOn, integral_add hremainder hq.integrableOn, hpq]
  calc
    _ = ∫ y in D, r y + p y ∂volume := by
      apply setIntegral_congr_fun hD.measurableSet
      intro y _hy
      dsimp only [r, p]
      ring
    _ = ∫ y in D, r y + q y ∂volume := hcommon
    _ = _ := by
      apply setIntegral_congr_fun hD.measurableSet
      intro y _hy
      simp only [r, q, reverseTimeDivergenceDrift,
        scalarSpatialCoefficientDivergence_reverseTimeCoefficient, reverseTimeMap_apply,
        reverseTimeVectorCoefficient_apply,
        scalarParabolicZeroOrderOperator_apply, matrixContraction, PDE.vecDot]
      unfold scalarSpatialCoefficientDivergence
      simp only [Pi.sub_apply, spatialPartial]
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib]
      simp_rw [Finset.sum_mul]
      rw [show
        (∑ j : Fin d, ∑ i : Fin d,
          (fderiv ℝ (fun x ↦ a (r₁ - τ) x i j) y) (PDE.basisVec i) *
            scalarSpatialGradient ell (r₁ - τ, y) j * ψ y) =
        ∑ i : Fin d, ∑ j : Fin d,
          (fderiv ℝ (fun x ↦ a (r₁ - τ) x i j) y) (PDE.basisVec i) *
            scalarSpatialGradient ell (r₁ - τ, y) j * ψ y from Finset.sum_comm]
      ring_nf
      simp_rw [Finset.mul_sum]
      simp_rw [Finset.sum_sub_distrib]
      simp_rw [Finset.sum_neg_distrib]
      ring_nf

end HypoellipticAleksandrov.Parabolic

module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.HarnackOscillation
public import HypoellipticAleksandrov.Parabolic.LocalHolder.HarnackOscillationGeometry

/-! # Structural homogeneous contraction on physical Euclidean cylinders -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Set
open scoped Matrix.Norms.Elementwise

/-- The Harnack contraction transports with unchanged structural constants. -/
theorem exists_homogeneous_range_contraction
    (N : ℕ) (hN : 1 ≤ N) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧
      ∀ (A : CoefficientField N), IsSmoothCoefficient A → IsSymmetricCoefficient A →
        HasLowerEllipticity lam A → HasUpperEllipticity Lam A →
      ∀ (T : ℝ) (v₀ : PDE.Vec N) (r : ℝ), 0 < r →
      ∀ (v : TimeVelocity N → ℝ),
        IsScalarC12On v
          (scalarParabolicOpenCylinder (T - r ^ 2) T (PDE.euclideanBall v₀ r)) →
        (∀ z ∈ scalarParabolicOpenCylinder (T - r ^ 2) T (PDE.euclideanBall v₀ r),
          scalarTimeDerivative v z =
            matrixContraction (coefficientAt A z) (scalarSpatialHessian v z)) →
        ∀ l b : ℝ,
          (∀ z ∈ scalarParabolicOpenCylinder (T - r ^ 2) T (PDE.euclideanBall v₀ r),
            l ≤ v z ∧ v z ≤ b) →
        ∃ l' b' : ℝ, b' - l' = θ * (b - l) ∧
          ∀ z ∈ scalarParabolicOpenCylinder (T - (r / 2) ^ 2) T
            (PDE.euclideanBall v₀ (r / 2)), l' ≤ v z ∧ v z ≤ b' := by
  obtain ⟨h, hh, hh1, hc⟩ :=
    exists_unit_homogeneous_range_contraction N hN lam Lam hlam hLam
  refine ⟨1 - h, sub_nonneg.mpr hh1, by linarith only [hh], ?_⟩
  intro A hA hs hlo hhi T v₀ r hr v hv he l b hb
  let D := scalarParabolicOpenCylinder (T - r ^ 2) T (PDE.euclideanBall v₀ r)
  let U := Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec N) 1
  let a := parabolicAffine (T - r ^ 2) v₀ r
  have hm : MapsTo a U D := parabolicAffine_mapsTo_backward_ball T v₀ hr
  have hD : IsOpen D := isOpen_Ioo.prod (PDE.isOpen_euclideanBall v₀ r)
  obtain ⟨hvhat, hj⟩ := KrylovEstimate.scalarC12On_affine_pullback hD v hv
    (T - r ^ 2) v₀ hr
  have hvU : IsScalarC12On (v ∘ a) U := by
    rcases hvhat with ⟨hv₀, ht, hv₂, hdt, hdg, hdh⟩
    exact ⟨hv₀.mono hm, fun z hz => ht z (hm hz), fun z hz => hv₂ z (hm hz),
      hdt.mono hm, hdg.mono hm, hdh.mono hm⟩
  have heU : ∀ z ∈ U, scalarTimeDerivative (v ∘ a) z =
      matrixContraction (coefficientAt (pullbackCoefficient A (T - r ^ 2) v₀ r) z)
        (scalarSpatialHessian (v ∘ a) z) := by
    intro z hz
    rw [(hj z (hm hz)).1, (hj z (hm hz)).2, coefficientAt_pullbackCoefficient,
      matrixContraction_smul_right, he _ (hm hz)]
  have hAc : IsContinuousCoefficientOn (pullbackCoefficient A (T - r ^ 2) v₀ r) U :=
    IsContinuousCoefficientOn.pullback
      (hA.continuous.continuousOn : IsContinuousCoefficientOn A D) hm
  have hsU : ∀ z ∈ U,
      (coefficientAt (pullbackCoefficient A (T - r ^ 2) v₀ r) z).IsSymm := by
    intro z _
    exact hs _ _
  have hloU : HasLowerEllipticityOn lam
      (pullbackCoefficient A (T - r ^ 2) v₀ r) U := by
    intro z _
    exact hlo _ _
  have hhiU : HasUpperEllipticityOn Lam
      (pullbackCoefficient A (T - r ^ 2) v₀ r) U := by
    intro z _
    exact hhi _ _
  obtain ⟨l', b', hw, hbounds⟩ := hc
    (pullbackCoefficient A (T - r ^ 2) v₀ r) (v ∘ a) hAc hsU hloU hhiU hvU heU
    l b (fun z hz => hb _ (hm hz))
  refine ⟨l', b', hw, ?_⟩
  intro z hz
  have hn := backward_half_ball_inverse_mem T v₀ hr hz
  have h := hbounds _ hn
  simpa only [Function.comp_def, a, parabolicAffine_inverse_apply T v₀ hr z] using h

end HypoellipticAleksandrov.Parabolic.LocalHolder

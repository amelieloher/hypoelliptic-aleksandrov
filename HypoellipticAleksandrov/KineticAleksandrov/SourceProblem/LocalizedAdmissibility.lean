module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.LocalizedKrylov

/-!
# Localized source estimate for the companion paper, Proposition 4.2

Admissibility of the radius and the localized bound for the companion paper, Proposition 4.2.

Setting: `0 ≤ F ∈ C_c^∞((0,1) × ℝ^d)`, smooth symmetric `B` with `λ ≤ B ≤ Λ`, `α ∈ [0,1)`,
`v_*`, `R > 0` with `R² = max {1, 4 d Λ}`, and `V` a classical solution of
`∂_r V + B : D_v² V = -F` on `(α, 1) × B_R(v_*)` with zero terminal and lateral values.

* `localizedKrylov_admissible` (admissibility): the reflected and rescaled
  `u(t, y) = V(1 - R² t, v_* + R y)` on `Q = (0, h) × B_1(0)`, `h = (1 - α)/R²`, together with
  `a(t, y) = B(1 - R² t, v_* + R y)` and `f = R² F(1 - R² t, v_* + R y)`, satisfies every
  hypothesis of the interior estimate `parabolic_aleksandrov_direct`.
* `localizedBound` (the bound): `0 ≤ V ≤ C R^(d/(d+1)) ‖F‖_{L^{d+1}}` on the closed cylinder with
  `C` depending only on `d, λ, Λ`.

Interior regularity and value continuity replace derivative boundary extensions.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic MeasureTheory Set Filter
open scoped Topology MatrixOrder Matrix.Norms.Elementwise ENNReal

variable {d : ℕ}

section Admissibility

variable {lam Lam : ℝ} {B : CoefficientField d}
  {F : TimeVelocity d → ℝ} {α R : ℝ} {vStar : PDE.Vec d} {V : TimeVelocity d → ℝ}
  (hd : 0 < d) (hlam : 0 < lam) (hLam : lam ≤ Lam)
  (hsymm : ∀ r v, (B r v).IsSymm) (hsmooth : IsSmoothCoefficient B)
  (hlow : ∀ r v, lam • (1 : PDE.Mat d) ≤ B r v) (hup : ∀ r v, B r v ≤ Lam • (1 : PDE.Mat d))
  (hF0 : ∀ z, 0 ≤ F z) (hFs : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F)
  (hFsupp : tsupport F ⊆ Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ)
  (hα0 : 0 ≤ α) (hα1 : α < 1) (hR : 0 < R) (hR1 : 1 ≤ R)
  (hV : IsClassicalBackwardDirichletSolution α 1 (PDE.euclideanBall vStar R) B
    (fun _ _ => 0) (fun _ _ => 0) (fun r v => -F (r, v)) (fun _ => 0) (fun _ => 0) V)

include hd hlam hLam hsymm hsmooth hlow hup hF0 hFs hFc hFsupp hα0 hα1 hR hR1 hV

omit hd hLam hFsupp in
/-- Admissibility of the reflected and rescaled localized solution (for any `R ≥ 1`). -/
theorem localizedKrylov_admissible_of_one_le_direct :
    IsScalarC12On (localizedScaled R vStar V)
        (krylovCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d)) ∧
      ContinuousOn (localizedScaled R vStar V)
        (krylovClosedCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d)) ∧
      ContinuousOn (localizedCoefficient R vStar B)
        (krylovClosedCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d)) ∧
      (∀ z ∈ krylovClosedCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d),
        (localizedCoefficient R vStar B z).IsSymm) ∧
      (∀ z ∈ krylovClosedCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d),
        lam • (1 : PDE.Mat d) ≤ localizedCoefficient R vStar B z ∧
          localizedCoefficient R vStar B z ≤ Lam • (1 : PDE.Mat d)) ∧
      0 < localHeight α R ∧ localHeight α R ≤ 1 ∧
      MemLp (localizedSource R vStar F) (parabolicExponent d)
        (volume.restrict
          (krylovCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d))) ∧
      (∀ z ∈ krylovCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d),
        scalarTimeDerivative (localizedScaled R vStar V) z -
            matrixContraction (localizedCoefficient R vStar B z)
              (scalarSpatialHessian (localizedScaled R vStar V) z) =
          localizedSource R vStar F z) ∧
      (∀ z, 0 ≤ localizedSource R vStar F z) ∧
      (∀ z ∈ krylovParabolicBoundary (localHeight α R) (localHeight α R) (0 : PDE.Vec d),
        localizedScaled R vStar V z = 0) ∧
      parabolicLpNormOn d (localizedSource R vStar F)
          (krylovCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d)) =
        R ^ ((d : ℝ) / ((d : ℝ) + 1)) *
          parabolicLpNormOn d F
            (scalarParabolicOpenCylinder α 1 (PDE.euclideanBall vStar R)) ∧
      (∀ z ∈ scalarParabolicClosedCylinder α 1 (PDE.euclideanBall vStar R), 0 ≤ V z) := by
  have hQV : IsOpen (scalarParabolicOpenCylinder α 1 (PDE.euclideanBall vStar R)) :=
    isOpen_Ioo.prod (PDE.isOpen_euclideanBall vStar R)
  have hQ : krylovCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d) ⊆
      reflectScale R vStar ⁻¹'
        scalarParabolicOpenCylinder α 1 (PDE.euclideanBall vStar R) :=
    fun z hz => (mem_krylovCylinder_iff_reflectScale hR z).1 hz
  have hFcont : Continuous F := hFs.continuous
  have hKsub := krylovClosedCylinder_subset_preimage (α := α) (vStar := vStar) (d := d) hR
  refine ⟨?_, ?_, ?_, ?_, ?_,
    localHeight_pos hα1 hR, localHeight_le_one hα0 hR1, ?_, ?_, ?_, ?_, ?_,
    classical_solution_nonneg hlam hF0 hα1 hR hsmooth hlow hV⟩
  · have hc := (isScalarC12On_reflectScale hQV hV.2.1 hR vStar).1
    exact ⟨hc.continuousOn.mono hQ,
      fun z hz => hc.timeSlice_differentiableAt (hQ hz),
      fun z hz => hc.spatialSlice_contDiffAt (hQ hz),
      hc.continuousOn_scalarTimeDerivative.mono hQ,
      hc.continuousOn_scalarSpatialGradient.mono hQ,
      hc.continuousOn_scalarSpatialHessian.mono hQ⟩
  · exact hV.1.comp (continuous_reflectScale R vStar).continuousOn hKsub
  · exact (hsmooth.continuous.comp (continuous_reflectScale R vStar)).continuousOn
  · intro z _
    exact hsymm _ _
  · intro z _
    exact ⟨hlow _ _, hup _ _⟩
  · exact memLp_localizedSource hR hFcont (hFcont.memLp_of_hasCompactSupport hFc)
  · intro z hz
    have hz' := hQ hz
    show scalarTimeDerivative (fun w => V (reflectScale R vStar w)) z -
        matrixContraction (coefficientAt B (reflectScale R vStar z))
          (scalarSpatialHessian (fun w => V (reflectScale R vStar w)) z) =
        R ^ 2 * F (reflectScale R vStar z)
    rw [scaled_operator_eq hQV hV.2.1 hR vStar B hz']
    have hp := hV.2.2.1 _ hz'
    simp only [scalarParabolicZeroOrderOperator_apply] at hp
    have hv0 : PDE.vecDot (0 : PDE.Vec d)
        (scalarSpatialGradient V (reflectScale R vStar z)) = 0 := by
      simp [PDE.vecDot]
    have hsum : scalarTimeDerivative V (reflectScale R vStar z) +
        matrixContraction (coefficientAt B (reflectScale R vStar z))
          (scalarSpatialHessian V (reflectScale R vStar z)) =
        -F (reflectScale R vStar z) := by
      simpa [hv0, coefficientAt] using hp
    rw [hsum]
    ring
  · intro z
    exact mul_nonneg (sq_nonneg R) (hF0 _)
  · intro z hz
    have hmem := krylovParabolicBoundary_subset_preimage (α := α) (vStar := vStar) hR hz
    change reflectScale R vStar z ∈ scalarParabolicTerminalFace 1 (PDE.euclideanBall vStar R) ∪
      scalarParabolicLateralFace α 1 (PDE.euclideanBall vStar R) at hmem
    show V (reflectScale R vStar z) = 0
    generalize reflectScale R vStar z = w at hmem
    rcases w with ⟨r, y⟩
    rcases hmem with ht | hl
    · rw [mem_scalarParabolicTerminalFace_iff] at ht
      obtain ⟨rfl, hy⟩ := ht
      exact hV.2.2.2.1 y hy
    · exact hV.2.2.2.2 _ hl
  · exact parabolicLpNormOn_localizedSource hR hFcont

end Admissibility

/-- The admissibility statement: `R > 0` with `R² = max {1, 4 d Λ}`. -/
theorem localizedKrylov_admissible_direct
    {lam Lam : ℝ} {B : CoefficientField d}
    {F : TimeVelocity d → ℝ} {α R : ℝ} {vStar : PDE.Vec d} {V : TimeVelocity d → ℝ}
    (_hd : 0 < d) (hlam : 0 < lam) (_hLam : lam ≤ Lam)
    (hsymm : ∀ r v, (B r v).IsSymm) (hsmooth : IsSmoothCoefficient B)
    (hlow : ∀ r v, lam • (1 : PDE.Mat d) ≤ B r v)
    (hup : ∀ r v, B r v ≤ Lam • (1 : PDE.Mat d))
    (hF0 : ∀ z, 0 ≤ F z) (hFs : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F)
    (_hFsupp : tsupport F ⊆ Set.Ioo (0 : ℝ) 1 ×ˢ Set.univ)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hR : 0 < R) (hRsq : R ^ 2 = max 1 (4 * d * Lam))
    (hV : IsClassicalBackwardDirichletSolution α 1 (PDE.euclideanBall vStar R) B
      (fun _ _ => 0) (fun _ _ => 0) (fun r v => -F (r, v)) (fun _ => 0) (fun _ => 0) V) :
    IsScalarC12On (localizedScaled R vStar V)
        (krylovCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d)) ∧
      ContinuousOn (localizedScaled R vStar V)
        (krylovClosedCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d)) ∧
      ContinuousOn (localizedCoefficient R vStar B)
        (krylovClosedCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d)) ∧
      (∀ z ∈ krylovClosedCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d),
        (localizedCoefficient R vStar B z).IsSymm) ∧
      (∀ z ∈ krylovClosedCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d),
        lam • (1 : PDE.Mat d) ≤ localizedCoefficient R vStar B z ∧
          localizedCoefficient R vStar B z ≤ Lam • (1 : PDE.Mat d)) ∧
      0 < localHeight α R ∧ localHeight α R ≤ 1 ∧
      MemLp (localizedSource R vStar F) (parabolicExponent d)
        (volume.restrict
          (krylovCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d))) ∧
      (∀ z ∈ krylovCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d),
        scalarTimeDerivative (localizedScaled R vStar V) z -
            matrixContraction (localizedCoefficient R vStar B z)
              (scalarSpatialHessian (localizedScaled R vStar V) z) =
          localizedSource R vStar F z) ∧
      (∀ z, 0 ≤ localizedSource R vStar F z) ∧
      (∀ z ∈ krylovParabolicBoundary (localHeight α R) (localHeight α R) (0 : PDE.Vec d),
        localizedScaled R vStar V z = 0) ∧
      parabolicLpNormOn d (localizedSource R vStar F)
          (krylovCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d)) =
        R ^ ((d : ℝ) / ((d : ℝ) + 1)) *
          parabolicLpNormOn d F
            (scalarParabolicOpenCylinder α 1 (PDE.euclideanBall vStar R)) ∧
      (∀ z ∈ scalarParabolicClosedCylinder α 1 (PDE.euclideanBall vStar R), 0 ≤ V z) := by
  have hR1 : 1 ≤ R := by
    have h1 : (1 : ℝ) ≤ R ^ 2 := by rw [hRsq]; exact le_max_left _ _
    rcases lt_or_ge R 1 with h | h
    · nlinarith
    · exact h
  exact localizedKrylov_admissible_of_one_le_direct hlam hsymm hsmooth hlow hup hF0 hFs hFc
    hα0 hα1 hR hR1 hV

end HypoellipticAleksandrov.KineticAleksandrov.Occupation

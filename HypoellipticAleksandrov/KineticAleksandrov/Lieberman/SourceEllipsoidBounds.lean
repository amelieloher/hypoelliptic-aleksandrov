module

public import HypoellipticAleksandrov.KineticAleksandrov.Lieberman.EllipsoidBarrier
public import HypoellipticAleksandrov.KineticAleksandrov.Lieberman.TerminalLift
public import HypoellipticAleksandrov.KineticAleksandrov.EllipsoidDirichlet
public import HypoellipticAleksandrov.KineticAleksandrov.Lieberman.SourceInteriorDrift
public import HypoellipticAleksandrov.KineticAleksandrov.Lieberman.SourceTimeDrift
public import HypoellipticAleksandrov.KineticAleksandrov.Lieberman.StationaryComparisonDrift
import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonBarrierPointwise
public import HypoellipticAleksandrov.Parabolic.ScalarDirichletGeometry

/-! # Ellipsoid source bounds assembled from exact upstream theorem surfaces -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Lieberman
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.Parabolic.Dirichlet HypoellipticAleksandrov.Parabolic.LocalHolder
open Set MeasureTheory Filter
open scoped Matrix ENNReal Topology MatrixOrder Matrix.Norms.Elementwise BigOperators

/-- Interior source bounds, conditional on the complete exact upstream declarations. -/
theorem exists_signed_source_ellipsoidInterior_with_bounds_of_upstream
    (hOpen :
      ∀ {d : ℕ} (Q : PDE.Mat d), IsOpen (openEllipsoid Q))
    (hGeom :
      ∀ {d : ℕ} {Q : PDE.Mat d}, Q.PosDef →
        Bornology.IsBounded (openEllipsoid Q) ∧
        closure (openEllipsoid Q) = {x | PDE.vecDot x (Q *ᵥ x) ≤ 1} ∧
        frontier (openEllipsoid Q) = {x | PDE.vecDot x (Q *ᵥ x) = 1} ∧
        HasUniformNondegenerateExteriorCone (openEllipsoid Q))
    (hDrift :
      ∀ {d : ℕ} {Ω : Set (PDE.Vec d)}, Bornology.IsBounded Ω →
        ∀ (a T : ℝ) (b : ℝ → PDE.Vec d → PDE.Vec d),
        Continuous (fun z : TimeVelocity d => b z.1 z.2) →
        ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ scalarParabolicClosedCylinder a T Ω,
          PDE.vecEuclideanNorm (b z.1 z.2) ≤ B)
    (hBarrier :
      ∀ {d : ℕ}, 0 < d → ∀ {Q : PDE.Mat d}, Q.PosDef →
        ∀ (a T lam M B : ℝ), 0 < lam → 0 ≤ M → 0 ≤ B →
        ∀ (A : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d),
        (∀ t y, (A t y).IsSymm) →
        (∀ z ∈ scalarParabolicClosedCylinder a T (openEllipsoid Q),
          lam • (1 : PDE.Mat d) ≤ A z.1 z.2) →
        (∀ z ∈ scalarParabolicClosedCylinder a T (openEllipsoid Q),
          PDE.vecEuclideanNorm (b z.1 z.2) ≤ B) →
        ∃ q : PDE.H10Function (openEllipsoid Q),
          ContDiff ℝ (⊤ : ℕ∞) q.toH1Function.toFun ∧
          (∀ y ∈ closure (openEllipsoid Q), 0 ≤ q.toH1Function.toFun y) ∧
          (∀ y ∈ frontier (openEllipsoid Q), q.toH1Function.toFun y = 0) ∧
          ∀ z ∈ Icc a T ×ˢ openEllipsoid Q,
            scalarParabolicZeroOrderOperator A b (fun _ _ => 0)
              (fun p => q.toH1Function.toFun p.2) z ≤ -M)
    (hInterior :
      ∀ {d : ℕ} (_hd : 0 < d)
          {Ω : Set (PDE.Vec d)} (_hΩ : IsOpen Ω) (_hΩb : Bornology.IsBounded Ω)
          (a T : ℝ) (_haT : a < T) (lam Lam : ℝ) (_hlam : 0 < lam) (_hLam : lam ≤ Lam)
          (A : CoefficientField d)
          (b : ℝ → PDE.Vec d → PDE.Vec d)
          (_hb : ContDiff ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => b z.1 z.2))
          (_hA : IsSmoothCoefficient A)
          (_hlo : HasLowerEllipticity lam A) (_hhi : HasUpperEllipticity Lam A)
          (F : TimeVelocity d → ℝ) (_hF : ContDiff ℝ (⊤ : ℕ∞) F),
         ∃ (u : ReverseTimeL2V _hΩ (T - a)) (g : ReverseTimeL2VStar _hΩ (T - a))
            (_hdu : HasGelfandWeakTimeDerivative _hΩ (T - a) (sub_pos.mpr _haT) u g),
            IsReverseTimeVariationalEnergySolution a T _haT _hΩ _hΩb A
              b (fun _ _ => 0) (fun t y => F (t, y))
              ⟨univ, isOpen_univ, subset_univ _, _hF.contDiffOn⟩ 0 u g _hdu ∧
            ∃ w : TimeVelocity d → ℝ,
              MemLp w 2 (timeVelocityVolumeOn (Ioo a T ×ˢ Ω)) ∧
              (∀ᵐ t ∂volume.restrict (Ioo a T),
                (fun y => w (t, y)) =ᵐ[PDE.volumeOn Ω] fun y => valueCLM _hΩ (u (T - t)) y) ∧
              IsScalarC12On w (scalarParabolicOpenCylinder a T Ω) ∧
              ∀ z ∈ scalarParabolicOpenCylinder a T Ω,
                scalarTimeDerivative w z +
                  matrixContraction (coefficientAt A z) (scalarSpatialHessian w z) +
                  PDE.vecDot (b z.1 z.2) (scalarSpatialGradient w z) = F z)
    (hTime :
      ∀ {d : ℕ}
          {Ω : Set (PDE.Vec d)} (_hΩ : IsOpen Ω) (_hΩb : Bornology.IsBounded Ω)
          (a T lam : ℝ) (_haT : a < T) (_hlam : 0 < lam)
          (A : CoefficientField d)
          (b : ℝ → PDE.Vec d → PDE.Vec d)
          (_hb : ContDiff ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => b z.1 z.2))
          (_hA : IsSmoothCoefficient A)
          (_hlo : HasLowerEllipticity lam A)
          (F : TimeVelocity d → ℝ) (_hF : ContDiff ℝ (⊤ : ℕ∞) F)
          (M : ℝ) (_hM : 0 ≤ M)
          (_hFM : ∀ z ∈ scalarParabolicClosedCylinder a T Ω, |F z| ≤ M)
          (u : ReverseTimeL2V _hΩ (T - a)) (g : ReverseTimeL2VStar _hΩ (T - a))
          (_hdu : HasGelfandWeakTimeDerivative _hΩ (T - a) (sub_pos.mpr _haT) u g)
          (_hu : IsReverseTimeVariationalEnergySolution a T _haT _hΩ _hΩb A
            b (fun _ _ => 0) (fun t y => F (t, y))
            ⟨univ, isOpen_univ, subset_univ _, _hF.contDiffOn⟩ 0 u g _hdu)
          (w : TimeVelocity d → ℝ)
          (_hw : ContinuousOn w (scalarParabolicOpenCylinder a T Ω))
          (_hwslice : ∀ᵐ t ∂volume.restrict (Ioo a T),
            (fun y => w (t, y)) =ᵐ[PDE.volumeOn Ω] fun y => valueCLM _hΩ (u (T - t)) y),
         ∀ z ∈ scalarParabolicOpenCylinder a T Ω, |w z| ≤ M * (T - z.1))
    (hCompare :
      ∀ {d : ℕ}
          {Ω : Set (PDE.Vec d)} (_hΩ : IsOpen Ω) (_hΩb : Bornology.IsBounded Ω)
          (a T : ℝ) (_haT : a < T) (lam : ℝ) (_hlam : 0 < lam)
          (A : CoefficientField d)
          (b : ℝ → PDE.Vec d → PDE.Vec d)
          (_hb : ContDiff ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => b z.1 z.2))
          (_hA : IsSmoothCoefficient A)
          (_hlo : HasLowerEllipticity lam A) (F G : TimeVelocity d → ℝ)
          (_hF : ContDiff ℝ (⊤ : ℕ∞) F) (_hG : ContDiff ℝ (⊤ : ℕ∞) G)
          (q : PDE.H10Function Ω) (_hq : ContDiff ℝ 2 q.toH1Function.toFun)
          (_hqn : ∀ y ∈ Ω, 0 ≤ q.toH1Function.toFun y)
          (_heq : ∀ z ∈ Icc a T ×ˢ Ω,
            scalarParabolicZeroOrderOperator A b (fun _ _ => 0)
              (fun z => q.toH1Function.toFun z.2) z = G z)
          (_hGF : ∀ z ∈ scalarParabolicClosedCylinder a T Ω, G z ≤ -|F z|)
          (u : ReverseTimeL2V _hΩ (T - a)) (g : ReverseTimeL2VStar _hΩ (T - a))
          (_hdu : HasGelfandWeakTimeDerivative _hΩ (T - a) (sub_pos.mpr _haT) u g)
          (_hu : IsReverseTimeVariationalEnergySolution a T _haT _hΩ _hΩb A
            b (fun _ _ => 0) (fun t y => F (t, y))
            ⟨univ, isOpen_univ, subset_univ _, _hF.contDiffOn⟩ 0 u g _hdu),
         ∀ τ : ℝ, ∀ _hτ : τ ∈ Icc 0 (T - a), ∀ᵐ y ∂PDE.volumeOn Ω,
            |reverseTimeHilbertRepresentative _hΩ (T - a) (sub_pos.mpr _haT)
              u g _hdu ⟨τ, _hτ⟩ y| ≤ q.toH1Function.toFun y)
    : ∀ {d : ℕ}, 0 < d → ∀ {Q : PDE.Mat d}, Q.PosDef →
  ∀ (a T lam Lam : ℝ), a < T → 0 < lam → lam ≤ Lam →
  ∀ (A : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d),
  (∀ t y, (A t y).IsSymm) → IsSmoothCoefficient A →
  HasLowerEllipticity lam A → HasUpperEllipticity Lam A →
  ContDiff ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => b z.1 z.2) →
  ∀ (F : TimeVelocity d → ℝ), ContDiff ℝ (⊤ : ℕ∞) F →
  ∀ (M : ℝ), 0 ≤ M →
  (∀ z ∈ scalarParabolicClosedCylinder a T (openEllipsoid Q), |F z| ≤ M) →
  ∃ (w : TimeVelocity d → ℝ) (q : PDE.H10Function (openEllipsoid Q)),
    ContDiff ℝ (⊤ : ℕ∞) q.toH1Function.toFun ∧
    (∀ y ∈ frontier (openEllipsoid Q), q.toH1Function.toFun y = 0) ∧
    IsScalarC12On w (scalarParabolicOpenCylinder a T (openEllipsoid Q)) ∧
    (∀ z ∈ scalarParabolicOpenCylinder a T (openEllipsoid Q),
      scalarParabolicZeroOrderOperator A b (fun _ _ => 0) w z = F z) ∧
    (∀ z ∈ scalarParabolicOpenCylinder a T (openEllipsoid Q),
      |w z| ≤ M * (T - z.1)) ∧
    ∀ z ∈ scalarParabolicOpenCylinder a T (openEllipsoid Q),
      |w z| ≤ q.toH1Function.toFun z.2 := by
  intro d hd Q hQ a T lam Lam haT hlam hLam A b hsym hA hlo hhi hb F hF M hM hFM
  have hΩ := hOpen Q
  have hΩb := (hGeom hQ).1
  obtain ⟨B, hB, hbB⟩ := hDrift hΩb a T b hb.continuous
  obtain ⟨q, hq, hqn, hqf, hqop⟩ :=
    hBarrier hd hQ a T lam M B hlam hM hB A b hsym
      (fun z _ => hlo z.1 z.2) hbB
  obtain ⟨u, g, hdu, hu, w, _, hs, hw, he⟩ :=
    hInterior hd hΩ hΩb a T haT lam Lam hlam hLam A b hb hA hlo hhi F hF
  have htime := hTime hΩ hΩb a T lam haT hlam A b hb hA hlo F hF
    M hM hFM u g hdu hu w hw.continuousOn hs
  let G : TimeVelocity d → ℝ := scalarParabolicZeroOrderOperator A b (fun _ _ => 0)
    (fun p => q.toH1Function.toFun p.2)
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := by
    have h := (contDiff_terminal_lift_source A b q.toH1Function.toFun hA hb hq).neg
    simpa only [neg_neg] using h
  have hcl : closure (scalarParabolicOpenCylinder a T (openEllipsoid Q)) =
      scalarParabolicClosedCylinder a T (openEllipsoid Q) := by
    unfold scalarParabolicOpenCylinder scalarParabolicClosedCylinder
    rw [closure_prod_eq, closure_Ioo haT.ne]
  have hGM : ∀ z ∈ scalarParabolicClosedCylinder a T (openEllipsoid Q), G z ≤ -M := by
    intro z hz
    apply le_on_closure (s := scalarParabolicOpenCylinder a T (openEllipsoid Q))
      (fun p hp => hqop p ⟨⟨hp.1.1.le, hp.1.2.le⟩, hp.2⟩)
      hG.continuous.continuousOn continuous_const.continuousOn
    rwa [hcl]
  have hGF : ∀ z ∈ scalarParabolicClosedCylinder a T (openEllipsoid Q), G z ≤ -|F z| :=
    fun z hz => (hGM z hz).trans (neg_le_neg (hFM z hz))
  have henergy := hCompare hΩ hΩb a T haT lam hlam A b hb hA hlo F G hF hG q
    (hq.of_le (by simp)) (fun y hy => hqn y (subset_closure hy))
    (fun _ _ => rfl) hGF u g hdu hu
  have hspace := classicalEnergyRepresentative_abs_le_continuous_barrier hΩ a T haT
    u g hdu q.toH1Function.toFun hq.continuous henergy w hw.continuousOn hs
  refine ⟨w, q, hq, hqf, hw, ?_, htime, hspace⟩
  intro z hz
  simpa only [scalarParabolicZeroOrderOperator_apply, coefficientAt, zero_mul, add_zero]
    using he z hz

/-- Interior source bounds with the drift ports discharged. -/
theorem exists_signed_source_ellipsoidInterior_with_bounds_of_geometry_barrier
    (hOpen :
      ∀ {d : ℕ} (Q : PDE.Mat d), IsOpen (openEllipsoid Q))
    (hGeom :
      ∀ {d : ℕ} {Q : PDE.Mat d}, Q.PosDef →
        Bornology.IsBounded (openEllipsoid Q) ∧
        closure (openEllipsoid Q) = {x | PDE.vecDot x (Q *ᵥ x) ≤ 1} ∧
        frontier (openEllipsoid Q) = {x | PDE.vecDot x (Q *ᵥ x) = 1} ∧
        HasUniformNondegenerateExteriorCone (openEllipsoid Q))
    (hDrift :
      ∀ {d : ℕ} {Ω : Set (PDE.Vec d)}, Bornology.IsBounded Ω →
        ∀ (a T : ℝ) (b : ℝ → PDE.Vec d → PDE.Vec d),
        Continuous (fun z : TimeVelocity d => b z.1 z.2) →
        ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ scalarParabolicClosedCylinder a T Ω,
          PDE.vecEuclideanNorm (b z.1 z.2) ≤ B)
    (hBarrier :
      ∀ {d : ℕ}, 0 < d → ∀ {Q : PDE.Mat d}, Q.PosDef →
        ∀ (a T lam M B : ℝ), 0 < lam → 0 ≤ M → 0 ≤ B →
        ∀ (A : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d),
        (∀ t y, (A t y).IsSymm) →
        (∀ z ∈ scalarParabolicClosedCylinder a T (openEllipsoid Q),
          lam • (1 : PDE.Mat d) ≤ A z.1 z.2) →
        (∀ z ∈ scalarParabolicClosedCylinder a T (openEllipsoid Q),
          PDE.vecEuclideanNorm (b z.1 z.2) ≤ B) →
        ∃ q : PDE.H10Function (openEllipsoid Q),
          ContDiff ℝ (⊤ : ℕ∞) q.toH1Function.toFun ∧
          (∀ y ∈ closure (openEllipsoid Q), 0 ≤ q.toH1Function.toFun y) ∧
          (∀ y ∈ frontier (openEllipsoid Q), q.toH1Function.toFun y = 0) ∧
          ∀ z ∈ Icc a T ×ˢ openEllipsoid Q,
            scalarParabolicZeroOrderOperator A b (fun _ _ => 0)
              (fun p => q.toH1Function.toFun p.2) z ≤ -M)
    : ∀ {d : ℕ}, 0 < d → ∀ {Q : PDE.Mat d}, Q.PosDef →
  ∀ (a T lam Lam : ℝ), a < T → 0 < lam → lam ≤ Lam →
  ∀ (A : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d),
  (∀ t y, (A t y).IsSymm) → IsSmoothCoefficient A →
  HasLowerEllipticity lam A → HasUpperEllipticity Lam A →
  ContDiff ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => b z.1 z.2) →
  ∀ (F : TimeVelocity d → ℝ), ContDiff ℝ (⊤ : ℕ∞) F →
  ∀ (M : ℝ), 0 ≤ M →
  (∀ z ∈ scalarParabolicClosedCylinder a T (openEllipsoid Q), |F z| ≤ M) →
  ∃ (w : TimeVelocity d → ℝ) (q : PDE.H10Function (openEllipsoid Q)),
    ContDiff ℝ (⊤ : ℕ∞) q.toH1Function.toFun ∧
    (∀ y ∈ frontier (openEllipsoid Q), q.toH1Function.toFun y = 0) ∧
    IsScalarC12On w (scalarParabolicOpenCylinder a T (openEllipsoid Q)) ∧
    (∀ z ∈ scalarParabolicOpenCylinder a T (openEllipsoid Q),
      scalarParabolicZeroOrderOperator A b (fun _ _ => 0) w z = F z) ∧
    (∀ z ∈ scalarParabolicOpenCylinder a T (openEllipsoid Q),
      |w z| ≤ M * (T - z.1)) ∧
    ∀ z ∈ scalarParabolicOpenCylinder a T (openEllipsoid Q),
      |w z| ≤ q.toH1Function.toFun z.2 := by
  exact exists_signed_source_ellipsoidInterior_with_bounds_of_upstream hOpen hGeom hDrift
    hBarrier (@exists_signed_source_classicalInterior_withDrift)
    (@classical_abs_le_source_time_withDrift) (@variational_abs_le_stationary_withDrift)

/-- Every smooth signed source has an interior correction with both ellipsoid envelopes. -/
theorem exists_signed_source_ellipsoidInterior_with_bounds :
∀ {d : ℕ}, 0 < d → ∀ {Q : PDE.Mat d}, Q.PosDef →
  ∀ (a T lam Lam : ℝ), a < T → 0 < lam → lam ≤ Lam →
  ∀ (A : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d),
  (∀ t y, (A t y).IsSymm) → IsSmoothCoefficient A →
  HasLowerEllipticity lam A → HasUpperEllipticity Lam A →
  ContDiff ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => b z.1 z.2) →
  ∀ (F : TimeVelocity d → ℝ), ContDiff ℝ (⊤ : ℕ∞) F →
  ∀ (M : ℝ), 0 ≤ M →
  (∀ z ∈ scalarParabolicClosedCylinder a T (openEllipsoid Q), |F z| ≤ M) →
  ∃ (w : TimeVelocity d → ℝ) (q : PDE.H10Function (openEllipsoid Q)),
    ContDiff ℝ (⊤ : ℕ∞) q.toH1Function.toFun ∧
    (∀ y ∈ frontier (openEllipsoid Q), q.toH1Function.toFun y = 0) ∧
    IsScalarC12On w (scalarParabolicOpenCylinder a T (openEllipsoid Q)) ∧
    (∀ z ∈ scalarParabolicOpenCylinder a T (openEllipsoid Q),
      scalarParabolicZeroOrderOperator A b (fun _ _ => 0) w z = F z) ∧
    (∀ z ∈ scalarParabolicOpenCylinder a T (openEllipsoid Q),
      |w z| ≤ M * (T - z.1)) ∧
    ∀ z ∈ scalarParabolicOpenCylinder a T (openEllipsoid Q),
      |w z| ≤ q.toH1Function.toFun z.2 := by
  exact exists_signed_source_ellipsoidInterior_with_bounds_of_geometry_barrier
    (@isOpen_openEllipsoid) (@openEllipsoid_geometry)
    (@exists_closedCylinder_drift_bound) (@exists_h10_ellipsoid_drift_barrier)

end HypoellipticAleksandrov.KineticAleksandrov.Lieberman

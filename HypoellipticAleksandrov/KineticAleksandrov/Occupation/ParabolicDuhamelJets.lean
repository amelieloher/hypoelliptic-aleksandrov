module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationWeakAdjoint
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationWeakRegularity
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeTransfer
public import HypoellipticAleksandrov.Parabolic.ContDiffOnTwoToScalarC12
public import HypoellipticAleksandrov.Parabolic.HarnackUnitCylinder.ScalarHessian

/-!
# Weak integration by parts for `z`-independent functions

A function `w` of `(σ, v)` that is smooth on an open set `D` gives a function `w ∘ π` of the
packed point `(σ, v, z)` that is smooth on `π ⁻¹' D`.  Against a compactly supported smooth test
`ψ` in `π ⁻¹' D`, the transported adjoint `Lop^*` satisfies
`∫ (w ∘ π) Lop^* ψ = ∫ (P₀ w ∘ π) ψ`, where `P₀ = ∂_σ + B : D_v²` is the parabolic operator.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Set Filter
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.Evolution
open scoped Topology

variable {d : ℕ}

/-- The projection `(σ, v, z) ↦ (σ, v)` of packed evolution space onto time and velocity. -/
def evolutionToTimeVelocity (d : ℕ) : EvolutionVec d →L[ℝ] TimeVelocity d :=
  (Evolution.timeCoord d).prod (diffusedCoord d)

@[simp] theorem evolutionToTimeVelocity_apply (x : EvolutionVec d) :
    evolutionToTimeVelocity d x = (Evolution.timeCoord d x, diffusedCoord d x) := rfl

theorem timeCoord_basisT : Evolution.timeCoord d (basisT : EvolutionVec d) = 1 := by
  simp [basisT]

theorem timeCoord_basisV (j : Fin d) :
    Evolution.timeCoord d (basisV j : EvolutionVec d) = 0 := by
  simp [basisV]

theorem timeCoord_basisZ (l : Fin d) :
    Evolution.timeCoord d (basisZ l : EvolutionVec d) = 0 := by
  simp [basisZ]

theorem evolutionToTimeVelocity_basisT :
    evolutionToTimeVelocity d (basisT : EvolutionVec d) = (1, 0) := by
  simp [basisT]

theorem evolutionToTimeVelocity_basisZ (l : Fin d) :
    evolutionToTimeVelocity d (basisZ l : EvolutionVec d) = 0 := by
  simp [basisZ]

theorem diffusedCoord_basisV (j : Fin d) :
    diffusedCoord d (basisV j : EvolutionVec d) = PDE.basisVec j := by
  simp only [basisV, diffusedCoord_packPoint]
  rfl

theorem evolutionToTimeVelocity_line (x w : EvolutionVec d)
    (hw : Evolution.timeCoord d w = 0) (t : ℝ) :
    evolutionToTimeVelocity d (x + t • w) =
      ((evolutionToTimeVelocity d x).1,
        (evolutionToTimeVelocity d x).2 + t • diffusedCoord d w) := by
  simp only [evolutionToTimeVelocity_apply, map_add, map_smul, hw, Prod.smul_mk, smul_zero,
    Prod.mk_add_mk, add_zero]

/-- The time line derivative of a `z`-independent function. -/
theorem hasLineDerivAt_zIndep_time {w : TimeVelocity d → ℝ} {D : Set (TimeVelocity d)}
    (hD : IsOpen D) (hw : IsScalarC12On w D) {x : EvolutionVec d}
    (hx : evolutionToTimeVelocity d x ∈ D) :
    HasLineDerivAt ℝ (w ∘ evolutionToTimeVelocity d)
      (scalarTimeDerivative w (evolutionToTimeVelocity d x)) x basisT := by
  have h := ((scalarC12_hasFDerivAt hD hw hx).comp x
    (evolutionToTimeVelocity d).hasFDerivAt).hasLineDerivAt basisT
  simpa only [ContinuousLinearMap.comp_apply, evolutionToTimeVelocity_basisT,
    ContinuousLinearMap.coprod_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, one_smul, map_zero, add_zero] using h

/-- Spatial line derivatives of a `z`-independent function. -/
theorem hasLineDerivAt_zIndep_spatial {w : TimeVelocity d → ℝ} {D : Set (TimeVelocity d)}
    (hw : IsScalarC12On w D) {x v : EvolutionVec d} (hx : evolutionToTimeVelocity d x ∈ D)
    (hv : Evolution.timeCoord d v = 0) :
    HasLineDerivAt ℝ (w ∘ evolutionToTimeVelocity d)
      (PDE.vecDot (scalarSpatialGradient w (evolutionToTimeVelocity d x))
        (diffusedCoord d v)) x v := by
  have h := ((hw.spatialSlice_contDiffAt hx).differentiableAt (by norm_num)).hasFDerivAt
    |>.hasLineDerivAt (diffusedCoord d v)
  rw [PDE.fderiv_apply_eq_vecDot_classicalGradient] at h
  unfold HasLineDerivAt at h ⊢
  simpa only [Function.comp_def, evolutionToTimeVelocity_line x v hv,
    scalarSpatialGradient] using! h

/-- Spatial line derivatives of gradient entries are scalar Hessian entries. -/
theorem hasLineDerivAt_zIndep_gradient {w : TimeVelocity d → ℝ} {D : Set (TimeVelocity d)}
    (hw : IsScalarC12On w D) {x v : EvolutionVec d} (hx : evolutionToTimeVelocity d x ∈ D)
    (hv : Evolution.timeCoord d v = 0) (i j : Fin d)
    (hdir : diffusedCoord d v = PDE.basisVec i) :
    HasLineDerivAt ℝ (fun y => scalarSpatialGradient w (evolutionToTimeVelocity d y) j)
      (scalarSpatialHessian w (evolutionToTimeVelocity d x) i j) x v := by
  have hc2 := hw.spatialSlice_contDiffAt hx
  have hd : DifferentiableAt ℝ (fderiv ℝ (fun y => w ((evolutionToTimeVelocity d x).1, y)))
      (evolutionToTimeVelocity d x).2 :=
    (hc2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h := (hd.clm_apply (differentiableAt_const (PDE.basisVec j))).hasFDerivAt
    |>.hasLineDerivAt (PDE.basisVec i)
  have he : fderiv ℝ (fun y => fderiv ℝ
      (fun y => w ((evolutionToTimeVelocity d x).1, y)) y (PDE.basisVec j))
      (evolutionToTimeVelocity d x).2 (PDE.basisVec i) =
      scalarSpatialHessian w (evolutionToTimeVelocity d x) i j := by
    have hz : fderiv ℝ (fun _ : PDE.Vec d => PDE.basisVec j)
        (evolutionToTimeVelocity d x).2 = 0 := (hasFDerivAt_const (PDE.basisVec j) _).fderiv
    rw [fderiv_clm_apply hd (differentiableAt_const (PDE.basisVec j))]
    erw [hz]
    simpa only [ContinuousLinearMap.comp_zero, zero_add,
      ContinuousLinearMap.flip_apply] using! (scalarSpatialHessian_eq_secondFDeriv hc2 i j).symm
  rw [he] at h
  unfold HasLineDerivAt at h ⊢
  simpa only [evolutionToTimeVelocity_line x v hv, hdir,
    scalarSpatialGradient, PDE.classicalGradient] using! h

/-- **Weak form for `z`-independent smooth functions.**  For `w` smooth on the open set `D`
and a smooth compactly supported test `ψ` supported in `π ⁻¹' D`,
`∫ (w ∘ π) Lop^* ψ = ∫ (P₀ w ∘ π) ψ` with `P₀ = ∂_σ + B : D_v²`. -/
theorem integral_transportedAdjoint_zIndep {B' : CoefficientField d}
    (hB : IsSmoothFullKineticCoefficient (zIndependentCoefficient B'))
    {b : PDE.Vec d → PDE.Vec d} (hb : IsSmoothDrift b)
    {D : Set (TimeVelocity d)} (hD : IsOpen D) {w : TimeVelocity d → ℝ}
    (hw : ContDiffOn ℝ (⊤ : ℕ∞) w D)
    {ψ : EvolutionVec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ evolutionToTimeVelocity d ⁻¹' D) :
    (∫ x in evolutionToTimeVelocity d ⁻¹' D, w (evolutionToTimeVelocity d x) *
        transportedAdjoint (zIndependentCoefficient B') b ψ x) =
      ∫ x in evolutionToTimeVelocity d ⁻¹' D,
        scalarParabolicOperator B' (fun _ _ => 0) w (evolutionToTimeVelocity d x) * ψ x := by
  have hu : IsScalarC12On w D :=
    isScalarC12On_of_isOpen_contDiffOn_two hD (hw.of_le (by norm_num))
  set Qp := evolutionToTimeVelocity d with hQp
  have hQc : Continuous Qp := Qp.continuous
  have hU : IsOpen (Qp ⁻¹' D) := hD.preimage hQc
  let T : EvolutionVec d → ℝ := fun x => scalarTimeDerivative w (Qp x)
  let V : Fin d → EvolutionVec d → ℝ := fun i x => scalarSpatialGradient w (Qp x) i
  let Z : Fin d → EvolutionVec d → ℝ := fun _ _ => 0
  let H : Fin d → Fin d → EvolutionVec d → ℝ := fun i j x => scalarSpatialHessian w (Qp x) i j
  let K : Fin d → EvolutionVec d → ℝ := fun _ _ => 0
  have hmaps : Set.MapsTo Qp (Qp ⁻¹' D) D := fun x hx => hx
  have hw0 : ContinuousOn (w ∘ Qp) (Qp ⁻¹' D) :=
    hu.continuousOn.comp hQc.continuousOn hmaps
  have hT : ContinuousOn T (Qp ⁻¹' D) :=
    hu.continuousOn_scalarTimeDerivative.comp hQc.continuousOn hmaps
  have hg0 : ContinuousOn (fun x => scalarSpatialGradient w (Qp x)) (Qp ⁻¹' D) :=
    hu.continuousOn_scalarSpatialGradient.comp hQc.continuousOn hmaps
  have hh0 : ContinuousOn (fun x => scalarSpatialHessian w (Qp x)) (Qp ⁻¹' D) :=
    hu.continuousOn_scalarSpatialHessian.comp hQc.continuousOn hmaps
  have hV : ∀ i, ContinuousOn (V i) (Qp ⁻¹' D) := fun i =>
    (continuous_apply i).comp_continuousOn hg0
  have hH : ∀ i j, ContinuousOn (H i j) (Qp ⁻¹' D) := fun i j =>
    (show Continuous (fun A : PDE.Mat d => A i j) from
      (continuous_apply j).comp (continuous_apply i)).comp_continuousOn hh0
  have hdT : ∀ x ∈ Qp ⁻¹' D, HasLineDerivAt ℝ (w ∘ Qp) (T x) x basisT := fun x hx =>
    hasLineDerivAt_zIndep_time hD hu hx
  have hdV : ∀ i x, x ∈ Qp ⁻¹' D → HasLineDerivAt ℝ (w ∘ Qp) (V i x) x (basisV i) := by
    intro i x hx
    have h := hasLineDerivAt_zIndep_spatial hu hx (timeCoord_basisV i)
    rw [diffusedCoord_basisV, PDE.vecDot_basisVec_right] at h
    exact h
  have hdZ : ∀ i x, x ∈ Qp ⁻¹' D → HasLineDerivAt ℝ (w ∘ Qp) (Z i x) x (basisZ i) := by
    intro i x hx
    have h := hasLineDerivAt_zIndep_spatial hu hx (timeCoord_basisZ i)
    have hz : diffusedCoord d (basisZ i : EvolutionVec d) = 0 := by
      simp [basisZ]
    rw [hz] at h
    simpa [PDE.vecDot] using h
  have hdH : ∀ i j x, x ∈ Qp ⁻¹' D → HasLineDerivAt ℝ (V i) (H i j x) x (basisV j) := by
    intro i j x hx
    have h := hasLineDerivAt_zIndep_gradient hu hx (timeCoord_basisV j) j i
      (diffusedCoord_basisV j)
    have hsy := scalarSpatialHessian_isSymm_of_c12 hu hx
    have he : scalarSpatialHessian w (Qp x) j i = H i j x :=
      congrFun (congrFun hsy i) j
    change HasLineDerivAt ℝ (V i) (scalarSpatialHessian w (Qp x) j i) x (basisV j) at h
    rw [he] at h
    exact h
  have hdK : ∀ i x, x ∈ Qp ⁻¹' D → HasLineDerivAt ℝ (Z i) (K i x) x (basisZ i) := by
    intro i x _
    exact (hasFDerivAt_const (0 : ℝ) x).hasLineDerivAt _
  have key := integral_regularizedAdjoint_of_jets (U := Qp ⁻¹' D) (zIndependentCoefficient B') b
    0 hB hb (w ∘ Qp) T V Z H K hw0 hT hV (fun _ => continuousOn_const)
    hH (fun _ => continuousOn_const) hdT hdV hdZ hdH hdK ψ hψ hc hs
  have hreg : ∀ x, regularizedAdjoint (zIndependentCoefficient B') b 0 ψ x =
      transportedAdjoint (zIndependentCoefficient B') b ψ x := fun x => by
    simp [regularizedAdjoint]
  simp only [hreg] at key
  refine key.trans ?_
  refine setIntegral_congr_fun hU.measurableSet fun x hx => ?_
  congr 1
  simp only [T, H, Z, K, mul_zero, Finset.sum_const_zero, add_zero,
    scalarParabolicOperator_apply, matrixContraction, PDE.vecDot, zIndependentCoefficient_apply]
  simp [hQp]

end HypoellipticAleksandrov.KineticAleksandrov.Occupation

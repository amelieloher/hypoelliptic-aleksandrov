module

public import HypoellipticAleksandrov.Parabolic.KrylovCylinder
public import HypoellipticAleksandrov.Parabolic.Scaling
public import HypoellipticAleksandrov.Parabolic.C2ToScalarC12

/-! # Scalar slice calculus for the Krylov estimate -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.KrylovEstimate
open Set Filter
open scoped Topology

/-- The forward scalar residual, using the slice derivatives. -/
def residual {N : ℕ} (a : TimeVelocity N → PDE.Mat N)
    (u : TimeVelocity N → ℝ) (z : TimeVelocity N) : ℝ :=
  scalarTimeDerivative u z - matrixContraction (a z) (scalarSpatialHessian u z)

private theorem gradient_affine {N : ℕ} (f : PDE.Vec N → ℝ)
    (v : PDE.Vec N) (ρ : ℝ) (x : PDE.Vec N)
    (hf : DifferentiableAt ℝ f (v + ρ • x)) :
    PDE.classicalGradient (fun y => f (v + ρ • y)) x =
      ρ • PDE.classicalGradient f (v + ρ • x) := by
  have ha : HasFDerivAt (fun y : PDE.Vec N => v + ρ • y)
      (ρ • ContinuousLinearMap.id ℝ (PDE.Vec N)) x := by
    simpa only [Pi.smul_def, id_eq] using! ((hasFDerivAt_id x).const_smul ρ).const_add v
  have hc := hf.hasFDerivAt.comp x ha
  ext i
  simp only [PDE.classicalGradient, Pi.smul_apply, smul_eq_mul]
  simp only [Function.comp_def] at hc
  rw [hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]

private theorem hessian_affine {N : ℕ} (f : PDE.Vec N → ℝ)
    (v : PDE.Vec N) (ρ : ℝ) (x : PDE.Vec N)
    (hf : ContDiffAt ℝ 2 f (v + ρ • x)) :
    (fun i j => (fderiv ℝ (PDE.classicalGradient (fun y => f (v + ρ • y))) x
      (PDE.basisVec i)) j) =
    ρ ^ 2 • (fun i j => (fderiv ℝ (PDE.classicalGradient f) (v + ρ • x)
      (PDE.basisVec i)) j) := by
  have ha : HasFDerivAt (fun y : PDE.Vec N => v + ρ • y)
      (ρ • ContinuousLinearMap.id ℝ (PDE.Vec N)) x := by
    simpa only [Pi.smul_def, id_eq] using! ((hasFDerivAt_id x).const_smul ρ).const_add v
  have hg : DifferentiableAt ℝ (PDE.classicalGradient f) (v + ρ • x) := by
    apply differentiableAt_pi.mpr
    intro i
    exact ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).clm_apply (differentiableAt_const (c := PDE.basisVec i))
  have he : PDE.classicalGradient (fun y => f (v + ρ • y)) =ᶠ[𝓝 x]
      (fun y => ρ • PDE.classicalGradient f (v + ρ • y)) := by
    have ht := ha.continuousAt.tendsto.eventually (hf.eventually (by norm_num))
    filter_upwards [ht] with y hy
    exact gradient_affine f v ρ y (hy.differentiableAt (by norm_num))
  have hc := (hg.hasFDerivAt.comp x ha).const_smul ρ
  change HasFDerivAt (fun y => ρ • PDE.classicalGradient f (v + ρ • y)) _ x at hc
  rw [he.fderiv_eq, hc.fderiv]
  ext i j
  simp only [Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, map_smul]
  ring

private theorem time_affine {N : ℕ} (u : TimeVelocity N → ℝ)
    (b : ℝ) (v : PDE.Vec N) (ρ : ℝ) (z : TimeVelocity N)
    (hu : DifferentiableAt ℝ (fun t => u (t, v + ρ • z.2)) (b + ρ ^ 2 * z.1)) :
    scalarTimeDerivative (u ∘ parabolicAffine b v ρ) z =
      ρ ^ 2 * scalarTimeDerivative u (parabolicAffine b v ρ z) := by
  have ha : HasDerivAt (fun t : ℝ => b + ρ ^ 2 * t) (ρ ^ 2) z.1 := by
    simpa using ((hasDerivAt_id z.1).const_mul (ρ ^ 2)).const_add b
  have hc := hu.hasDerivAt.comp z.1 ha
  change deriv (fun t => u (b + ρ ^ 2 * t, v + ρ • z.2)) z.1 = _
  simp only [Function.comp_def] at hc
  rw [hc.deriv]
  change _ * ρ ^ 2 = ρ ^ 2 * _
  exact mul_comm _ _

/-- Parabolic affine pullback preserves scalar C12 regularity and its selected derivatives. -/
theorem scalarC12On_affine_pullback
    {N : ℕ} {D : Set (TimeVelocity N)} (hD : IsOpen D)
    (u : TimeVelocity N → ℝ) (hu : IsScalarC12On u D)
    (b : ℝ) (v₀ : PDE.Vec N) {ρ : ℝ} (hρ : 0 < ρ) :
    IsScalarC12On (u ∘ parabolicAffine b v₀ ρ)
      (parabolicAffine b v₀ ρ ⁻¹' D) ∧
    ∀ z ∈ parabolicAffine b v₀ ρ ⁻¹' D,
      scalarTimeDerivative (u ∘ parabolicAffine b v₀ ρ) z =
          ρ ^ 2 * scalarTimeDerivative u (parabolicAffine b v₀ ρ z) ∧
      scalarSpatialHessian (u ∘ parabolicAffine b v₀ ρ) z =
          ρ ^ 2 • scalarSpatialHessian u (parabolicAffine b v₀ ρ z) := by
  let S := parabolicAffine b v₀ ρ ⁻¹' D
  have ht (z : TimeVelocity N) (hz : z ∈ S) :=
    time_affine u b v₀ ρ z (hu.timeSlice_differentiableAt hz)
  have hg (z : TimeVelocity N) (hz : z ∈ S) :
      scalarSpatialGradient (u ∘ parabolicAffine b v₀ ρ) z =
        ρ • scalarSpatialGradient u (parabolicAffine b v₀ ρ z) :=
    gradient_affine (fun y => u (b + ρ ^ 2 * z.1, y)) v₀ ρ z.2
      ((hu.spatialSlice_contDiffAt hz).differentiableAt (by norm_num))
  have hh (z : TimeVelocity N) (hz : z ∈ S) :
      scalarSpatialHessian (u ∘ parabolicAffine b v₀ ρ) z =
        ρ ^ 2 • scalarSpatialHessian u (parabolicAffine b v₀ ρ z) :=
    hessian_affine (fun y => u (b + ρ ^ 2 * z.1, y)) v₀ ρ z.2
      (hu.spatialSlice_contDiffAt hz)
  have hm : Set.MapsTo (parabolicAffine b v₀ ρ) S D := fun _ hz => hz
  have hc := (contDiff_parabolicAffine b v₀ ρ).continuous
  refine ⟨⟨hu.continuousOn.comp hc.continuousOn hm, ?_, ?_, ?_, ?_, ?_⟩,
    fun z hz => ⟨ht z hz, hh z hz⟩⟩
  · intro z hz
    have ha : DifferentiableAt ℝ (fun t : ℝ => b + ρ ^ 2 * t) z.1 := by fun_prop
    have hs := (hu.timeSlice_differentiableAt hz).comp z.1 ha
    simpa only [Function.comp_def, parabolicAffine] using! hs
  · intro z hz
    have ha : ContDiffAt ℝ 2 (fun y : PDE.Vec N => v₀ + ρ • y) z.2 := by
      fun_prop
    have hs := (hu.spatialSlice_contDiffAt hz).comp z.2 ha
    simpa only [Function.comp_def, parabolicAffine] using! hs
  · apply ((hu.continuousOn_scalarTimeDerivative.comp hc.continuousOn hm).const_mul
      (ρ ^ 2)).congr
    exact fun z hz => ht z hz
  · apply ((hu.continuousOn_scalarSpatialGradient.comp hc.continuousOn hm).const_smul
      ρ).congr
    exact fun z hz => hg z hz
  · apply ((hu.continuousOn_scalarSpatialHessian.comp hc.continuousOn hm).const_smul
      (ρ ^ 2)).congr
    exact fun z hz => hh z hz

private theorem coordinate_single_smooth {N : ℕ} (w : TimeVelocity N → ℝ)
    (hw : ContDiff ℝ 2 w) (c : TimeVelocityCoord N) (z : TimeVelocity N) :
    TimeVelocityMultiIndex.coordinateIteratedFDeriv (Pi.single c 1) w z =
      fderiv ℝ w z (timeVelocityBasis c) := by
  have hs := TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single_at
    (0 : TimeVelocityMultiIndex N) c w z (by
      simpa [TimeVelocityMultiIndex.order, VelocityMultiIndex.order,
        TimeVelocityMultiIndex.timeOrder, TimeVelocityMultiIndex.velocity, zero_add] using
        (hw.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).contDiffAt)
  have hzero : TimeVelocityMultiIndex.coordinateIteratedFDeriv
      (0 : TimeVelocityMultiIndex N) w = w := by
    funext y
    exact TimeVelocityMultiIndex.coordinateIteratedFDeriv_zero w y
  simpa only [zero_add, hzero] using hs

/-- For a smooth function the scalar residual is the existing ABP operator. -/
theorem scalar_residual_eq_parabolicOperator
    {N : ℕ} (a : TimeVelocity N → PDE.Mat N)
    (w : TimeVelocity N → ℝ) (hw : ContDiff ℝ 2 w) (z : TimeVelocity N) :
    residual a w z = parabolicOperator (fun t v => a (t, v)) w z := by
  have ht : scalarTimeDerivative w z = timeDerivative w z := by
    rw [scalarTimeDerivative_eq_coordinateIteratedFDeriv_of_contDiff_two hw z,
      coordinate_single_smooth w hw]
    rfl
  have hh : scalarSpatialHessian w z = velocityHessian w z := by
    ext i j
    rw [scalarSpatialHessian_apply_eq_coordinateIteratedFDeriv_of_contDiff_two hw z i j]
    have ho : TimeVelocityMultiIndex.order
        (Pi.single (velocityCoord j) 1 : TimeVelocityMultiIndex N) + 1 = 2 := by
      simp only [TimeVelocityMultiIndex.order_single]
    have hs := TimeVelocityMultiIndex.coordinateIteratedFDeriv_add_single_at
      (Pi.single (velocityCoord j) 1) (velocityCoord i) w z (by
        simpa only [TimeVelocityMultiIndex.order_single, Nat.cast_one,
          show (1 : WithTop ℕ∞) + 1 = 2 from rfl] using! hw.contDiffAt)
    have hf : TimeVelocityMultiIndex.coordinateIteratedFDeriv
        (Pi.single (velocityCoord j) 1) w =
        (fun y => fderiv ℝ w y (timeVelocityBasis (velocityCoord j))) := by
      funext y
      exact coordinate_single_smooth w hw _ y
    rw [hs, hf]
    have hd := ((hw.fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num)) z
    rw [fderiv_clm_apply hd (differentiableAt_const (c :=
      timeVelocityBasis (velocityCoord j)))]
    simp [timeVelocityBasis_velocity, velocityHessian, PDE.basisVec]
  simp only [residual, parabolicOperator, coefficientAt, ht, hh]

end HypoellipticAleksandrov.Parabolic.KrylovEstimate

module

public import HypoellipticAleksandrov.Parabolic.KrylovCylinder
public import HypoellipticAleksandrov.Parabolic.KrylovEstimate.ScalarAffine
public import HypoellipticAleksandrov.Parabolic.TimeReversal
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Reflect-and-rescale calculus for the localized occupation estimate

The proof of the companion paper, Proposition 4.2, applies Krylov's estimate to
`u(t, y) = V(1 - R² t, v_* + R y)`.  This file proves the slice calculus of that map for the
anisotropic carriers `IsScalarC12On` and `IsScalarC12UpTo`: the map factors as the time
reflection `(r, y) ↦ (1 - r, y)` followed by the parabolic affine map
`(t, y) ↦ (R² t, v_* + R y)`, and the derivative identities
`u_t = -R² V_r`, `D_y u = R D_v V`, `D_y² u = R² D_v² V` hold.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter
open scoped Topology

variable {d : ℕ}

/-- The reflect-and-rescale map `(t, y) ↦ (1 - R² t, v_* + R y)`. -/
def reflectScale (R : ℝ) (vStar : PDE.Vec d) (z : TimeVelocity d) : TimeVelocity d :=
  (1 - R ^ 2 * z.1, vStar + R • z.2)

/-- The reflect-and-rescale map is the time reflection of a parabolic affine map. -/
theorem reflectScale_eq (R : ℝ) (vStar : PDE.Vec d) :
    reflectScale R vStar = timeReflection ∘ parabolicAffine 0 vStar R := by
  funext z
  simp only [reflectScale, Function.comp_apply, timeReflection, parabolicAffine, zero_add]

/-- The reflect-and-rescale map is continuous. -/
theorem continuous_reflectScale (R : ℝ) (vStar : PDE.Vec d) :
    Continuous (reflectScale R vStar) := by
  unfold reflectScale
  fun_prop

/-- Reflection reverses the scalar time derivative. -/
theorem scalarTimeDerivative_timeReflectedScalar (V : TimeVelocity d → ℝ)
    (z : TimeVelocity d) :
    scalarTimeDerivative (timeReflectedScalar V) z =
      -scalarTimeDerivative V (timeReflection z) := by
  unfold scalarTimeDerivative timeReflectedScalar timeReflection
  exact deriv_comp_const_sub (f := fun r : ℝ => V (r, z.2)) (a := 1) (x := z.1)

/-- Reflection preserves the scalar spatial gradient. -/
theorem scalarSpatialGradient_timeReflectedScalar (V : TimeVelocity d → ℝ)
    (z : TimeVelocity d) :
    scalarSpatialGradient (timeReflectedScalar V) z =
      scalarSpatialGradient V (timeReflection z) :=
  rfl

/-- Reflection preserves the scalar spatial Hessian. -/
theorem scalarSpatialHessian_timeReflectedScalar (V : TimeVelocity d → ℝ)
    (z : TimeVelocity d) :
    scalarSpatialHessian (timeReflectedScalar V) z =
      scalarSpatialHessian V (timeReflection z) :=
  rfl

/-- Scalar `C^{1,2}` regularity transfers through the time reflection. -/
theorem isScalarC12On_timeReflectedScalar {V : TimeVelocity d → ℝ} {D : Set (TimeVelocity d)}
    (hV : IsScalarC12On V D) :
    IsScalarC12On (timeReflectedScalar V) (timeReflection ⁻¹' D) := by
  have hm : MapsTo (timeReflection (d := d)) (timeReflection ⁻¹' D) D := fun _ hz => hz
  have hc : ContinuousOn (timeReflection (d := d)) (timeReflection ⁻¹' D) :=
    continuous_timeReflection.continuousOn
  refine ⟨hV.continuousOn.comp hc hm, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have h1 := hV.timeSlice_differentiableAt (z := timeReflection z) hz
    have h2 : DifferentiableAt ℝ (fun r : ℝ => 1 - r) z.1 := by fun_prop
    have h3 : DifferentiableAt ℝ (fun r : ℝ => V (r, z.2)) (1 - z.1) := h1
    exact h3.comp z.1 h2
  · intro z hz
    exact hV.spatialSlice_contDiffAt (z := timeReflection z) hz
  · refine ((hV.continuousOn_scalarTimeDerivative.comp hc hm).neg).congr ?_
    intro z _
    exact scalarTimeDerivative_timeReflectedScalar V z
  · exact hV.continuousOn_scalarSpatialGradient.comp hc hm
  · exact hV.continuousOn_scalarSpatialHessian.comp hc hm

private theorem gradient_affine_aux (f : PDE.Vec d → ℝ)
    (v : PDE.Vec d) (ρ : ℝ) (x : PDE.Vec d)
    (hf : DifferentiableAt ℝ f (v + ρ • x)) :
    PDE.classicalGradient (fun y => f (v + ρ • y)) x =
      ρ • PDE.classicalGradient f (v + ρ • x) := by
  have ha : HasFDerivAt (fun y : PDE.Vec d => v + ρ • y)
      (ρ • ContinuousLinearMap.id ℝ (PDE.Vec d)) x := by
    simpa only [Pi.smul_def, id_eq] using! ((hasFDerivAt_id x).const_smul ρ).const_add v
  have hc := hf.hasFDerivAt.comp x ha
  ext i
  simp only [PDE.classicalGradient, Pi.smul_apply, smul_eq_mul]
  simp only [Function.comp_def] at hc
  rw [hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]

/-- The spatial gradient under a parabolic affine pullback. -/
theorem scalarSpatialGradient_parabolicAffine (u : TimeVelocity d → ℝ) (b : ℝ)
    (v : PDE.Vec d) (ρ : ℝ) (z : TimeVelocity d)
    (hu : DifferentiableAt ℝ (fun y : PDE.Vec d => u (b + ρ ^ 2 * z.1, y)) (v + ρ • z.2)) :
    scalarSpatialGradient (u ∘ parabolicAffine b v ρ) z =
      ρ • scalarSpatialGradient u (parabolicAffine b v ρ z) :=
  gradient_affine_aux (fun y => u (b + ρ ^ 2 * z.1, y)) v ρ z.2 hu

/-- `C^{1,2}` regularity and the derivative identities for `V ∘ reflectScale`. -/
theorem isScalarC12On_reflectScale {V : TimeVelocity d → ℝ} {D : Set (TimeVelocity d)}
    (hD : IsOpen D) (hV : IsScalarC12On V D) {R : ℝ} (hR : 0 < R) (vStar : PDE.Vec d) :
    IsScalarC12On (fun z => V (reflectScale R vStar z)) (reflectScale R vStar ⁻¹' D) ∧
    ∀ z ∈ reflectScale R vStar ⁻¹' D,
      scalarTimeDerivative (fun w => V (reflectScale R vStar w)) z =
        -R ^ 2 * scalarTimeDerivative V (reflectScale R vStar z) ∧
      scalarSpatialGradient (fun w => V (reflectScale R vStar w)) z =
        R • scalarSpatialGradient V (reflectScale R vStar z) ∧
      scalarSpatialHessian (fun w => V (reflectScale R vStar w)) z =
        R ^ 2 • scalarSpatialHessian V (reflectScale R vStar z) := by
  have hD' : IsOpen (timeReflection ⁻¹' D : Set (TimeVelocity d)) :=
    hD.preimage continuous_timeReflection
  have hV' := isScalarC12On_timeReflectedScalar hV
  have hfun : (fun z => V (reflectScale R vStar z)) =
      timeReflectedScalar V ∘ parabolicAffine 0 vStar R := by
    funext z
    simp only [Function.comp_apply, timeReflectedScalar_apply]
    exact congrArg V (congrFun (reflectScale_eq R vStar) z)
  have hpre : parabolicAffine 0 vStar R ⁻¹' (timeReflection ⁻¹' D) =
      reflectScale R vStar ⁻¹' D := by
    rw [reflectScale_eq, Set.preimage_comp]
  obtain ⟨hC, hform⟩ := KrylovEstimate.scalarC12On_affine_pullback hD'
    (timeReflectedScalar V) hV' 0 vStar hR
  rw [hpre] at hC hform
  rw [hfun]
  refine ⟨hC, ?_⟩
  intro z hz
  have hz' : z ∈ parabolicAffine 0 vStar R ⁻¹' (timeReflection ⁻¹' D) := by
    rw [hpre]; exact hz
  have hΦ : reflectScale R vStar z = timeReflection (parabolicAffine 0 vStar R z) :=
    congrFun (reflectScale_eq R vStar) z
  obtain ⟨ht, hh⟩ := hform z hz
  refine ⟨?_, ?_, ?_⟩
  · rw [ht, scalarTimeDerivative_timeReflectedScalar, hΦ]
    ring
  · have hslice := (hV'.spatialSlice_contDiffAt hz').differentiableAt (by norm_num)
    rw [scalarSpatialGradient_parabolicAffine _ 0 vStar R z hslice,
      scalarSpatialGradient_timeReflectedScalar, hΦ]
  · rw [hh, scalarSpatialHessian_timeReflectedScalar, hΦ]

/-- Scalar `C^{1,2}` regularity restricts to subsets. -/
theorem isScalarC12On_mono' {u : TimeVelocity d → ℝ} {D E : Set (TimeVelocity d)}
    (h : IsScalarC12On u D) (hE : E ⊆ D) : IsScalarC12On u E :=
  ⟨h.1.mono hE, fun z hz => h.2.1 z (hE hz), fun z hz => h.2.2.1 z (hE hz),
    h.2.2.2.1.mono hE, h.2.2.2.2.1.mono hE, h.2.2.2.2.2.mono hE⟩

/-- Closure regularity transfers through `reflectScale`, given inclusions of the carriers. -/
theorem isScalarC12UpTo_reflectScale {V : TimeVelocity d → ℝ}
    {QV KV Q K : Set (TimeVelocity d)}
    (hQV : IsOpen QV) (hV : IsScalarC12UpTo V QV KV) {R : ℝ} (hR : 0 < R)
    (vStar : PDE.Vec d)
    (hQ : Q ⊆ reflectScale R vStar ⁻¹' QV) (hK : K ⊆ reflectScale R vStar ⁻¹' KV) :
    IsScalarC12UpTo (fun z => V (reflectScale R vStar z)) Q K := by
  obtain ⟨hC, hcont, dt, dv, dvv, hdt, hdv, hdvv, e1, e2, e3⟩ := hV
  obtain ⟨hC', hform⟩ := isScalarC12On_reflectScale hQV hC hR vStar
  have hc := (continuous_reflectScale R vStar).continuousOn (s := K)
  have hm : MapsTo (reflectScale R vStar) K KV := fun z hz => hK hz
  refine ⟨isScalarC12On_mono' hC' hQ, hcont.comp hc hm,
    fun z => -R ^ 2 * dt (reflectScale R vStar z),
    fun z => R • dv (reflectScale R vStar z),
    fun z => R ^ 2 • dvv (reflectScale R vStar z), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hdt.comp hc hm).const_mul (-R ^ 2)
  · exact (hdv.comp hc hm).const_smul R
  · exact (hdvv.comp hc hm).const_smul (R ^ 2)
  · intro z hz
    obtain ⟨h1, -, -⟩ := hform z (hQ hz)
    show -R ^ 2 * dt (reflectScale R vStar z) = _
    rw [h1, e1 (hQ hz)]
  · intro z hz
    obtain ⟨-, h2, -⟩ := hform z (hQ hz)
    show R • dv (reflectScale R vStar z) = _
    rw [h2, e2 (hQ hz)]
  · intro z hz
    obtain ⟨-, -, h3⟩ := hform z (hQ hz)
    show R ^ 2 • dvv (reflectScale R vStar z) = _
    rw [h3, e3 (hQ hz)]

/-- The scaled backward operator: `u_t - a : D² u = -R² (V_r + B : D² V)` at `reflectScale`. -/
theorem scaled_operator_eq {V : TimeVelocity d → ℝ} {D : Set (TimeVelocity d)}
    (hD : IsOpen D) (hV : IsScalarC12On V D) {R : ℝ} (hR : 0 < R) (vStar : PDE.Vec d)
    (B : CoefficientField d) {z : TimeVelocity d} (hz : z ∈ reflectScale R vStar ⁻¹' D) :
    scalarTimeDerivative (fun w => V (reflectScale R vStar w)) z -
        matrixContraction (coefficientAt B (reflectScale R vStar z))
          (scalarSpatialHessian (fun w => V (reflectScale R vStar w)) z) =
      -R ^ 2 * (scalarTimeDerivative V (reflectScale R vStar z) +
        matrixContraction (coefficientAt B (reflectScale R vStar z))
          (scalarSpatialHessian V (reflectScale R vStar z))) := by
  obtain ⟨-, hform⟩ := isScalarC12On_reflectScale hD hV hR vStar
  obtain ⟨h1, -, h3⟩ := hform z hz
  rw [h1, h3, HypoellipticAleksandrov.matrixContraction_smul_right]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Occupation

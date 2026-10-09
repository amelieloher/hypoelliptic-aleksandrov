module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.KineticPullbackJets
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Setting
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.SmoothEstimateEllipticity
public import HypoellipticAleksandrov.Parabolic.Scaling
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExternalRegularity
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic

/-! # Kinetic affine normalization of supplied classical solutions -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set Filter MeasureTheory Parabolic Holder
open scoped Topology MatrixOrder ContDiff Matrix.Norms.Elementwise

/-- The time--velocity coefficient in the normalized physical coordinates. -/
def kineticPullbackCoefficient {d : ℕ} (A : CoefficientField d)
    (P₀ : KineticPoint d) (R : ℝ) : CoefficientField d :=
  fun t v => A (P₀.time + R ^ 2 * t) (P₀.velocity + R • v)

/-- Normalization preserves smoothness of the time--velocity coefficient. -/
theorem kineticPullbackCoefficient_smooth {d : ℕ} {A : CoefficientField d}
    (hA : IsSmoothCoefficient A) (P₀ : KineticPoint d) (R : ℝ) :
    IsSmoothCoefficient (kineticPullbackCoefficient A P₀ R) := by
  exact hA.comp (show ContDiff ℝ ∞ (fun z : TimeVelocity d =>
    (P₀.time + R ^ 2 * z.1, P₀.velocity + R • z.2)) by fun_prop)

/-- Normalization preserves the symmetry and the literal ellipticity constants. -/
theorem kineticPullbackCoefficient_bounds {d : ℕ} {A : CoefficientField d}
    {lam Lam : ℝ} (hs : IsSymmetricCoefficient A)
    (hlo : HasLowerEllipticity lam A) (hhi : HasUpperEllipticity Lam A)
    (P₀ : KineticPoint d) (R : ℝ) :
    IsSymmetricCoefficient (kineticPullbackCoefficient A P₀ R) ∧
    HasLowerEllipticity lam (kineticPullbackCoefficient A P₀ R) ∧
    HasUpperEllipticity Lam (kineticPullbackCoefficient A P₀ R) :=
  ⟨fun t v => hs (P₀.time + R ^ 2 * t) (P₀.velocity + R • v),
    fun t v => hlo (P₀.time + R ^ 2 * t) (P₀.velocity + R • v),
    fun t v => hhi (P₀.time + R ^ 2 * t) (P₀.velocity + R • v)⟩

/-- The anisotropic classical class is preserved by the moving affine pullback. -/
theorem kineticPullback_C112 {d : ℕ} {u : KineticPoint d → ℝ}
    {D : Set (KineticPoint d)} (hD : IsOpen D) (hu : IsKineticC112On u D)
    (P₀ : KineticPoint d) (R : ℝ) :
    IsKineticC112On (kineticPullback u P₀ R) (kineticAffine P₀ R ⁻¹' D) := by
  let E := kineticAffine P₀ R ⁻¹' D
  have hc := (continuous_kineticAffine P₀ R).continuousOn (s := E)
  have hmap : ∀ P ∈ E, kineticAffine P₀ R P ∈ D := fun _ h => h
  have ht := hu.continuousOn_kineticTimeDerivative.comp hc hmap
  have hx := hu.continuousOn_kineticPositionGradient.comp hc hmap
  have hv := hu.continuousOn_kineticVelocityGradient.comp hc hmap
  have hh := hu.continuousOn_kineticVelocityHessian.comp hc hmap
  refine ⟨hu.continuousOn.comp hc hmap, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro P hp
    exact (kineticPullback_time_hasDerivAt hD hu P₀ R P hp).differentiableAt
  · intro P hp
    let a := P₀.position + (R ^ 2 * P.time) • P₀.velocity
    have hs := hu.positionSlice_contDiffAt hp
    have he : (kineticAffine P₀ R P).position = a + R ^ 3 • P.position := by
      dsimp [kineticAffine, a]
      abel_nf
    rw [he] at hs
    have h := hs.comp P.position
      (show ContDiffAt ℝ 1 (fun x : PDE.Vec d => a + R ^ 3 • x) P.position by fun_prop)
    convert h using 1
    funext x
    simp only [kineticPullback, Function.comp_def, kineticAffine, a]
    congr 1
    abel_nf
  · intro P hp
    change ContDiffAt ℝ 2
      (fun v => u ⟨P₀.time + R ^ 2 * P.time,
        (kineticAffine P₀ R P).position, P₀.velocity + R • v⟩) P.velocity
    have h := (hu.velocitySlice_contDiffAt hp).comp P.velocity
      (show ContDiffAt ℝ 2 (fun v : PDE.Vec d => P₀.velocity + R • v)
        P.velocity by fun_prop)
    exact h
  · have hdot : ContinuousOn
        (fun P => PDE.vecDot P₀.velocity (kineticPositionGradient u
          (kineticAffine P₀ R P))) E := by
      unfold PDE.vecDot
      apply continuousOn_finsetSum
      intro i _
      exact continuousOn_const.mul ((continuous_apply i).comp_continuousOn hx)
    exact ((ht.add hdot).const_smul (R ^ 2)).congr
      (fun P hp => kineticPullback_timeDerivative hD hu P₀ R P hp)
  · exact (hx.const_smul (R ^ 3)).congr
      (fun P hp => kineticPullback_positionGradient hu P₀ R P hp)
  · exact (hv.const_smul R).congr
      (fun P hp => kineticPullback_velocityGradient hu P₀ R P hp)
  · exact (hh.const_smul (R ^ 2)).congr
      (fun P hp => kineticPullback_velocityHessian hu P₀ R P hp)

/-- The normalized operator is the original operator multiplied by the time dilation. -/
theorem kineticPullback_operator {d : ℕ} {u : KineticPoint d → ℝ}
    {D : Set (KineticPoint d)} (hD : IsOpen D) (hu : IsKineticC112On u D)
    (A : CoefficientField d) (P₀ : KineticPoint d) (R : ℝ) (P : KineticPoint d)
    (hp : kineticAffine P₀ R P ∈ D) :
    backwardOperatorOfTimeVelocityCoefficient (kineticPullbackCoefficient A P₀ R)
      (kineticPullback u P₀ R) P =
    R ^ 2 * backwardOperatorOfTimeVelocityCoefficient A u (kineticAffine P₀ R P) := by
  rw [backwardOperatorOfTimeVelocityCoefficient_apply,
    kineticPullback_timeDerivative hD hu P₀ R P hp,
    kineticPullback_positionGradient hu P₀ R P hp,
    kineticPullback_velocityHessian hu P₀ R P hp,
    matrixContraction_smul_right, backwardOperatorOfTimeVelocityCoefficient_apply]
  have hd₁ : ∀ (c : ℝ) (v g : PDE.Vec d),
      PDE.vecDot v (c • g) = c * PDE.vecDot v g := by
    intro c v g
    simp only [PDE.vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hd₂ : ∀ (c : ℝ) (v w g : PDE.Vec d),
      PDE.vecDot (v + c • w) g = PDE.vecDot v g + c * PDE.vecDot w g := by
    intro c v w g
    simp only [PDE.vecDot, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  rw [hd₁, kineticAffine_velocity, hd₂]
  simp only [kineticPullbackCoefficient, kineticAffine_time]
  ring

/-- The classical kinetic operator is continuous on its open solution domain. -/
theorem continuousOn_backwardOperator {d : ℕ} {u : KineticPoint d → ℝ}
    {D : Set (KineticPoint d)} (hu : IsKineticC112On u D)
    {A : CoefficientField d} (hA : IsContinuousCoefficient A) :
    ContinuousOn (backwardOperatorOfTimeVelocityCoefficient A u) D := by
  have hc : ContinuousOn (fun P : KineticPoint d => A P.time P.velocity) D :=
    hA.comp (continuous_time.prodMk continuous_velocity) |>.continuousOn
  have hg := hu.continuousOn_kineticPositionGradient
  have hh := hu.continuousOn_kineticVelocityHessian
  change ContinuousOn (fun P => kineticTimeDerivative u P +
    (∑ i, P.velocity i * kineticPositionGradient u P i) -
    (∑ i, ∑ j, A P.time P.velocity i j * kineticVelocityHessian u P i j)) D
  refine (hu.continuousOn_kineticTimeDerivative.add ?_).sub ?_
  · apply continuousOn_finsetSum
    intro i _
    exact ((continuous_apply i).comp continuous_velocity).continuousOn.mul
      ((continuous_apply i).comp_continuousOn hg)
  · apply continuousOn_finsetSum
    intro i _
    apply continuousOn_finsetSum
    intro j _
    exact ((continuous_apply j).comp_continuousOn
      ((continuous_apply i).comp_continuousOn hc)).mul
      ((continuous_apply j).comp_continuousOn
        ((continuous_apply i).comp_continuousOn hh))

/-- A continuous classical equation holding almost everywhere holds at every interior point. -/
theorem backwardEquation_pointwise {d : ℕ} {u : KineticPoint d → ℝ}
    {D : Set (KineticPoint d)} (hD : IsOpen D) (hu : IsKineticC112On u D)
    {A : CoefficientField d} (hA : IsContinuousCoefficient A)
    (he : ∀ᵐ P ∂volume.restrict D, backwardOperatorOfTimeVelocityCoefficient A u P = 0) :
    ∀ P ∈ D, backwardOperatorOfTimeVelocityCoefficient A u P = 0 :=
  Evolution.eqOn_of_ae_eq_of_continuousOn_kinetic hD
    ((continuousOn_backwardOperator hu hA).comp
      (Evolution.evolutionHomeomorph d).continuous.continuousOn (fun _ h => h))
    continuousOn_const he

/-- Normalization supplies the pointwise homogeneous equation on the unit cylinder. -/
theorem kineticPullback_normalized {d : ℕ} {u : KineticPoint d → ℝ}
    (P₀ : KineticPoint d) {R : ℝ} (hR : 0 < R)
    (hu : IsKineticC112On u (backwardCylinder P₀ R))
    {A : CoefficientField d} (hA : IsSmoothCoefficient A)
    (he : ∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
      backwardOperatorOfTimeVelocityCoefficient A u P = 0) :
    IsKineticC112On (kineticPullback u P₀ R)
      (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1) ∧
    ∀ P ∈ backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1,
      backwardOperatorOfTimeVelocityCoefficient (kineticPullbackCoefficient A P₀ R)
        (kineticPullback u P₀ R) P = 0 := by
  have hD := isOpen_backwardCylinder P₀ R hR
  have hp : ∀ P ∈ backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1,
      kineticAffine P₀ R P ∈ backwardCylinder P₀ R :=
    fun P h => (kineticAffine_mem_cylinder P₀ P hR).mpr h
  have hreg := kineticPullback_C112 hD hu P₀ R
  have hreg' : IsKineticC112On (kineticPullback u P₀ R)
      (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1) := by
    exact ⟨hreg.1.mono hp, fun P h => hreg.2.1 P (hp P h),
      fun P h => hreg.2.2.1 P (hp P h), fun P h => hreg.2.2.2.1 P (hp P h),
      hreg.2.2.2.2.1.mono hp, hreg.2.2.2.2.2.1.mono hp,
      hreg.2.2.2.2.2.2.1.mono hp, hreg.2.2.2.2.2.2.2.mono hp⟩
  refine ⟨hreg', ?_⟩
  intro P hP
  rw [kineticPullback_operator hD hu A P₀ R P (hp P hP),
    backwardEquation_pointwise hD hu hA.continuous he _ (hp P hP), mul_zero]

end HypoellipticAleksandrov.KineticAleksandrov.LocalA

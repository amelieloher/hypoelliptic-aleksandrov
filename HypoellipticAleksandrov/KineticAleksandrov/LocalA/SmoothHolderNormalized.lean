module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.SmoothHolderGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ScalingSlices
public import HypoellipticAleksandrov.Parabolic.LocalHolder.Holder
public import HypoellipticAleksandrov.Parabolic.AffineScalarCalculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-! # Combine parabolic slice regularity with spatial control

The first-derivative premise of the internal combination lemma is discharged by the
exact spatial-bound input in SmoothHolder. Amplitude is the literal outer oscillation.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic Holder

/-- The transport forcing is bounded by the physical position differential. -/
theorem abs_position_transport_le {d : ℕ} (u : KineticPoint d → ℝ)
    (P : KineticPoint d) (v : PDE.Vec d) :
    |PDE.vecDot v (kineticPositionGradient u P)| ≤
      ‖fderiv ℝ (physicalPositionSlice u P) P.position‖ * PDE.vecEuclideanNorm v := by
  have he : PDE.vecDot v (kineticPositionGradient u P) =
      fderiv ℝ (physicalPositionSlice u P) P.position v := by
    rw [PDE.fderiv_apply_eq_vecDot_classicalGradient]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [he, ← Real.norm_eq_abs]
  exact ((fderiv ℝ (physicalPositionSlice u P) P.position).le_opNorm v).trans
    (mul_le_mul_of_nonneg_left (PDE.norm_le_vecEuclideanNorm v) (norm_nonneg _))

/-- The spatial displacement term is bounded by its kinetic Hölder power on the unit ball. -/
theorem position_displacement_le_kinetic_power {d : ℕ} {P Q : KineticPoint d}
    (hP : P.position ∈ PDE.euclideanBall 0 (1 / 8 : ℝ))
    (hQ : Q.position ∈ PDE.euclideanBall 0 (1 / 8 : ℝ))
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    PDE.vecEuclideanNorm (P.position - Q.position) ≤
      kineticIncrement (⟨0, 0, 0⟩ : KineticPoint d) P Q ^ α := by
  let x := PDE.vecEuclideanNorm (P.position - Q.position)
  have hx : 0 ≤ x := PDE.vecEuclideanNorm_nonneg _
  have hx1 : x ≤ 1 := by
    have h := PDE.vecEuclideanNorm_add_le P.position (-Q.position)
    have hp := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mp hP
    have hq := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mp hQ
    simp only [sub_zero] at hp hq
    simp only [PDE.vecEuclideanNorm_neg] at h
    change PDE.vecEuclideanNorm (P.position + -Q.position) ≤ _ at h
    dsimp only [x]
    change PDE.vecEuclideanNorm (P.position + -Q.position) ≤ 1
    linarith only [h, hp, hq]
  have hbase : x ^ (1 / 3 : ℝ) ≤
      kineticIncrement (⟨0, 0, 0⟩ : KineticPoint d) P Q := by
    dsimp only [kineticIncrement]
    simp only [smul_zero, sub_zero]
    exact le_add_of_nonneg_left (add_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
      (PDE.vecEuclideanNorm_nonneg _))
  calc
    x ≤ x ^ (α / 3) := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_ge' hx hx1 (by positivity : 0 ≤ α / 3)
          (by linarith only [hα1] : α / 3 ≤ 1)
    _ = (x ^ (1 / 3 : ℝ)) ^ α := by
      rw [← Real.rpow_mul hx]
      congr 1
      ring
    _ ≤ kineticIncrement (⟨0, 0, 0⟩ : KineticPoint d) P Q ^ α :=
      Real.rpow_le_rpow (Real.rpow_nonneg hx _) hbase hα.le

/-- Parabolic and spatial moduli give an oscillation-normalized kinetic estimate. -/
theorem normalized_holder_from_slice_jets
    (hLE : LiebermanEllipsoidDirichletStatement)
    (d : ℕ) (hd : 1 ≤ d) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (K : ℝ) (hK : 0 ≤ K) :
    ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ α < 1 ∧
      ∀ (A : CoefficientField d), IsSmoothCoefficient A → IsSymmetricCoefficient A →
      HasLowerEllipticity lam A → HasUpperEllipticity Lam A →
      ∀ (u : KineticPoint d → ℝ),
      ContinuousOn u (closure (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1)) →
      IsKineticC112On u (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1) →
      (∀ P ∈ backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1,
        backwardOperatorOfTimeVelocityCoefficient A u P = 0) →
      (∀ P ∈ backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) (3 / 4),
        ‖fderiv ℝ (physicalPositionSlice u P) P.position‖ ≤
          K * oscillationOn u (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1)) →
      ∀ P ∈ backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) (1 / 2),
      ∀ Q ∈ backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) (1 / 2),
        |u P - u Q| ≤ C * oscillationOn u
          (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1) *
          kineticIncrement (⟨0, 0, 0⟩ : KineticPoint d) P Q ^ α := by
  obtain ⟨Cp, α, hCp, hα, hα1, hpar⟩ :=
    parabolic_holder_of_bounded_source hLE d hd lam Lam hlam hLam
  refine ⟨Cp * (1 + K) + K, α, by positivity, hα, hα1, ?_⟩
  intro A hA hs hlo hhi u hc hu he hdx P hP Q hQ
  let Z : KineticPoint d := ⟨0, 0, 0⟩
  let D := backwardCylinder Z 1
  let O := oscillationOn u D
  obtain ⟨habc, hbbc⟩ := bounded_values_of_compact
    (isCompact_closure_backwardCylinder Z 1 (by norm_num)) hc
  have hab := habc.mono (image_mono subset_closure)
  have hbb := hbbc.mono (image_mono subset_closure)
  have hO : 0 ≤ O := oscillationOn_nonneg (backwardCylinder_nonempty Z (by norm_num)) hab hbb
  obtain ⟨hPt, hPx⟩ := holder_half_coordinates hP
  obtain ⟨hQt, hQx⟩ := holder_half_coordinates hQ
  have houter : ∀ z ∈ scalarParabolicOpenCylinder (-1 / 4) 0
      (PDE.euclideanBall (0 : PDE.Vec d) (1 / 2)),
      z ∈ scalarParabolicOpenCylinder (-9 / 16) 0 (PDE.euclideanBall 0 (3 / 4)) := by
    intro z hz
    exact ⟨⟨by linarith only [hz.1.1], hz.1.2⟩,
      PDE.euclideanBall_mono (by norm_num) (by norm_num) hz.2⟩
  let B : KineticPoint d := ⟨-1 / 2, 0, 0⟩
  have hB : B ∈ D := by
    norm_num [B, D, Z, backwardCylinder, relativePosition, PDE.euclideanBall,
      PDE.euclideanSqDist, PDE.vecNormSq, PDE.vecDot]
  let w : TimeVelocity d → ℝ := fun z => 1 * u ⟨z.1, P.position, z.2⟩ + -u B
  obtain ⟨hw, hwe⟩ := normalized_slice_equation A u hu he P.position hPx
  have hw' := hw.const_mul_add_const 1 (-u B)
  have hwb : ∀ z ∈ scalarParabolicOpenCylinder (-9 / 16) 0
      (PDE.euclideanBall (0 : PDE.Vec d) (3 / 4)), |w z| ≤ (1 + K) * O := by
    intro z hz
    have h := abs_sub_le_oscillationOn hab hbb (normalized_slice_mem P.position hPx z hz) hB
    have hKO : 0 ≤ K * O := mul_nonneg hK hO
    dsimp only [w]
    simp only [one_mul, ← sub_eq_add_neg]
    dsimp only [O]
    linarith only [h, hKO]
  have hwf : ∀ z ∈ scalarParabolicOpenCylinder (-9 / 16) 0
      (PDE.euclideanBall (0 : PDE.Vec d) (3 / 4)),
      |scalarTimeDerivative w z - matrixContraction (coefficientAt A z)
        (scalarSpatialHessian w z)| ≤ (1 + K) * O := by
    intro z hz
    dsimp only [w]
    rw [scalarTimeDerivative_const_mul_add_const,
      scalarSpatialHessian_const_mul_add_const]
    simp only [one_mul, one_smul]
    rw [hwe z hz, abs_neg]
    have ht := abs_position_transport_le u ⟨z.1, P.position, z.2⟩ z.2
    have hv : PDE.vecEuclideanNorm z.2 ≤ 1 := by
      have h := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mp hz.2
      simp only [sub_zero] at h
      linarith only [h]
    have hbound := hdx _ (holder_slice_mem_inner P.position hPx z hz)
    have h := ht.trans (mul_le_mul hbound hv (PDE.vecEuclideanNorm_nonneg _) (mul_nonneg hK hO))
    linarith only [h, hO]
  have hslice := hpar A hA hs hlo hhi w ((1 + K) * O) (by positivity) hw'
    hwb hwf (P.time, P.velocity) hPt (Q.time, Q.velocity) hQt
  have hslice' : |u P - u ⟨Q.time, P.position, Q.velocity⟩| ≤
      Cp * ((1 + K) * O) * parabolicDistance (P.time, P.velocity) (Q.time, Q.velocity) ^ α := by
    convert hslice using 1
    dsimp only [w]
    congr 1
    ring
  have hdiff : ∀ x ∈ PDE.euclideanBall (0 : PDE.Vec d) (1 / 8),
      DifferentiableAt ℝ (fun x => u ⟨Q.time, x, Q.velocity⟩) x := by
    intro x hx
    exact ((hu.positionSlice_contDiffAt
      (normalized_slice_mem x hx _ (houter _ hQt))).differentiableAt (by norm_num))
  have hbound : ∀ x ∈ PDE.euclideanBall (0 : PDE.Vec d) (1 / 8),
      ‖fderiv ℝ (fun x => u ⟨Q.time, x, Q.velocity⟩) x‖ ≤ K * O := by
    intro x hx
    exact hdx _ (holder_slice_mem_inner x hx _ (houter _ hQt))
  have hspace := Convex.norm_image_sub_le_of_norm_fderiv_le
    hdiff hbound (PDE.convex_euclideanBall (0 : PDE.Vec d) (1 / 8)) hQx hPx
  have hspace' : |u ⟨Q.time, P.position, Q.velocity⟩ - u Q| ≤
      K * O * PDE.vecEuclideanNorm (P.position - Q.position) := by
    rw [Real.norm_eq_abs] at hspace
    exact hspace.trans (mul_le_mul_of_nonneg_left
      (PDE.norm_le_vecEuclideanNorm _) (mul_nonneg hK hO))
  have hpdist : parabolicDistance (P.time, P.velocity) (Q.time, Q.velocity) ≤
      kineticIncrement Z P Q := by
    exact le_add_of_nonneg_right (Real.rpow_nonneg (PDE.vecEuclideanNorm_nonneg _) _)
  have hdist : 0 ≤ parabolicDistance (P.time, P.velocity) (Q.time, Q.velocity) :=
    add_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (PDE.vecEuclideanNorm_nonneg _)
  have hpower := Real.rpow_le_rpow hdist hpdist hα.le
  have hxpower := position_displacement_le_kinetic_power hPx hQx hα hα1
  calc
    |u P - u Q| ≤ |u P - u ⟨Q.time, P.position, Q.velocity⟩| +
        |u ⟨Q.time, P.position, Q.velocity⟩ - u Q| := abs_sub_le _ _ _
    _ ≤ Cp * ((1 + K) * O) * parabolicDistance (P.time, P.velocity) (Q.time, Q.velocity) ^ α +
        K * O * PDE.vecEuclideanNorm (P.position - Q.position) := add_le_add hslice' hspace'
    _ ≤ Cp * ((1 + K) * O) * kineticIncrement Z P Q ^ α +
        K * O * kineticIncrement Z P Q ^ α := by gcongr
    _ = (Cp * (1 + K) + K) * O * kineticIncrement Z P Q ^ α := by ring

end HypoellipticAleksandrov.KineticAleksandrov.LocalA

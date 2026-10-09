module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullCutoffRawHessian
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullDensity
import HypoellipticAleksandrov.LinearAlgebra.LoewnerEntryBound
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

/-! # Uniform almost-everywhere operator bound for the physical near-full cutoff -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set MeasureTheory Parabolic
open scoped MatrixOrder

/-- The unit jet expression is jointly continuous in point and matrix entries. -/
theorem continuous_unitCutoffJet {d : ℕ}
    {f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Continuous (fun z : KineticPoint d × PDE.Mat d =>
      fderiv ℝ f (KineticPoint.equivProd d z.1) (1, (z.1.velocity, 0)) -
        matrixContraction z.2 (sliceHessian (unitCutoffVelocitySlice f z.1) z.1.velocity)) := by
  have hD : Continuous (fun z : KineticPoint d × PDE.Mat d =>
      fderiv ℝ f (KineticPoint.equivProd d z.1) (1, (z.1.velocity, 0))) :=
    (continuous_unitCutoffTransport hf).comp continuous_fst
  apply hD.sub
  have hH : Continuous (fun z : KineticPoint d × PDE.Mat d =>
      sliceHessian (unitCutoffVelocitySlice f z.1) z.1.velocity) :=
    (continuous_unitCutoffVelocityHessian hf).comp continuous_fst
  unfold matrixContraction
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact ((continuous_apply j).comp ((continuous_apply i).comp continuous_snd)).mul
    ((continuous_apply j).comp ((continuous_apply i).comp hH))

/-- Compact unit geometry gives a matrix-entry-uniform bound on the cutoff jet. -/
theorem exists_unitCutoffJet_bound {d : ℕ}
    {f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (Lam : ℝ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ Q ∈ closure
      (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1),
      ∀ B : PDE.Mat d, (∀ i j, |B i j| ≤ |Lam|) →
        |fderiv ℝ f (KineticPoint.equivProd d Q) (1, (Q.velocity, 0)) -
          matrixContraction B (sliceHessian (unitCutoffVelocitySlice f Q) Q.velocity)| ≤ C₀ := by
  let K := closure (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1)
  let S : Set (PDE.Mat d) := {B | ∀ i j, B i j ∈ Icc (-|Lam|) |Lam|}
  have hK : IsCompact K := isCompact_closure_backwardCylinder _ 1 (by norm_num)
  have hS : IsCompact S :=
    isCompact_pi_infinite (fun _ => isCompact_pi_infinite (fun _ => isCompact_Icc))
  obtain ⟨M, hM⟩ := (hK.prod hS).exists_bound_of_continuousOn
    (continuous_unitCutoffJet hf).continuousOn
  refine ⟨max M 0, le_max_right _ _, fun Q hQ B hB => ?_⟩
  have hBS : B ∈ S := fun i j => abs_le.mp (hB i j)
  exact (show |fderiv ℝ f (KineticPoint.equivProd d Q) (1, (Q.velocity, 0)) -
    matrixContraction B (sliceHessian (unitCutoffVelocitySlice f Q) Q.velocity)| ≤ M by
      simpa only [Real.norm_eq_abs] using hM (Q, B) ⟨hQ, hBS⟩).trans (le_max_left _ _)

/-- Ellipticity and exact affine jets yield the source cutoff bound with uniform constants. -/
theorem exists_scaledUnitCutoff_operator_bound {d : ℕ}
    {f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (Lam : ℝ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ lam : ℝ, 0 < lam →
      ∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
      ∀ (P₀ : KineticPoint d) (R ell : ℝ), 0 < R → 0 ≤ ell →
      ∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)),
        |backwardOperator A (scaledUnitCutoff f P₀ R ell) P| ≤ C₀ * ell * (R ^ 2)⁻¹ := by
  obtain ⟨C₀, hC₀, hbound⟩ := exists_unitCutoffJet_bound hf Lam
  refine ⟨C₀, hC₀, fun lam hlam A hA P₀ R ell hR hell => ?_⟩
  have hQ := isOpen_backwardCylinder P₀ R hR
  filter_upwards [ae_restrict_mem hQ.measurableSet,
    ae_restrict_of_ae hA.2.2.1, ae_restrict_of_ae hA.2.2.2] with P hP hl hu
  have hunit : kineticAffineInverse P₀ R P ∈
      backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 := by
    apply (kineticAffine_mem_cylinder P₀ _ hR).mp
    simpa only [kineticAffine_apply_inverse P₀ hR.ne' P] using hP
  have hB : ∀ i j, |fullKineticCoefficientAt A P i j| ≤ |Lam| :=
    fun i j =>
      (HypoellipticAleksandrov.abs_apply_le_of_loewner hlam hl hu i j).trans (le_abs_self Lam)
  have hb := hbound _ (subset_closure hunit) _ hB
  rw [scaledUnitCutoff_backwardOperator hf, abs_mul,
    abs_of_nonneg (mul_nonneg hell (inv_nonneg.mpr (sq_nonneg R)))]
  calc
    _ ≤ ell * (R ^ 2)⁻¹ * C₀ :=
      mul_le_mul_of_nonneg_left hb (mul_nonneg hell (inv_nonneg.mpr (sq_nonneg R)))
    _ = C₀ * ell * (R ^ 2)⁻¹ := by ring

end HypoellipticAleksandrov.KineticAleksandrov.Holder

module

public import HypoellipticAleksandrov.LinearAlgebra.LoewnerEntryBound
public import HypoellipticAleksandrov.Parabolic.ScalarClassical
public import HypoellipticAleksandrov.Parabolic.WeakDerivatives
public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApproxSquareNorm
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-! # Time derivative control from the homogeneous equation

The literal principal contraction is bounded by Hessian energy using ellipticity and
finite-dimensional Cauchy--Schwarz.
-/

@[expose] public section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open MeasureTheory Set
open scoped BigOperators MatrixOrder

/-- Entry bounds control the square of the literal principal contraction. -/
theorem principal_contraction_sq_le {d : ℕ} (A H : PDE.Mat d)
    (L : ℝ) (hL : 0 ≤ L) (hA : ∀ i j, |A i j| ≤ L) :
    (∑ i, ∑ j, A i j * H j i) ^ 2 ≤
      (d : ℝ) ^ 2 * L ^ 2 * ∑ i, ∑ j, H j i ^ 2 := by
  classical
  have hcs : (∑ i, ∑ j, A i j * H j i) ^ 2 ≤
      (∑ i, ∑ j, A i j ^ 2) * ∑ i, ∑ j, H j i ^ 2 := by
    simpa only [Fintype.sum_prod_type] using
      Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d × Fin d))
        (fun p => A p.1 p.2) (fun p => H p.2 p.1)
  have hb : (∑ i, ∑ j, A i j ^ 2) ≤ (d : ℝ) ^ 2 * L ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, L ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hL).2 (hA i j)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  exact hcs.trans (mul_le_mul_of_nonneg_right hb
    (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))))

/-- The homogeneous equation bounds time energy by the actual spatial Hessian energy. -/
theorem integral_local_time_derivative_sq_le {d : ℕ}
    (U : Set (TimeVelocity d)) (hU : MeasurableSet U)
    (u : TimeVelocity d → ℝ) (A : CoefficientField d)
    (L : ℝ) (hL : 0 ≤ L)
    (hA : ∀ z ∈ U, ∀ i j, |A z.1 z.2 i j| ≤ L)
    (ht : MemLp (scalarTimeDerivative u) 2 (timeVelocityVolumeOn U))
    (hh : ∀ i j, MemLp (fun z => scalarSpatialHessian u z i j) 2
      (timeVelocityVolumeOn U))
    (heq : ∀ z ∈ U, scalarTimeDerivative u z +
      matrixContraction (coefficientAt A z) (scalarSpatialHessian u z) = 0) :
    (∫ z in U, scalarTimeDerivative u z ^ 2) ≤
      (d : ℝ) ^ 2 * L ^ 2 * ∫ z in U,
        ∑ i, ∑ j, scalarSpatialHessian u z j i ^ 2 := by
  classical
  have hti : IntegrableOn (fun z => scalarTimeDerivative u z ^ 2) U := by
    simpa only [Real.norm_eq_abs, sq_abs, timeVelocityVolumeOn, IntegrableOn] using
      ht.integrable_norm_pow
      (by norm_num)
  have hhi (j i : Fin d) : IntegrableOn
      (fun z => scalarSpatialHessian u z j i ^ 2) U := by
    simpa only [Real.norm_eq_abs, sq_abs, timeVelocityVolumeOn, IntegrableOn] using
      (hh j i).integrable_norm_pow (by norm_num)
  have hs : IntegrableOn (fun z => ∑ i, ∑ j, scalarSpatialHessian u z j i ^ 2) U :=
    integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hhi j i))
  have hp : ∀ᵐ z ∂volume.restrict U,
      scalarTimeDerivative u z ^ 2 ≤
        (d : ℝ) ^ 2 * L ^ 2 * ∑ i, ∑ j, scalarSpatialHessian u z j i ^ 2 := by
    apply ae_restrict_of_forall_mem hU
    intro z hz
    have he := heq z hz
    have hsym : (∑ i, ∑ j, A z.1 z.2 i j * scalarSpatialHessian u z i j) =
        ∑ i, ∑ j, A z.1 z.2 j i * scalarSpatialHessian u z j i := Finset.sum_comm
    change scalarTimeDerivative u z +
      (∑ i, ∑ j, A z.1 z.2 i j * scalarSpatialHessian u z i j) = 0 at he
    have hv : scalarTimeDerivative u z =
        -(∑ i, ∑ j, A z.1 z.2 j i * scalarSpatialHessian u z j i) := by
      rw [hsym] at he
      exact eq_neg_of_add_eq_zero_left he
    rw [hv, neg_sq]
    exact principal_contraction_sq_le (fun i j => A z.1 z.2 j i)
      (scalarSpatialHessian u z) L hL (fun i j => hA z hz j i)
  have hb := integral_mono_ae hti (hs.const_mul ((d : ℝ) ^ 2 * L ^ 2)) hp
  simpa only [integral_const_mul] using hb

end HypoellipticAleksandrov.Parabolic.LocalHolder

module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApproxWeakLimit
public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApproxWeakTestingTools
public import HypoellipticAleksandrov.Coefficients.Ellipticity
public import HypoellipticAleksandrov.Parabolic.ParabolicLowOrderIndex
import Mathlib.Tactic.Ring

/-! # Passing homogeneous equations through the common weak subsequence

Coefficient-weighted compact tests preserve the actual time and Hessian equation. All
selected derivatives use the same subsequence.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter MeasureTheory Set
open scoped BigOperators Topology Matrix.Norms.Elementwise

/-- The literal homogeneous residual of a coherent family through at least weight two. -/
def homogeneousWeakFamilyResidual {d L : ℕ} {U : Set (TimeVelocity d)}
    {u : TimeVelocity d → ℝ} (hL : 2 ≤ L) (A : CoefficientField d)
    (D : ParabolicWeakDerivativeFamily d L U u) (z : TimeVelocity d) : ℝ :=
  D.representative (ParabolicDerivativeIndex.castLE hL
    (ParabolicDerivativeIndex.timeOne d)) z +
  ∑ i, ∑ j, A z.1 z.2 i j * D.representative
    (ParabolicDerivativeIndex.castLE hL (ParabolicDerivativeIndex.velocityTwo j i)) z

/-- Testing the literal residual equals the sum of its selected derivative pairings. -/
theorem integral_homogeneousWeakFamilyResidual_mul {d L : ℕ}
    {U : Set (TimeVelocity d)} {u : TimeVelocity d → ℝ}
    (hL : 2 ≤ L) (A : CoefficientField d) (hA : IsSmoothCoefficient A)
    (D : ParabolicWeakDerivativeFamily d L U u)
    (φ : TimeVelocity d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) :
    (∫ z in U, homogeneousWeakFamilyResidual hL A D z * φ z) =
      (∫ z in U, D.representative (ParabolicDerivativeIndex.castLE hL
        (ParabolicDerivativeIndex.timeOne d)) z * φ z) +
      ∑ i, ∑ j, ∫ z in U, D.representative
        (ParabolicDerivativeIndex.castLE hL (ParabolicDerivativeIndex.velocityTwo j i)) z *
        (A z.1 z.2 i j * φ z) := by
  classical
  have ht := integrableOn_weak_pairing _ φ (D.memLp
    (ParabolicDerivativeIndex.castLE hL (ParabolicDerivativeIndex.timeOne d))) hφ hc
  have hij (i j : Fin d) : IntegrableOn (fun z => D.representative
      (ParabolicDerivativeIndex.castLE hL (ParabolicDerivativeIndex.velocityTwo j i)) z *
      (A z.1 z.2 i j * φ z)) U := by
    have ha : ContDiff ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => A z.1 z.2 i j) :=
      (contDiff_apply ℝ ℝ j).comp ((contDiff_apply ℝ (Fin d → ℝ) i).comp hA)
    exact integrableOn_weak_pairing _ _ (D.memLp _) (ha.mul hφ)
      (HasCompactSupport.mul_left hc)
  have heq : (fun z => homogeneousWeakFamilyResidual hL A D z * φ z) =
      (fun z => D.representative (ParabolicDerivativeIndex.castLE hL
        (ParabolicDerivativeIndex.timeOne d)) z * φ z + ∑ i, ∑ j,
        D.representative (ParabolicDerivativeIndex.castLE hL
          (ParabolicDerivativeIndex.velocityTwo j i)) z * (A z.1 z.2 i j * φ z)) := by
    funext z
    simp only [homogeneousWeakFamilyResidual, add_mul, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq, integral_add ht (integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hij i j))),
    integral_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hij i j))]
  simp_rw [integral_finsetSum Finset.univ (fun j _ => hij _ j)]

/-- A common weak testing limit preserves the homogeneous equation almost everywhere. -/
theorem homogeneousWeakFamilyResidual_ae_eq_zero_of_testing_limit {d L : ℕ}
    (U : Set (TimeVelocity d)) (hU : IsOpen U)
    (hL : 2 ≤ L) (A : CoefficientField d) (hA : IsSmoothCoefficient A)
    (M : ℝ) (hAb : ∀ z ∈ U, ∀ i j, |A z.1 z.2 i j| ≤ M)
    (u : ℕ → TimeVelocity d → ℝ)
    (D : ∀ n, ParabolicWeakDerivativeFamily d L U (u n))
    (v : TimeVelocity d → ℝ) (E : ParabolicWeakDerivativeFamily d L U v)
    (hzero : ∀ n, homogeneousWeakFamilyResidual hL A (D n)
      =ᵐ[timeVelocityVolumeOn U] 0)
    (htest : ∀ β (φ : TimeVelocity d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ U →
      Tendsto (fun n => ∫ z in U, (D n).representative β z * φ z) atTop
        (𝓝 (∫ z in U, E.representative β z * φ z))) :
    homogeneousWeakFamilyResidual hL A E =ᵐ[timeVelocityVolumeOn U] 0 := by
  classical
  have hRm : ParabolicMemLpOn U 2 (homogeneousWeakFamilyResidual hL A E) := by
    apply (E.memLp _).add
    apply memLp_finsetSum
    intro i _
    apply memLp_finsetSum
    intro j _
    have ha : Continuous (fun z : TimeVelocity d => A z.1 z.2 i j) :=
      (continuous_apply j).comp ((continuous_apply i).comp hA.continuous)
    exact memLp_two_mul_of_bound hU.measurableSet _ _ ha (E.memLp _) M
      (fun z hz => hAb z hz i j)
  apply ae_eq_zero_of_weak_pairings hU _ hRm
  intro φ hφ hc hs
  have ht := htest (ParabolicDerivativeIndex.castLE hL
    (ParabolicDerivativeIndex.timeOne d)) φ hφ hc hs
  have hij (i j : Fin d) := by
    have ha : ContDiff ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => A z.1 z.2 i j) :=
      (contDiff_apply ℝ ℝ j).comp ((contDiff_apply ℝ (Fin d → ℝ) i).comp hA)
    exact htest (ParabolicDerivativeIndex.castLE hL
      (ParabolicDerivativeIndex.velocityTwo j i))
      (fun z => A z.1 z.2 i j * φ z) (ha.mul hφ)
      (HasCompactSupport.mul_left hc) (tsupport_mul_subset_right.trans hs)
  have hsum := ht.add (tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_finsetSum Finset.univ (fun j _ => hij i j)))
  have hn (n : ℕ) : (∫ z in U, homogeneousWeakFamilyResidual hL A (D n) z * φ z) = 0 := by
    have hz := hzero n
    rw [timeVelocityVolumeOn] at hz
    calc
      _ = ∫ z in U, (0 : ℝ) := integral_congr_ae (hz.mono fun z hz => by rw [hz]; simp)
      _ = 0 := integral_zero _ _
  have hvpair := integral_homogeneousWeakFamilyResidual_mul hL A hA E φ hφ hc
  have hseq : Tendsto (fun _n : ℕ => (0 : ℝ)) atTop
      (𝓝 (∫ z in U, homogeneousWeakFamilyResidual hL A E z * φ z)) := by
    rw [hvpair]
    apply hsum.congr'
    exact Eventually.of_forall (fun n =>
      (integral_homogeneousWeakFamilyResidual_mul hL A hA (D n) φ hφ hc).symm.trans (hn n))
  exact tendsto_nhds_unique hseq tendsto_const_nhds

end HypoellipticAleksandrov.Parabolic.LocalHolder

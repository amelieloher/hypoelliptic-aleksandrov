module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalSpatialSpacetime
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalTimeEnergy
import Mathlib.Tactic.Linarith

/-! # Local value energy for homogeneous backward equations

The spatial flux and coefficient derivative terms combine with the supplied equation to
give the literal time-energy pairing. The next estimate can absorb the lower-order terms.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter MeasureTheory Set
open scoped BigOperators Matrix.Norms.Elementwise

/-- The actual homogeneous equation identifies the localized flux integral with time energy. -/
theorem integral_scalar_local_value_energy_eq {d : ℕ}
    (a T : ℝ) (O : Set (PDE.Vec d)) (hO : IsOpen O)
    (u ρ : TimeVelocity d → ℝ) (hu : IsScalarC12On u (Ioo a T ×ˢ O))
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hc : HasCompactSupport ρ)
    (hsub : tsupport ρ ⊆ Ioo a T ×ˢ O)
    (A : CoefficientField d) (hA : IsSmoothCoefficient A)
    (heq : ∀ z ∈ Ioo a T ×ˢ O, scalarTimeDerivative u z +
      matrixContraction (coefficientAt A z) (scalarSpatialHessian u z) = 0) :
    (∫ z in Ioo a T ×ˢ O, ∑ i, ∑ j,
      (A z.1 z.2 i j * scalarSpatialGradient u z j *
        (ρ z ^ 2 * scalarSpatialGradient u z i +
          2 * ρ z * scalarSpatialGradient ρ z i * u z) +
        spatialPartial i (fun y => A z.1 y i j) z.2 *
          scalarSpatialGradient u z j * u z * ρ z ^ 2)) =
    ∫ z in Ioo a T ×ˢ O, scalarTimeDerivative u z * u z * ρ z ^ 2 := by
  classical
  let U := Ioo a T ×ˢ O
  have hU : IsOpen U := isOpen_Ioo.prod hO
  let L (i j : Fin d) (z : TimeVelocity d) :=
    A z.1 z.2 i j * scalarSpatialGradient u z j *
      (ρ z ^ 2 * scalarSpatialGradient u z i +
        2 * ρ z * scalarSpatialGradient ρ z i * u z)
  let R (i j : Fin d) (z : TimeVelocity d) :=
    (spatialPartial i (fun y => A z.1 y i j) z.2 * scalarSpatialGradient u z j +
      A z.1 z.2 i j * scalarSpatialHessian u z i j) * (u z * ρ z ^ 2)
  let E (i j : Fin d) (z : TimeVelocity d) :=
    spatialPartial i (fun y => A z.1 y i j) z.2 *
      scalarSpatialGradient u z j * u z * ρ z ^ 2
  let W (z : TimeVelocity d) := scalarTimeDerivative u z * u z * ρ z ^ 2
  have hL (i j : Fin d) : IntegrableOn (L i j) U :=
    (integrable_scalar_local_spatial_value_energy_terms hU u ρ hu hρ hc hsub A hA i j).1.restrict
  have hR (i j : Fin d) : IntegrableOn (R i j) U :=
    (integrable_scalar_local_spatial_value_energy_terms hU u ρ hu hρ hc hsub A hA i j).2.restrict
  have hE (i j : Fin d) : IntegrableOn (E i j) U := by
    have hcoeff : ContDiff ℝ (⊤ : ℕ∞) (fun z : TimeVelocity d => A z.1 z.2 i j) :=
      (contDiff_apply ℝ ℝ j).comp ((contDiff_apply ℝ (Fin d → ℝ) i).comp hA)
    have hcoeff12 := isScalarC12On_of_contDiff_two (hcoeff.of_le (by simp)) univ
    have hdA : Continuous (fun z : TimeVelocity d =>
        spatialPartial i (fun y => A z.1 y i j) z.2) :=
      (continuous_apply i).comp
        (continuousOn_univ.mp hcoeff12.continuousOn_scalarSpatialGradient)
    exact (integrable_local_cutoff_square_mul hU
      (fun z => spatialPartial i (fun y => A z.1 y i j) z.2 *
        scalarSpatialGradient u z j * u z) ρ
      ((hdA.continuousOn.mul ((continuous_apply j).comp_continuousOn
        hu.continuousOn_scalarSpatialGradient)).mul hu.continuousOn)
      hρ.continuous hc hsub).restrict
  have hW : IntegrableOn W U :=
    (integrable_local_cutoff_square_mul hU
      (fun z => scalarTimeDerivative u z * u z) ρ
      (hu.continuousOn_scalarTimeDerivative.mul hu.continuousOn) hρ.continuous hc hsub).restrict
  have hLs : IntegrableOn (fun z => ∑ i, ∑ j, L i j z) U :=
    integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hL i j))
  have hRs : IntegrableOn (fun z => ∑ i, ∑ j, R i j z) U :=
    integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hR i j))
  have hEs : IntegrableOn (fun z => ∑ i, ∑ j, E i j z) U :=
    integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hE i j))
  have hflux : (∫ z in U, ∑ i, ∑ j, L i j z) = -(∫ z in U, ∑ i, ∑ j, R i j z) := by
    rw [integral_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hL i j))]
    simp_rw [integral_finsetSum Finset.univ (fun j _ => hL _ j)]
    rw [integral_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hR i j))]
    simp_rw [integral_finsetSum Finset.univ (fun j _ => hR _ j),
      ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact integral_scalar_local_spatial_value_energy_spacetime
      a T O hO u ρ hu hρ hc hsub A hA i j
  have hRval : (∫ z in U, ∑ i, ∑ j, R i j z) =
      (∫ z in U, ∑ i, ∑ j, E i j z) - ∫ z in U, W z := by
    rw [← integral_sub hEs hW]
    apply setIntegral_congr_fun hU.measurableSet
    intro z hz
    dsimp only
    have hpde := heq z hz
    change scalarTimeDerivative u z +
      (∑ i, ∑ j, A z.1 z.2 i j * scalarSpatialHessian u z i j) = 0 at hpde
    simp only [R, E, W, add_mul, Finset.sum_add_distrib,
      ← Finset.sum_mul]
    rw [show (∑ i, ∑ j, A z.1 z.2 i j * scalarSpatialHessian u z i j) =
      -scalarTimeDerivative u z by linarith only [hpde]]
    ring
  change (∫ z in U, ∑ i, ∑ j, (L i j z + E i j z)) = ∫ z in U, W z
  simp_rw [Finset.sum_add_distrib]
  rw [integral_add hLs hEs]
  linarith only [hflux, hRval]

end HypoellipticAleksandrov.Parabolic.LocalHolder

module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalValueEnergy
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalTimeBound
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalCoercivity
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalEnergyRow
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # A local gradient bound from solution values

The bound combines actual quadratic testing, ellipticity, and the complete coefficient
error row. Its constants do not involve derivatives of the solution or its boundary data.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter MeasureTheory Set
open scoped BigOperators MatrixOrder Matrix.Norms.Elementwise

/-- Localized gradient energy is bounded by value energy for a homogeneous classical solution. -/
theorem integral_local_gradient_energy_le {d : ℕ}
    (a T : ℝ) (O : Set (PDE.Vec d)) (hO : IsOpen O)
    (u ρ : TimeVelocity d → ℝ) (hu : IsScalarC12On u (Ioo a T ×ˢ O))
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hc : HasCompactSupport ρ)
    (hsub : tsupport ρ ⊆ Ioo a T ×ˢ O)
    (A : CoefficientField d) (hA : IsSmoothCoefficient A)
    (lam K Kt : ℝ) (hlam : 0 < lam) (hK : 0 ≤ K)
    (hell : ∀ z ∈ Ioo a T ×ˢ O, lam • (1 : PDE.Mat d) ≤ coefficientAt A z)
    (hrow : ∀ z ∈ Ioo a T ×ˢ O, ∀ j, |localValueEnergyErrorRow A ρ z j| ≤ K)
    (ht : ∀ z ∈ Ioo a T ×ˢ O, |timeDerivative (fun y => ρ y ^ 2) z| ≤ Kt)
    (hq : IntegrableOn (fun z => u z ^ 2) (Ioo a T ×ˢ O))
    (heq : ∀ z ∈ Ioo a T ×ˢ O, scalarTimeDerivative u z +
      matrixContraction (coefficientAt A z) (scalarSpatialHessian u z) = 0) :
    (lam / 2) * (∫ z in Ioo a T ×ˢ O,
      ρ z ^ 2 * ∑ j, scalarSpatialGradient u z j ^ 2) ≤
      (Kt / 2 + (d : ℝ) * K ^ 2 / (2 * lam)) *
        ∫ z in Ioo a T ×ˢ O, u z ^ 2 := by
  classical
  let U := Ioo a T ×ˢ O
  have hU : IsOpen U := isOpen_Ioo.prod hO
  let G (z : TimeVelocity d) := scalarSpatialGradient u z
  let P (z : TimeVelocity d) := ∑ i, ∑ j, A z.1 z.2 i j * G z j * G z i
  let B (z : TimeVelocity d) := localValueEnergyErrorRow A ρ z
  let E (z : TimeVelocity d) := ρ z ^ 2 * P z +
    u z * ρ z * ∑ j, B z j * G z j
  have hG (j : Fin d) : ContinuousOn (fun z => G z j) U :=
    (continuous_apply j).comp_continuousOn hu.continuousOn_scalarSpatialGradient
  have hP : ContinuousOn P U := by
    apply continuousOn_finsetSum
    intro i _
    apply continuousOn_finsetSum
    intro j _
    have hcoeff : Continuous (fun z : TimeVelocity d => A z.1 z.2 i j) :=
      (continuous_apply j).comp ((continuous_apply i).comp hA.continuous)
    exact (hcoeff.continuousOn.mul (hG j)).mul (hG i)
  have hB : Continuous B := continuous_localValueEnergyErrorRow A hA ρ hρ
  have hBG : ContinuousOn (fun z => ∑ j, B z j * G z j) U := by
    apply continuousOn_finsetSum
    intro j _
    exact ((continuous_apply j).comp hB).continuousOn.mul (hG j)
  have hEi : IntegrableOn E U := by
    have hcont : ContinuousOn (fun z => ρ z * P z + u z * ∑ j, B z j * G z j) U :=
      (hρ.continuous.continuousOn.mul hP).add (hu.continuousOn.mul hBG)
    have hi := (integrable_local_cutoff_mul hU
      (fun z => ρ z * P z + u z * ∑ j, B z j * G z j) ρ
      hcont hρ.continuous hc hsub).restrict (s := U)
    apply hi.congr
    exact Eventually.of_forall (fun z => by dsimp [E]; ring)
  have hgrad : IntegrableOn (fun z => ρ z ^ 2 * ∑ j, G z j ^ 2) U := by
    have hcont : ContinuousOn (fun z => ∑ j, G z j ^ 2) U := by
      apply continuousOn_finsetSum
      intro j _
      exact (hG j).pow 2
    have hi := (integrable_local_cutoff_square_mul hU
      (fun z => ∑ j, G z j ^ 2) ρ hcont hρ.continuous hc hsub).restrict (s := U)
    apply hi.congr
    exact Eventually.of_forall (fun z => mul_comm _ _)
  let c := (d : ℝ) * K ^ 2 / (2 * lam)
  have hcpoint : ∀ᵐ z ∂volume.restrict U,
      (lam / 2) * (ρ z ^ 2 * ∑ j, G z j ^ 2) ≤ E z + c * u z ^ 2 := by
    apply ae_restrict_of_forall_mem hU.measurableSet
    intro z hz
    have hp := local_value_energy_flux_coercivity lam (ρ z) (u z) K hlam hK
      (coefficientAt A z) (G z) (B z) (hell z hz) (hrow z hz)
    convert hp using 1 <;> (try dsimp [E, P, c, coefficientAt]) <;> ring
  have hb := integral_mono_ae (hgrad.const_mul (lam / 2))
    (hEi.add (hq.const_mul c)) hcpoint
  simp only [Pi.add_apply] at hb
  rw [integral_add hEi (hq.const_mul c), integral_const_mul,
    integral_const_mul] at hb
  have hEeq : (∫ z in U, E z) =
      ∫ z in U, scalarTimeDerivative u z * u z * ρ z ^ 2 := by
    rw [← integral_scalar_local_value_energy_eq a T O hO u ρ hu hρ hc hsub A hA heq]
    apply setIntegral_congr_fun hU.measurableSet
    intro z _
    exact (local_value_energy_flux_eq (ρ z) (u z) (coefficientAt A z)
      (fun i j => spatialPartial i (fun y => A z.1 y i j) z.2)
      (G z) (scalarSpatialGradient ρ z)).symm
  rw [hEeq] at hb
  have htime := integral_local_time_energy_le hU u ρ hu hρ hc hsub Kt hq ht
  dsimp only [G, c] at hb
  linarith only [hb, htime]

/-- The smooth compact cutoff has a finite bound on the time derivative of its square. -/
theorem exists_local_cutoff_square_timeDerivative_bound {d : ℕ}
    (ρ : TimeVelocity d → ℝ) (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hc : HasCompactSupport ρ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z, |timeDerivative (fun y => ρ y ^ 2) z| ≤ K := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun z => ρ z ^ 2) := hρ.pow 2
  have hsc : HasCompactSupport (fun z => ρ z ^ 2) := by
    rw [show (fun z => ρ z ^ 2) = ρ * ρ by funext z; exact pow_two _]
    exact HasCompactSupport.mul_left hc
  have hdc : Continuous (timeDerivative (fun z => ρ z ^ 2)) :=
    (hs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hds : HasCompactSupport (timeDerivative (fun z => ρ z ^ 2)) :=
    hsc.fderiv_apply (𝕜 := ℝ) (1, 0)
  obtain ⟨K, hK⟩ := hdc.bounded_above_of_compact_support hds
  exact ⟨max K 0, le_max_right _ _, fun z =>
    (Real.norm_eq_abs _).symm.le.trans ((hK z).trans (le_max_left _ _))⟩

/-- One cutoff-dependent constant bounds every homogeneous solution's gradient energy. -/
theorem exists_local_gradient_energy_constant {d : ℕ}
    (a T : ℝ) (O : Set (PDE.Vec d)) (hO : IsOpen O)
    (ρ : TimeVelocity d → ℝ) (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hc : HasCompactSupport ρ) (hsub : tsupport ρ ⊆ Ioo a T ×ˢ O)
    (A : CoefficientField d) (hA : IsSmoothCoefficient A)
    (lam : ℝ) (hlam : 0 < lam)
    (hell : ∀ z ∈ Ioo a T ×ˢ O, lam • (1 : PDE.Mat d) ≤ coefficientAt A z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : TimeVelocity d → ℝ,
      IsScalarC12On u (Ioo a T ×ˢ O) →
      IntegrableOn (fun z => u z ^ 2) (Ioo a T ×ˢ O) →
      (∀ z ∈ Ioo a T ×ˢ O, scalarTimeDerivative u z +
        matrixContraction (coefficientAt A z) (scalarSpatialHessian u z) = 0) →
      (lam / 2) * (∫ z in Ioo a T ×ˢ O,
        ρ z ^ 2 * ∑ j, scalarSpatialGradient u z j ^ 2) ≤
        C * ∫ z in Ioo a T ×ˢ O, u z ^ 2 := by
  obtain ⟨K, hK, hrow⟩ := exists_localValueEnergyErrorRow_bound A hA ρ hρ hc
  obtain ⟨Kt, hKt, ht⟩ := exists_local_cutoff_square_timeDerivative_bound ρ hρ hc
  refine ⟨Kt / 2 + (d : ℝ) * K ^ 2 / (2 * lam), by positivity, ?_⟩
  intro u hu hq heq
  exact integral_local_gradient_energy_le a T O hO u ρ hu hρ hc hsub A hA
    lam K Kt hlam hK hell (fun z _ j => hrow z j) (fun z _ => ht z) hq heq

end HypoellipticAleksandrov.Parabolic.LocalHolder

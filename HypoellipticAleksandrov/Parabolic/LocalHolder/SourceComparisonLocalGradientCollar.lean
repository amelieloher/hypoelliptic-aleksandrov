module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalGradientBound
public import HypoellipticAleksandrov.Parabolic.WeakJetCutoff
import Mathlib.Tactic.Linarith

/-! # Uniform gradient energy on smaller collars

A compact interior plateau removes the cutoff weight on the smaller carrier. The resulting
constant is fixed before choosing the classical solution.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter MeasureTheory Set
open scoped BigOperators MatrixOrder Topology

/-- Every compactly contained carrier has a uniform gradient bound from outer value energy. -/
theorem exists_local_gradient_collar_constant {d : ℕ}
    (a T : ℝ) (O : Set (PDE.Vec d)) (hO : IsOpen O)
    (hUc : IsCompact (closure (Ioo a T ×ˢ O)))
    (V : Set (TimeVelocity d)) (hVm : MeasurableSet V)
    (hVc : IsCompact (closure V)) (hVU : closure V ⊆ Ioo a T ×ˢ O)
    (A : CoefficientField d) (hA : IsSmoothCoefficient A)
    (lam : ℝ) (hlam : 0 < lam)
    (hell : ∀ z ∈ Ioo a T ×ˢ O, lam • (1 : PDE.Mat d) ≤ coefficientAt A z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : TimeVelocity d → ℝ,
      IsScalarC12On u (Ioo a T ×ˢ O) →
      IntegrableOn (fun z => u z ^ 2) (Ioo a T ×ˢ O) →
      (∀ z ∈ Ioo a T ×ˢ O, scalarTimeDerivative u z +
        matrixContraction (coefficientAt A z) (scalarSpatialHessian u z) = 0) →
      (∫ z in V, ∑ j, scalarSpatialGradient u z j ^ 2) ≤
        C * ∫ z in Ioo a T ×ˢ O, u z ^ 2 := by
  classical
  let U := Ioo a T ×ˢ O
  have hU : IsOpen U := isOpen_Ioo.prod hO
  obtain ⟨ρ, hρ, hρone, hρsub⟩ := exists_smooth_cutoff_tsupport_subset hVc hU hVU
  have hc : HasCompactSupport ρ :=
    hasCompactSupport_of_tsupport_subset_of_isCompact_closure hρsub hUc
  obtain ⟨C, hC, hbound⟩ := exists_local_gradient_energy_constant
    a T O hO ρ hρ hc hρsub A hA lam hlam hell
  refine ⟨2 * C / lam, by positivity, ?_⟩
  intro u hu hq heq
  let f (z : TimeVelocity d) := ∑ j, scalarSpatialGradient u z j ^ 2
  have hcont : ContinuousOn f U := by
    apply continuousOn_finsetSum
    intro j _
    exact ((continuous_apply j).comp_continuousOn
      hu.continuousOn_scalarSpatialGradient).pow 2
  have hfi : IntegrableOn (fun z => ρ z ^ 2 * f z) U := by
    apply ((integrable_local_cutoff_square_mul hU f ρ hcont
      hρ.continuous hc hρsub).restrict (s := U)).congr
    exact Eventually.of_forall (fun z => mul_comm _ _)
  have hmono := setIntegral_mono_set hfi
    (Eventually.of_forall (fun z => mul_nonneg (sq_nonneg (ρ z))
      (Finset.sum_nonneg (fun j _ => sq_nonneg _))))
    (Eventually.of_forall (fun z hz => hVU (subset_closure hz)))
  have hsame : (∫ z in V, ρ z ^ 2 * f z) = ∫ z in V, f z := by
    apply setIntegral_congr_fun hVm
    intro z hz
    obtain ⟨W, hW, hVW, hρW⟩ := eventually_nhdsSet_iff_exists.mp hρone
    change ρ z ^ 2 * f z = f z
    rw [hρW z (hVW (subset_closure hz)), one_pow, one_mul]
  rw [hsame] at hmono
  have hb := hbound u hu hq heq
  have hmul := mul_le_mul_of_nonneg_left hmono (show 0 ≤ lam / 2 by positivity)
  dsimp only [f] at hmul
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hlam).mpr
  nlinarith only [hmul, hb]

end HypoellipticAleksandrov.Parabolic.LocalHolder

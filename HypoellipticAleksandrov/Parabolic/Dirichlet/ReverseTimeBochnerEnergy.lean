module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialSobolevNorm
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeBochnerContinuous

/-!
# Reverse-time Bochner energy bound

This module turns a continuous spatial Sobolev curve with separate value and
gradient energy bounds into its quotient-valued reverse-time Bochner class.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- A continuous spatial Sobolev curve satisfying the stated value and
gradient bounds has a reverse-time Bochner `L²(V)` representative with the
corresponding constant-one graph-norm energy bound. -/
theorem exists_reverseTimeL2V_of_continuousOn_energy
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) {T lam B G : ℝ}
    (hT : 0 < T) (hlam : 0 < lam)
    (w : ℝ → H10HilbertGraph hΩ)
    (hw : ContinuousOn w (Set.Icc 0 T))
    (hvalue : ∀ t ∈ Set.Icc 0 T,
      ‖valueCLM hΩ (w t)‖ ^ 2 ≤ B)
    (hgradient : lam * ∫ t in Set.Ioc 0 T,
      ‖gradientCLM hΩ (w t)‖ ^ 2 ≤ G) :
    ∃ W : ReverseTimeL2V hΩ T,
      W =ᵐ[reverseTimeVolume T] w ∧
      ‖W‖ ^ 2 ≤ T * B + G / lam := by
  let W : ReverseTimeL2V hΩ T := reverseTimeL2OfContinuousOn T w hw
  let hwLp := memLp_two_reverseTime_of_continuousOn T w hw
  letI : IsFiniteMeasure (reverseTimeVolume T) := by
    change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) T))
    infer_instance
  have hBnonneg : 0 ≤ B := by
    exact (sq_nonneg (‖valueCLM hΩ (w 0)‖)).trans
      (hvalue 0 ⟨le_rfl, le_of_lt hT⟩)
  have hgradientIntegralNonneg :
      0 ≤ ∫ t in Set.Ioc 0 T, ‖gradientCLM hΩ (w t)‖ ^ 2 := by
    exact integral_nonneg fun _ => sq_nonneg _
  have hGnonneg : 0 ≤ G := by
    exact (mul_nonneg (le_of_lt hlam) hgradientIntegralNonneg).trans hgradient
  have hvalueContinuous :
      ContinuousOn (fun t => valueCLM hΩ (w t)) (Set.Icc 0 T) :=
    (valueCLM hΩ).continuous.comp_continuousOn hw
  have hgradientContinuous :
      ContinuousOn (fun t => gradientCLM hΩ (w t)) (Set.Icc 0 T) :=
    (gradientCLM hΩ).continuous.comp_continuousOn hw
  have hvalueLp :
      MemLp (fun t => valueCLM hΩ (w t)) (2 : ℝ≥0∞) (reverseTimeVolume T) :=
    memLp_two_reverseTime_of_continuousOn T _ hvalueContinuous
  have hgradientLp :
      MemLp (fun t => gradientCLM hΩ (w t)) (2 : ℝ≥0∞) (reverseTimeVolume T) :=
    memLp_two_reverseTime_of_continuousOn T _ hgradientContinuous
  have hvalueIntegrable :
      Integrable (fun t => ‖valueCLM hΩ (w t)‖ ^ 2) (reverseTimeVolume T) := by
    exact hvalueLp.integrable_norm_pow (by norm_num)
  have hgradientIntegrable :
      Integrable (fun t => ‖gradientCLM hΩ (w t)‖ ^ 2) (reverseTimeVolume T) := by
    exact hgradientLp.integrable_norm_pow (by norm_num)
  have hvalueBound :
      (∫ t, ‖valueCLM hΩ (w t)‖ ^ 2 ∂reverseTimeVolume T) ≤ T * B := by
    calc
      (∫ t, ‖valueCLM hΩ (w t)‖ ^ 2 ∂reverseTimeVolume T) ≤
          ∫ _ : ℝ, B ∂reverseTimeVolume T := by
        apply integral_mono_ae hvalueIntegrable (integrable_const B)
        change ∀ᵐ t ∂volume.restrict (Ioo 0 T),
          ‖valueCLM hΩ (w t)‖ ^ 2 ≤ B
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        exact hvalue t ⟨le_of_lt ht.1, le_of_lt ht.2⟩
      _ = T * B := by
        rw [integral_const, smul_eq_mul, reverseTimeVolume_real_univ T hT]
  have hgradientIoc :
      (∫ t, ‖gradientCLM hΩ (w t)‖ ^ 2 ∂reverseTimeVolume T) =
        ∫ t in Set.Ioc 0 T, ‖gradientCLM hΩ (w t)‖ ^ 2 := by
    change (∫ t in Set.Ioo 0 T, ‖gradientCLM hΩ (w t)‖ ^ 2) =
      ∫ t in Set.Ioc 0 T, ‖gradientCLM hΩ (w t)‖ ^ 2
    exact MeasureTheory.setIntegral_congr_set Ioo_ae_eq_Ioc
  have hgradientBound :
      (∫ t, ‖gradientCLM hΩ (w t)‖ ^ 2 ∂reverseTimeVolume T) ≤ G / lam := by
    rw [hgradientIoc]
    apply (le_div_iff₀ hlam).mpr
    simpa only [mul_comm] using hgradient
  have hnorm :
      (∫ t, ‖w t‖ ^ 2 ∂reverseTimeVolume T) = ‖W‖ ^ 2 := by
    simpa only [W, reverseTimeL2OfContinuousOn] using
      integral_norm_sq_eq_norm_sq_toLp w hwLp
  refine ⟨W, coeFn_reverseTimeL2OfContinuousOn T w hw, ?_⟩
  calc
    ‖W‖ ^ 2 = ∫ t, ‖w t‖ ^ 2 ∂reverseTimeVolume T := hnorm.symm
    _ = ∫ t, (‖valueCLM hΩ (w t)‖ ^ 2 + ‖gradientCLM hΩ (w t)‖ ^ 2)
        ∂reverseTimeVolume T := by
      apply integral_congr_ae
      filter_upwards with t
      exact norm_sq_h10HilbertGraph hΩ (w t)
    _ = (∫ t, ‖valueCLM hΩ (w t)‖ ^ 2 ∂reverseTimeVolume T) +
        ∫ t, ‖gradientCLM hΩ (w t)‖ ^ 2 ∂reverseTimeVolume T :=
      integral_add hvalueIntegrable hgradientIntegrable
    _ ≤ T * B + G / lam := add_le_add hvalueBound hgradientBound

end HypoellipticAleksandrov.Parabolic.Dirichlet

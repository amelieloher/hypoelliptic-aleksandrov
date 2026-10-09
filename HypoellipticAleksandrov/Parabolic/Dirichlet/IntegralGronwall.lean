module

public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Order.ProjIcc

/-!
# Integral Grönwall zero closure

This module turns the scalar integral inequality arising from the Dirichlet
energy estimate into its zero conclusion.  It uses a continuous extension and
the differential Grönwall theorem, so every interval integral is justified by
continuity on a compact interval.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open Set

/-- A nonnegative continuous scalar function dominated by a multiple of its
past integral vanishes on the closed time interval. -/
theorem eq_zero_on_Icc_of_nonneg_le_mul_integral
    {T K : ℝ} (hT : 0 < T) (hK : 0 ≤ K)
    (E : ℝ → ℝ)
    (hEcont : ContinuousOn E (Set.Icc 0 T))
    (hEnonneg : ∀ t ∈ Set.Icc 0 T, 0 ≤ E t)
    (hEzero : E 0 = 0)
    (hEle : ∀ t ∈ Set.Icc 0 T,
      E t ≤ K * (∫ r in Set.Ioc 0 t, E r)) :
    ∀ t ∈ Set.Icc 0 T, E t = 0 := by
  let F : ℝ → ℝ := Set.IccExtend hT.le ((Set.Icc 0 T).restrict E)
  have hFcont : Continuous F := by
    exact hEcont.restrict.Icc_extend'
  have hF_eq_E {t : ℝ} (ht : t ∈ Set.Icc 0 T) : F t = E t := by
    dsimp [F]
    rw [Set.IccExtend_of_mem hT.le _ ht]
    rfl
  have hEint : MeasureTheory.IntegrableOn E (Set.Icc 0 T) :=
    hEcont.integrableOn_Icc
  have hEintIoc {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
      MeasureTheory.IntegrableOn E (Set.Ioc 0 t) :=
    hEint.mono_set (Set.Ioc_subset_Icc_self.trans fun r hr =>
      ⟨hr.1, hr.2.trans ht.2⟩)
  let P : ℝ → ℝ := fun t => ∫ r in 0..t, F r
  have hPderiv (t : ℝ) : HasDerivAt P (F t) t := by
    simpa only [P] using (hFcont.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hPcont : Continuous P :=
    continuous_iff_continuousAt.mpr fun t => (hPderiv t).continuousAt
  have hPzero : P 0 = 0 := by
    simp only [P, intervalIntegral.integral_same]
  have hP_eq {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
      P t = ∫ r in Set.Ioc 0 t, E r := by
    rw [show P t = ∫ r in 0..t, F r by rfl, intervalIntegral.integral_of_le ht.1]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro r hr
    exact hF_eq_E ⟨hr.1.le, hr.2.trans ht.2⟩
  have hPnonneg {t : ℝ} (ht : t ∈ Set.Icc 0 T) : 0 ≤ P t := by
    rw [show P t = ∫ r in 0..t, F r by rfl]
    refine intervalIntegral.integral_nonneg ht.1 fun r hr => ?_
    rw [hF_eq_E ⟨hr.1, hr.2.trans ht.2⟩]
    exact hEnonneg r ⟨hr.1, hr.2.trans ht.2⟩
  have hPbound : ∀ t ∈ Set.Ico 0 T, ‖F t‖ ≤ K * ‖P t‖ := by
    intro t ht
    have htcc : t ∈ Set.Icc 0 T := ⟨ht.1, ht.2.le⟩
    have hFnonneg : 0 ≤ F t := by
      rw [hF_eq_E htcc]
      exact hEnonneg t htcc
    calc
      ‖F t‖ = F t := Real.norm_of_nonneg hFnonneg
      _ = E t := hF_eq_E htcc
      _ ≤ K * (∫ r in Set.Ioc 0 t, E r) := hEle t htcc
      _ = K * P t := by rw [← hP_eq htcc]
      _ = K * ‖P t‖ := by rw [Real.norm_of_nonneg (hPnonneg htcc)]
  have hPvanish : ∀ t ∈ Set.Icc 0 T, P t = 0 :=
    eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right hPcont.continuousOn
      (fun t ht => (hPderiv t).hasDerivWithinAt) hPzero hPbound
  intro t ht
  by_cases htzero : t = 0
  · subst t
    exact hEzero
  have hEt : E t ≤ 0 := by
    calc
      E t ≤ K * (∫ r in Set.Ioc 0 t, E r) := hEle t ht
      _ = K * P t := by rw [← hP_eq ht]
      _ ≤ K * 0 := mul_le_mul_of_nonneg_left (by rw [hPvanish t ht]) hK
      _ = 0 := mul_zero K
  exact le_antisymm hEt (hEnonneg t ht)

end HypoellipticAleksandrov.Parabolic.Dirichlet

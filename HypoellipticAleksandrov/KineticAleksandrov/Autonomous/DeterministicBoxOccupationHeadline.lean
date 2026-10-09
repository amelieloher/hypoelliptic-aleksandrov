module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.DeterministicBoxOccupation

/-! # Source-facing real-time extended occupation headlines -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov MeasureTheory Set
open scoped ENNReal

/-- The singular source weight is a measurable extended function, including its infinite origin. -/
theorem rhoWeight_measurable (g Y : ℝ) :
    Measurable (fun q : Z => rhoWeight g (q.1 - Y, q.2)) :=
  (ENNReal.measurable_ofReal.comp (bellmanGauge_continuous.measurable.comp
    ((measurable_fst.sub_const Y).prodMk measurable_snd))).pow_const _

/-- The plan's iterated occupation conditions, with `c` absorbed into one uniform constant. -/
theorem deterministic_barrier_occupation
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (alpha M : ℝ)
    (ha : bellmanAdjointExponent (Lam / lam)
      (by apply (le_div_iff₀ hlam).2; simpa only [one_mul] using hLam) - 2 < alpha ∧
      alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (T Y : ℝ) (z : Z),
      0 < T → |z.2| ≤ M * Real.sqrt T →
      let E := fullSpaceEvolution hH hLE hlam hLam A
      (∫⁻ t in Ioc 0 T, ∫⁻ w, rhoWeight (gamma alpha) (w.1 - Y, w.2)
        ∂kernelXV E (Real.toNNReal t) z) ≤ ENNReal.ofReal (C * T ^ (alpha / 2)) := by
  obtain ⟨c, B, hc, hB, hb⟩ :=
    deterministic_barrier_occupation_uniform hH hLE lam Lam hlam hLam alpha ha.1 ha.2 M
  refine ⟨B / c, div_pos hB hc, ?_⟩
  intro A T Y z hT hz
  have ht : (Real.toNNReal T : ℝ) = T := Real.coe_toNNReal T hT.le
  have hh := mul_le_mul (le_refl ((ENNReal.ofReal c)⁻¹))
    (hb A z (Real.toNNReal T) Y (by simpa only [ht] using hT)
      (by simpa only [ht] using hz)) bot_le bot_le
  rw [← mul_assoc, ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hc).ne'
    ENNReal.ofReal_ne_top, one_mul, ht,
    physicalOccupationMeasure_lintegral _ _ _ _ (rhoWeight_measurable _ _)] at hh
  exact hh.trans_eq (by
    rw [show B / c * T ^ (alpha / 2) = (B * T ^ (alpha / 2)) / c by ring,
      ENNReal.ofReal_div_of_pos hc]
    simp only [div_eq_mul_inv]
    exact mul_comm _ _)

/-- Extended literal box occupation with real source parameters and no return-time premise. -/
theorem deterministic_box_occupation_extended
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (alpha A0 M : ℝ)
    (ha : bellmanAdjointExponent (Lam / lam)
      (by apply (le_div_iff₀ hlam).2; simpa only [one_mul] using hLam) - 2 < alpha ∧
      alpha < 1) (hA0 : 0 < A0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (r T Y : ℝ) (z : Z),
      0 < r → 0 < T → |z.2| ≤ M * Real.sqrt T →
      let E := fullSpaceEvolution hH hLE hlam hLam A
      (∫⁻ t in Ioc 0 T, kernelXV E (Real.toNNReal t) z (box A0 r Y)) ≤
        ENNReal.ofReal (C * r ^ (gamma alpha) * T ^ (alpha / 2)) := by
  obtain ⟨C, hC, hb⟩ :=
    deterministic_box_occupation hH hLE lam Lam hlam hLam alpha ha.1 ha.2 A0 M hA0
  refine ⟨C, hC, ?_⟩
  intro A r T Y z hr hT hz
  have ht : (Real.toNNReal T : ℝ) = T := Real.coe_toNNReal T hT.le
  have hh := hb A z Y r (Real.toNNReal T) hr (by simpa only [ht] using hz)
  simp only [ht] at hh
  dsimp only
  rw [← box_occupation_ofReal_integral]
  exact ENNReal.ofReal_le_ofReal hh

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

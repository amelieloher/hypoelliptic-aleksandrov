module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.DeterministicBoxOccupationGreenFatou
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.DeterministicBoxOccupationGeometry

/-! # Uniform deterministic box occupation, independent of return-time comparison -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov MeasureTheory Set
open scoped ENNReal

/-- The literal source box occupation estimate, with its constant before all dynamic data. -/
theorem deterministic_box_occupation
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) (alpha : ℝ)
    (ha : bellmanAdjointExponent (Lam / lam)
      (by apply (le_div_iff₀ hlam).2; simpa only [one_mul] using hLam) - 2 < alpha)
    (ha1 : alpha < 1) (A0 M : ℝ) (hA0 : 0 < A0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (z : Z) (Y r : ℝ) (T : NNReal),
      0 < r → |z.2| ≤ M * Real.sqrt (T : ℝ) →
      (∫ t in Ioc 0 (T : ℝ),
        (kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal t) z
          (box A0 r Y)).toReal) ≤ C * r ^ (gamma alpha) * (T : ℝ) ^ (alpha / 2) := by
  obtain ⟨hlo, _, _⟩ := exists_bellman_barrier lam Lam hlam hLam
  have ha0 : 0 < alpha := lt_of_le_of_lt (sub_nonneg.mpr hlo) ha
  have hg : 0 < gamma alpha := by dsimp only [gamma]; linarith
  obtain ⟨c, B, hc, hB, hb⟩ :=
    deterministic_barrier_occupation_uniform hH hLE lam Lam hlam hLam alpha ha ha1 M
  let D : ℝ := (A0 ^ 2 + A0 ^ 6) ^ (1 / 6 : ℝ)
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨D ^ (gamma alpha) * B / c, by positivity, ?_⟩
  intro A z Y r T hr hz
  let E := fullSpaceEvolution hH hLE hlam hLam A
  by_cases hT : (T : ℝ) = 0
  · simp only [hT, Ioc_self, Measure.restrict_empty, integral_zero_measure]
    positivity
  have hTp : 0 < (T : ℝ) := lt_of_le_of_ne T.property (Ne.symm hT)
  let L := ∫⁻ q, rhoWeight (gamma alpha) (q.1 - Y, q.2)
    ∂physicalOccupationMeasure E z T
  have hw : L ≤ ENNReal.ofReal (B * (T : ℝ) ^ (alpha / 2) / c) := by
    have hh := mul_le_mul (le_refl ((ENNReal.ofReal c)⁻¹)) (hb A z T Y hTp hz) bot_le bot_le
    rw [← mul_assoc, ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hc).ne'
      ENNReal.ofReal_ne_top, one_mul] at hh
    exact hh.trans_eq (by
      rw [ENNReal.ofReal_div_of_pos hc]
      simp only [div_eq_mul_inv]
      exact mul_comm _ _)
  have hbox := (box_measure_le_weight (physicalOccupationMeasure E z T) hA0 hr hg.le).trans
    (mul_le_mul le_rfl hw bot_le bot_le)
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (mul_nonneg hD.le hr.le) _)] at hbox
  have he : (D * r) ^ (gamma alpha) * (B * (T : ℝ) ^ (alpha / 2) / c) =
      (D ^ (gamma alpha) * B / c) * r ^ (gamma alpha) * (T : ℝ) ^ (alpha / 2) := by
    rw [Real.mul_rpow hD.le hr.le]
    ring
  rw [he, physicalOccupationMeasure_apply _ _ _ _ (box_measurable A0 r Y),
    ← box_occupation_ofReal_integral] at hbox
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hbox

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

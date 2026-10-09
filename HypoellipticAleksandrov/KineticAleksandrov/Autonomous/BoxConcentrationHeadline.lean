module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoxConcentration
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.DeterministicBoxOccupationHeadline

/-! # A common source constant for occupation and conditional concentration -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov MeasureTheory Set
open scoped ENNReal

/-- The two literal source bounds share one constant. Only concentration uses return-time.
The explicit premise is the full return-time conclusion for all nonnegative bounded Borel data. -/
theorem deterministic_box_occupation_concentration_of_return_time
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (alpha A0 M : ℝ)
    (ha : bellmanAdjointExponent (Lam / lam)
      (by apply (le_div_iff₀ hlam).2; simpa only [one_mul] using hLam) - 2 < alpha ∧
      alpha < 1) (hA0 : 0 < A0)
    (hReturn : ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam)
      (F : BoundedBorel (EvolutionAmbientState 1)), (∀ p, 0 ≤ F p) →
      ∀ (t s : NNReal) (z : Z), 0 < (t : ℝ) →
        2 * (t : ℝ) ≤ (s : ℝ) → (s : ℝ) ≤ 3 * (t : ℝ) →
        |z.2| ≤ Real.sqrt (t : ℝ) →
        let E := fullSpaceEvolution hH hLE hlam hLam A
        fullSpaceAction E F ⟨t, fun _ => z.1, fun _ => z.2⟩ ≤
          C * fullSpaceAction E F ⟨s, fun _ => z.1, fun _ => z.2⟩) :
    ∃ C : ℝ, 0 < C ∧
      (∀ (A : SmoothAutonomous lam Lam) (r T Y : ℝ) (z : Z),
        0 < r → 0 < T → |z.2| ≤ M * Real.sqrt T →
        let E := fullSpaceEvolution hH hLE hlam hLam A
        (∫⁻ t in Ioc 0 T, kernelXV E (Real.toNNReal t) z (box A0 r Y)) ≤
          ENNReal.ofReal (C * r ^ (gamma alpha) * T ^ (alpha / 2))) ∧
      (∀ (A : SmoothAutonomous lam Lam) (r Y t : ℝ) (z : Z),
        0 < r → 0 ≤ t → |z.2| ≤ 3 * r →
        let E := fullSpaceEvolution hH hLE hlam hLam A
        kernelXV E (Real.toNNReal t) z (box A0 r Y) ≤
          ENNReal.ofReal (C * (1 + t / r ^ 2) ^ (-gamma alpha / 2))) := by
  obtain ⟨B, hB, hb⟩ :=
    deterministic_box_occupation_extended hH hLE hlam hLam alpha A0 M ha hA0
  obtain ⟨D, hD, hd⟩ :=
    box_concentration_of_return_time hH hLE lam Lam hlam hLam alpha ha.1 ha.2 A0 hA0 hReturn
  refine ⟨B + D, add_pos hB hD, ?_, ?_⟩
  · intro A r T Y z hr hT hz
    apply (hb A r T Y z hr hT hz).trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD.le)
        (Real.rpow_nonneg hr.le _)) (Real.rpow_nonneg hT.le _)
  · intro A r Y t z hr ht hz
    dsimp only
    let E := fullSpaceEvolution hH hLE hlam hLam A
    have hh := hd A z Y r (Real.toNNReal t) hr hz
    simp only [Real.coe_toNNReal t ht] at hh
    have hmass := (measure_mono (subset_univ (box A0 r Y))).trans
      (kernelXV_mass_le_one E (Real.toNNReal t) z)
    rw [← ENNReal.ofReal_toReal (hmass.trans_lt ENNReal.one_lt_top).ne]
    apply (ENNReal.ofReal_le_ofReal hh).trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hB.le)
      (Real.rpow_nonneg (by positivity) _)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

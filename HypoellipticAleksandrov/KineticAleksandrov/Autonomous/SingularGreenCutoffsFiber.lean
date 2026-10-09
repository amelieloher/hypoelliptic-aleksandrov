module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsModulus

/-! # Position-fiber majorants of the actual homogeneous Bellman jets -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Set MeasureTheory

/-- The position coordinate gives its own cube-root gauge lower bound. -/
theorem barrier_position_gauge_lower (q : ℝ × ℝ) : |q.1| ^ (1 / 3 : ℝ) ≤ bellmanGauge q := by
  have hh := Real.rpow_le_rpow (abs_nonneg q.1) (bellmanGauge_coordinate_bounds q).1
    (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have he : (bellmanGauge q ^ 3) ^ (1 / 3 : ℝ) = bellmanGauge q := by
    rw [← Real.rpow_natCast_mul (bellmanGauge_nonneg q)]
    norm_num
  rwa [he] at hh

/-- A negative homogeneous gauge bound has a uniform position-fiber power majorant. -/
theorem barrier_position_fiber_bound (beta : ℝ) (hb : beta ≤ 0)
    (f : (ℝ × ℝ) → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ q ∈ bellmanPuncturedSet, |f q| ≤ C * bellmanGauge q ^ beta)
    (X v : ℝ) (hX : X ≠ 0) : |f (X, v)| ≤ C * |X| ^ (beta / 3) := by
  have hq : (X, v) ∈ bellmanPuncturedSet := fun he => hX (congrArg Prod.fst he)
  have hl := barrier_position_gauge_lower (X, v)
  have hh := Real.rpow_le_rpow_of_nonpos
    (Real.rpow_pos_of_pos (abs_pos.mpr hX) _) hl hb
  rw [← Real.rpow_mul (abs_nonneg X)] at hh
  have he : (1 / 3 : ℝ) * beta = beta / 3 := by ring
  rw [he] at hh
  exact (hbound _ hq).trans (mul_le_mul_of_nonneg_left hh hC)

/-- The three jet fibers are integrable on every compact position interval, uniformly in v. -/
theorem barrier_jet_fiber_integrable {alpha : ℝ} {phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha phi) (ha : 0 < alpha) (ha1 : alpha < 1)
    (v a b : ℝ) :
    IntegrableOn (fun X => bellmanDx phi (X, v)) (Icc a b) volume ∧
    IntegrableOn (fun X => bellmanDv phi (X, v)) (Icc a b) volume ∧
    IntegrableOn (fun X => bellmanDvv phi (X, v)) (Icc a b) volume := by
  have hi (beta : ℝ) (hb : -3 < beta) (hb0 : beta ≤ 0)
      (f : (ℝ × ℝ) → ℝ) (hc : ContinuousOn f bellmanPuncturedSet)
      (C : ℝ) (hC : 0 ≤ C)
      (hbound : ∀ q ∈ bellmanPuncturedSet, |f q| ≤ C * bellmanGauge q ^ beta) :
      IntegrableOn (fun X => f (X, v)) (Icc a b) volume := by
    have hm : Measurable (fun X => f (X, v)) :=
      (measurable_of_continuousOn_compl_singleton (0, 0) hc).comp
        (measurable_id.prodMk measurable_const)
    have hmaj := ((bellman_abs_rpow_locallyIntegrable (beta / 3) (by linarith)).smul C)
      |>.integrableOn_isCompact (isCompact_Icc (a := a) (b := b))
    apply hmaj.mono' hm.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with X hX
    simpa only [Real.norm_eq_abs, Pi.smul_apply, smul_eq_mul] using
      barrier_position_fiber_bound beta hb0 f C hC hbound X v hX
  obtain ⟨_, hX, hv, hvv⟩ := h.origin_jet_bounds
  obtain ⟨CX, hCX, hbX⟩ := hX
  obtain ⟨Cv, hCv, hbv⟩ := hv
  obtain ⟨Cvv, hCvv, hbvv⟩ := hvv
  refine ⟨?_, ?_, ?_⟩
  · exact hi (alpha - 3) (by linarith) (by linarith) _ h.dx_continuousOn CX hCX hbX
  · exact hi (alpha - 1) (by linarith) (by linarith) _
      (h.directional_contDiffOn (0, 1)).continuousOn Cv hCv hbv
  · exact hi (alpha - 2) (by linarith) (by linarith) _ h.dvv_continuousOn Cvv hCvv hbvv

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

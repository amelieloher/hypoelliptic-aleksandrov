module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsWeightOrigin

/-! # Pointwise extended-weight limits, including the origin -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov MeasureTheory Filter Set
open scoped Topology ENNReal Convolution

/-- Away from the physical origin the mollified weight tends to the literal source weight. -/
theorem regularizedBarrierWeight_punctured_tendsto (alpha : ℝ) (q : Z) (hq : q ≠ (0, 0)) :
    Tendsto (fun n => ENNReal.ofReal (regularizedBarrierWeight alpha n q))
      atTop (𝓝 (rhoWeight (gamma alpha) q)) := by
  have hr := bellmanGauge_pos q hq
  have hbase : ContinuousAt (fun X : ℝ => bellmanGauge (X, q.2)) q.1 :=
    (bellmanGauge_continuous.comp (continuous_id.prodMk continuous_const)).continuousAt
  have hc : ContinuousAt (fun X : ℝ => bellmanGauge (X, q.2) ^ (alpha - 2)) q.1 :=
    hbase.rpow_const (Or.inl hr.ne')
  have hm : Measurable (fun X : ℝ => bellmanGauge (X, q.2) ^ (alpha - 2)) :=
    (bellmanGauge_continuous.measurable.comp
      (measurable_id.prodMk measurable_const)).pow_const _
  have hh := ContDiffBump.convolution_tendsto_right (μ := volume)
    (φ := barrierMollifierBump)
    (g := fun _ : ℕ => fun X : ℝ => bellmanGauge (X, q.2) ^ (alpha - 2))
    (k := fun _ : ℕ => q.1) barrierMollifierRadius_tendsto
    (Eventually.of_forall (fun _ => hm.aestronglyMeasurable))
    (hc.tendsto.comp tendsto_snd) tendsto_const_nhds
  have ht : Tendsto (fun n => regularizedBarrierWeight alpha n q)
      atTop (𝓝 (bellmanGauge q ^ (alpha - 2))) := by
    simpa only [regularizedBarrierWeight, positionConvolution_displacement,
      barrierMollifier, convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul] using hh
  have he : rhoWeight (gamma alpha) q = ENNReal.ofReal (bellmanGauge q ^ (alpha - 2)) := by
    change (ENNReal.ofReal (bellmanGauge q)) ^ (-(2 - alpha)) = _
    have he : -(2 - alpha) = alpha - 2 := by ring
    rw [he, ENNReal.ofReal_rpow_of_pos hr]
  rw [he]
  exact (ENNReal.continuous_ofReal.tendsto _).comp ht

/-- The extended source weight is the pointwise mollifier limit at every point, including atoms. -/
theorem regularizedBarrierWeight_tendsto (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1)
    (q : Z) :
    Tendsto (fun n => ENNReal.ofReal (regularizedBarrierWeight alpha n q))
      atTop (𝓝 (rhoWeight (gamma alpha) q)) := by
  by_cases hq : q = (0, 0)
  · subst q
    rw [rhoWeight_origin (by dsimp only [gamma]; linarith : 0 < gamma alpha)]
    exact regularizedBarrierWeight_origin_tendsto alpha ha ha1
  · exact regularizedBarrierWeight_punctured_tendsto alpha q hq

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

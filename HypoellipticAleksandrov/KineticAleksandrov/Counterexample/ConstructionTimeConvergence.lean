module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionTimeJet
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionJetConvergence

/-! # Recovery of the literal extended time representative -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory Filter HypoellipticAleksandrov.Parabolic
open scoped Topology

/-- At fixed time the raw time derivative is continuous in the spatial parameter. -/
theorem construction_rawTimeJet_continuous {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R t : ℝ) :
    Continuous (fun q : XV d =>
      kineticTimeDerivative (timeCutoffProfile (profileFunction h) alpha r mu R)
        ⟨t, q.1, q.2⟩) := by
  simp_rw [timeCutoffProfile_timeDerivative, barrier_timeDerivative]
  have hs := ((continuous_selectedFlatProfile h r).sub
    (contDiff_nativeBarrier d mu R t).continuous)
  exact ((contDiff_timeCutoffTheta.continuous_deriv (by simp)).comp hs).neg.mul
    (continuous_const.mul (continuous_const.sub
      ((PDE.contDiff_vecNormSq.continuous.comp continuous_snd).div_const _)))

/-- The time representative of the actual extension is locally integrable. -/
theorem construction_extendedTimeJet_locallyIntegrable {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R t : ℝ) :
    LocallyIntegrable (constructionExtendedTimeJet h r mu R t) volume := by
  have hH := (selectedProfile_spec h).2.2.2.2.2.2.1
  exact (construction_rawTimeJet_continuous h r mu R t).locallyIntegrable.indicator
    (isOpen_lt hH continuous_const).measurableSet

/-- The actual time derivatives of the smoothed extensions recover the literal time jet. -/
theorem construction_actual_timeJet_tendsto_ae {d : ℕ} {alpha : ℝ}
    (ha : 0 < alpha) (h : CounterProfileStatement d alpha) (r mu R : ℝ)
    (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R)
    (hvel : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < R ^ 2) (t : ℝ) :
    ∀ᵐ q ∂volume, Tendsto
      (fun n => deriv (fun s => spatialMollify (standardMollifierSequence n)
        (fun y => zeroExtendedProfile (profileFunction h) alpha r mu R ⟨s, y.1, y.2⟩) q) t)
      atTop (𝓝 (constructionExtendedTimeJet h r mu R t q)) := by
  simpa only [construction_mollified_time_jet ha h r mu R hr hmu hR hvel] using
    construction_spatialMollify_tendsto_ae _
      (construction_extendedTimeJet_locallyIntegrable h r mu R t)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

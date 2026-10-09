module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningWeakJetApprox
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningValues

/-! # Almost-everywhere convergence of the classical flattened approximation jets -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Filter

/-- Flattening the smooth approximations keeps the literal profile formula. -/
noncomputable def mollifiedFlatProfile {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (n : ℕ) : XV d → ℝ :=
  flatProfile (mollifiedProfile h n) flatteningPsi flatteningOffset alpha r

/-- Every flattened approximation is globally smooth. -/
theorem contDiff_mollifiedFlatProfile {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (mollifiedFlatProfile h r n) := by
  unfold mollifiedFlatProfile flatProfile
  exact contDiff_const.sub (contDiff_const.mul
    (contDiff_flatteningPsi.comp ((contDiff_mollifiedProfile h n).div_const _)))

/-- The literal position chain-rule formula for each smooth profile approximation. -/
theorem dx_mollifiedFlatProfile_eq {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r)
    (n : ℕ) (q : XV d) (i : Fin d) :
    dx (mollifiedFlatProfile h r n) q i =
      -deriv flatteningPsi (mollifiedProfile h n q / Real.rpow r alpha) *
        spatialMollify (standardMollifierSequence n) (fun z => profilePositionJet h z i) q := by
  unfold dx mollifiedFlatProfile
  rw [fderiv_flatProfile _ _ _ hr q
    ((contDiff_mollifiedProfile h n).differentiable (by simp) q)]
  change -deriv flatteningPsi (mollifiedProfile h n q / Real.rpow r alpha) *
    dx (mollifiedProfile h n) q i = _
  rw [dx_mollifiedProfile]

/-- The literal velocity chain-rule formula for each smooth profile approximation. -/
theorem dv_mollifiedFlatProfile_eq {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r)
    (n : ℕ) (q : XV d) (i : Fin d) :
    dv (mollifiedFlatProfile h r n) q i =
      -deriv flatteningPsi (mollifiedProfile h n q / Real.rpow r alpha) *
        spatialMollify (standardMollifierSequence n) (fun z => profileVelocityJet h z i) q := by
  unfold dv mollifiedFlatProfile
  rw [fderiv_flatProfile _ _ _ hr q
    ((contDiff_mollifiedProfile h n).differentiable (by simp) q)]
  change -deriv flatteningPsi (mollifiedProfile h n q / Real.rpow r alpha) *
    dv (mollifiedProfile h n) q i = _
  rw [dv_mollifiedProfile]

/-- The literal Hessian chain-rule formula for each smooth profile approximation. -/
theorem dvv_mollifiedFlatProfile_eq {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r)
    (n : ℕ) (q : XV d) (i k : Fin d) :
    dvv (mollifiedFlatProfile h r n) q i k =
      -deriv flatteningPsi (mollifiedProfile h n q / Real.rpow r alpha) *
        spatialMollify (standardMollifierSequence n) (fun z => profileHessian h z i k) q -
      Real.rpow r (-alpha) *
        deriv (deriv flatteningPsi) (mollifiedProfile h n q / Real.rpow r alpha) *
        spatialMollify (standardMollifierSequence n) (fun z => profileVelocityJet h z i) q *
        spatialMollify (standardMollifierSequence n) (fun z => profileVelocityJet h z k) q := by
  rw [mollifiedFlatProfile, dvv_flatProfile_of_contDiffAt _ _ _ hr q
    ((contDiff_mollifiedProfile h n).contDiffAt.of_le (by simp)) i k,
    dvv_mollifiedProfile, dv_mollifiedProfile, dv_mollifiedProfile]

/-- The fixed slope composed with division is continuous. -/
theorem continuous_flatSlope (alpha r : ℝ) :
    Continuous (fun s : ℝ => deriv flatteningPsi (s / Real.rpow r alpha)) := by
  rw [funext deriv_flatteningPsi]
  exact contDiff_flatteningSlope.continuous.comp (continuous_id.div_const _)

/-- The fixed second derivative composed with division is continuous. -/
theorem continuous_flatSecond (alpha r : ℝ) :
    Continuous (fun s : ℝ => deriv (deriv flatteningPsi) (s / Real.rpow r alpha)) := by
  rw [funext deriv_flatteningPsi]
  exact (contDiff_flatteningSlope.continuous_deriv (by simp)).comp (continuous_id.div_const _)

/-- The flattened approximation values converge almost everywhere to the literal flattening. -/
theorem mollifiedFlatProfile_ae_tendsto {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) :
    ∀ᵐ q ∂volume, Tendsto (fun n => mollifiedFlatProfile h r n q) atTop
      (nhds (selectedFlatProfile h r q)) := by
  have hH := (selectedProfile_spec h).2.2.2.2.2.2.1
  have hc : Continuous (fun s : ℝ => 1 - flatteningOffset * Real.rpow r alpha -
      Real.rpow r alpha * flatteningPsi (s / Real.rpow r alpha)) :=
    continuous_const.sub (continuous_const.mul
      (contDiff_flatteningPsi.continuous.comp (continuous_id.div_const _)))
  filter_upwards [spatialMollify_ae_tendsto _ hH.locallyIntegrable] with q hq
  exact hc.continuousAt.tendsto.comp hq

/-- The position jets converge to the explicit selected flattened position jet. -/
theorem dx_mollifiedFlatProfile_ae_tendsto {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r) (i : Fin d) :
    ∀ᵐ q ∂volume, Tendsto (fun n => dx (mollifiedFlatProfile h r n) q i) atTop
      (nhds (flatProfilePositionJet h r q i)) := by
  have hH := (selectedProfile_spec h).2.2.2.2.2.2.1
  have hx := (selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i
  filter_upwards [spatialMollify_ae_tendsto _ hH.locallyIntegrable,
    spatialMollify_ae_tendsto _ hx] with q hq hg
  have hc := ((continuous_flatSlope alpha r).continuousAt.tendsto.comp hq).neg.mul hg
  convert hc using 1
  · funext n
    unfold dx mollifiedFlatProfile
    rw [fderiv_flatProfile _ _ _ hr q
      ((contDiff_mollifiedProfile h n).differentiable (by simp) q)]
    change -deriv flatteningPsi (mollifiedProfile h n q / Real.rpow r alpha) *
        dx (mollifiedProfile h n) q i = _
    rw [dx_mollifiedProfile]
    rfl
  · rfl

/-- The velocity jets converge to the explicit selected flattened velocity jet. -/
theorem dv_mollifiedFlatProfile_ae_tendsto {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r) (i : Fin d) :
    ∀ᵐ q ∂volume, Tendsto (fun n => dv (mollifiedFlatProfile h r n) q i) atTop
      (nhds (flatProfileVelocityJet h r q i)) := by
  have hH := (selectedProfile_spec h).2.2.2.2.2.2.1
  have hv := (selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i
  filter_upwards [spatialMollify_ae_tendsto _ hH.locallyIntegrable,
    spatialMollify_ae_tendsto _ hv] with q hq hg
  have hc := ((continuous_flatSlope alpha r).continuousAt.tendsto.comp hq).neg.mul hg
  convert hc using 1
  · funext n
    unfold dv mollifiedFlatProfile
    rw [fderiv_flatProfile _ _ _ hr q
      ((contDiff_mollifiedProfile h n).differentiable (by simp) q)]
    change -deriv flatteningPsi (mollifiedProfile h n q / Real.rpow r alpha) *
        dv (mollifiedProfile h n) q i = _
    rw [dv_mollifiedProfile]
    rfl
  · rfl

/-- The Hessian jets converge, including the nonlinear product of the two first jets. -/
theorem dvv_mollifiedFlatProfile_ae_tendsto {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r) (i k : Fin d) :
    ∀ᵐ q ∂volume, Tendsto (fun n => dvv (mollifiedFlatProfile h r n) q i k) atTop
      (nhds (flatProfileHessian h r q i k)) := by
  have hH := (selectedProfile_spec h).2.2.2.2.2.2.1
  have hv := (selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hh := (selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i k
  filter_upwards [spatialMollify_ae_tendsto _ hH.locallyIntegrable,
    spatialMollify_ae_tendsto _ (hv i), spatialMollify_ae_tendsto _ (hv k),
    spatialMollify_ae_tendsto _ hh] with q hq hi hk hhq
  have hp := (continuous_flatSlope alpha r).continuousAt.tendsto.comp hq
  have hp2 := (continuous_flatSecond alpha r).continuousAt.tendsto.comp hq
  have hconst : Tendsto (fun _ : ℕ => Real.rpow r (-alpha)) atTop
      (nhds (Real.rpow r (-alpha))) := tendsto_const_nhds
  have hc := (hp.neg.mul hhq).sub (((hconst.mul hp2).mul hi).mul hk)
  convert hc using 1
  · funext n
    rw [mollifiedFlatProfile, dvv_flatProfile_of_contDiffAt _ _ _ hr q
      ((contDiff_mollifiedProfile h n).contDiffAt.of_le (by simp)) i k,
      dvv_mollifiedProfile, dv_mollifiedProfile, dv_mollifiedProfile]
    rfl
  · rfl

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsBarrierGreenBounds

/-! # Actual quantitative cutoff removal for regularized singular barriers -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov MeasureTheory Filter Set
open scoped Topology ENNReal

/-- Compact Green bounds pass to the noncompact sublinear barrier by extended Fatou.
All cutoff generator errors have been proved quantitatively, and the signed endpoint is retained. -/
theorem barrier_green_cutoff_removal
    (hH : HormanderHypoellipticityStatement) {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (f : Z → ℝ) (hf : ContDiff ℝ 2 f) (alpha D Bv : ℝ)
    (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1) (hD : 0 ≤ D) (hBv : 0 ≤ Bv)
    (hm : ∀ z w : Z, |f z - f w| ≤
      D * (|z.1 - w.1| ^ (alpha / 3) + |z.2 - w.2| ^ alpha))
    (hbv : ∀ z : Z, |deriv (fun v => f (z.1, v)) z.2| ≤ Bv)
    (c : ℝ) (hc : 0 < c) (w : Z → ℝ) (hw : Measurable w) (hwn : ∀ q, 0 ≤ w q)
    (hbound : ∀ q, c * w q ≤ physicalSpatialOperator A.a f q)
    (Y : ℝ) (z : Z) (T : NNReal) (hT : 0 < (T : ℝ))
    (hfi : Integrable f (kernelXV E T z)) :
    ENNReal.ofReal c * (∫⁻ q, ENNReal.ofReal (w q) ∂physicalOccupationMeasure E z T) ≤
      ENNReal.ofReal ((∫ q, f q ∂kernelXV E T z) - f z) := by
  obtain ⟨C, hC, hb⟩ := barrier_cutoff_green_bounds hH hlam hLam A E hE f hf alpha D Bv
    ha ha1 hD hBv hm hbv c hc w hw hwn hbound Y z T hT
  let F := fun n : ℕ => fun q : Z =>
    ENNReal.ofReal (c * (barrierRectCutoff Y ((n : ℝ) + 1) q * w q))
  let b := fun n : ℕ => (∫ q, barrierRectCutoff Y ((n : ℝ) + 1) q * f q ∂kernelXV E T z) -
    barrierRectCutoff Y ((n : ℝ) + 1) z * f z + C * (T : ℝ) / ((n : ℝ) + 1)
  have hmF (n : ℕ) : Measurable (F n) :=
    (((barrierRectCutoff_continuous _ _).measurable.mul hw).const_mul c).ennreal_ofReal
  have hpF (q : Z) : Tendsto (fun n => F n q) atTop (𝓝 (ENNReal.ofReal (c * w q))) := by
    apply Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [barrierRectCutoff_eventually_one Y q] with n hn
    simp only [F, hn, one_mul]
  have hcut0 : Tendsto (fun n : ℕ => barrierRectCutoff Y ((n : ℝ) + 1) z * f z)
      atTop (𝓝 (f z)) := by
    apply Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [barrierRectCutoff_eventually_one Y z] with n hn
    simp only [hn, one_mul]
  have herr : Tendsto (fun n : ℕ => C * (T : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_one_div] using
      (tendsto_const_nhds (x := C * (T : ℝ))).mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hbt : Tendsto b atTop (𝓝 ((∫ q, f q ∂kernelXV E T z) - f z)) := by
    have hi := barrierRectCutoff_integral_tendsto (kernelXV E T z) f
      hf.continuous.measurable hfi Y
    simpa only [add_zero] using (hi.sub hcut0).add herr
  have hboundF (n : ℕ) : (∫⁻ q, F n q ∂physicalOccupationMeasure E z T) ≤ ENNReal.ofReal (b n) :=
    hb ((n : ℝ) + 1) (by
      have hn : (0 : ℝ) ≤ n := by positivity
      linarith only [hn])
  have hh := singular_fatou_of_real_bounds (physicalOccupationMeasure E z T) F
    (fun q => ENNReal.ofReal (c * w q)) hmF hpF b _ hbt hboundF
  simpa only [ENNReal.ofReal_mul hc.le,
    lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne] using hh

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

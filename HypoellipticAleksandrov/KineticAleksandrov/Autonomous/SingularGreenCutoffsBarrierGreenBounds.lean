module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsBarrierLimit

/-! # Quantitative compact Green bounds for the actual regularized-barrier cutoff -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov MeasureTheory Set Filter
open scoped ENNReal

/-- Derived compact Green bounds have a vanishing, explicit inverse-radius error.
The premises describe the actual test and its generator, and no Green identity is assumed. -/
theorem barrier_cutoff_green_bounds
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
    (Y : ℝ) (z : Z) (T : NNReal) (hT : 0 < (T : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
      (∫⁻ q, ENNReal.ofReal (c * (barrierRectCutoff Y R q * w q))
        ∂physicalOccupationMeasure E z T) ≤
      ENNReal.ofReal ((∫ q, barrierRectCutoff Y R q * f q ∂kernelXV E T z) -
        barrierRectCutoff Y R z * f z + C * (T : ℝ) / R) := by
  obtain ⟨D1, D2, hD1, hD2, hb1, hb2⟩ := barrierCutoff_derivative_bounds
  let C := (2 * D1 + Lam * D2) * (|f (Y, 0)| + 4 * D) + 2 * Lam * D1 * Bv
  have hL : 0 ≤ Lam := hlam.le.trans hLam
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, fun R hR => ?_⟩
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  let F := fun q : Z => barrierRectCutoff Y R q * f q
  let G := fun q : Z => c * (barrierRectCutoff Y R q * w q)
  let mu := physicalOccupationMeasure E z T
  have hFc := barrierRectCutoff_contDiff Y R f hf
  have hFs := barrierRectCutoff_hasCompactSupport Y R hR0 f
  have hFL := physicalSpatialOperator_continuous_compact A F hFc hFs
  have hFi := physicalSpatialOperator_occupation_integrable A F hFc hFs E z T
  have hcut : Continuous (barrierRectCutoff Y R) := by
    exact (barrierCutoff_contDiff.continuous.comp
      ((continuous_fst.sub continuous_const).div_const _)).mul
        (barrierCutoff_contDiff.continuous.comp (continuous_snd.div_const _))
  have hGm : Measurable G := (hcut.measurable.mul hw).const_mul c
  have hGn (q : Z) : 0 ≤ G q :=
    mul_nonneg hc.le (mul_nonneg (barrierRectCutoff_bounds _ _ _).1 (hwn q))
  have hGb (q : Z) : G q ≤ physicalSpatialOperator A.a F q + C / R := by
    have herr := barrierRectError_quantitative A.a f Lam alpha D Bv D1 D2 Y R
      hL ha ha1 hD hBv hD1 hD2 hm hbv hb1 hb2 hR q
      (hlam.le.trans (A.bounds _ _).1) (A.bounds _ _).2
    have hid := barrierRectError_eq_operator A.a f hf Y R hR0 q
    have hlift := mul_le_mul_of_nonneg_left (hbound q) (barrierRectCutoff_bounds Y R q).1
    have heG : G q = barrierRectCutoff Y R q * (c * w q) := by dsimp only [G]; ring
    rw [← heG] at hlift
    have he := (neg_le_abs (barrierRectError A.a f Y R q)).trans herr
    change G q ≤ physicalSpatialOperator A.a F q + C / R
    linarith only [hid, hlift, he]
  obtain ⟨K, hbK⟩ := hFL.1.bounded_above_of_compact_support hFL.2
  have hGi : Integrable G mu := by
    apply (integrable_const (K + C / R)).mono' hGm.aestronglyMeasurable
    filter_upwards with q
    rw [Real.norm_eq_abs, abs_of_nonneg (hGn q)]
    have hLb : physicalSpatialOperator A.a F q ≤ K :=
      (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hbK q)
    exact (hGb q).trans (add_le_add hLb le_rfl)
  have hi := integral_mono hGi (hFi.add (integrable_const (C / R))) hGb
  change (∫ q, G q ∂physicalOccupationMeasure E z T) ≤
    ∫ q, physicalSpatialOperator A.a F q + C / R ∂physicalOccupationMeasure E z T at hi
  rw [integral_add hFi (integrable_const (C / R)), integral_const,
    smul_eq_mul, measureReal_def, physicalOccupationMeasure_mass_eq hlam A E hE,
    ENNReal.toReal_ofReal hT.le] at hi
  rw [fullspace_physical_green_compact_c2 hH hlam hLam A E hE F hFc hFs z T hT] at hi
  rw [← ofReal_integral_eq_lintegral_ofReal hGi (Eventually.of_forall hGn)]
  apply ENNReal.ofReal_le_ofReal
  exact hi.trans_eq (by dsimp only [F]; ring)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

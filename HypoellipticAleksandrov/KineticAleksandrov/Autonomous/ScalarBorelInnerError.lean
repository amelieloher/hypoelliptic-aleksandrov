module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ScalarBorelConvolution
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelDominated

/-! # The autonomous scalar coefficient defect on a fixed compact inner cylinder -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory Filter HypoellipticAleksandrov.Parabolic
open scoped Topology ENNReal

/-- The literal scalar Hessian contraction defect; the classical solution stays fixed. -/
def scalarBorelError (C a : ℝ → ℝ → ℝ) (H : Point → ℝ) (P : Point) : ℝ :=
  |(C (P.position 0) (P.velocity 0) - a (P.position 0) (P.velocity 0)) * H P|

/-- The autonomous operator difference is exactly the negative scalar contraction. -/
theorem scalar_borel_operator_sub (C a : ℝ → ℝ → ℝ) (u : Point → ℝ) (P : Point) :
    autonomousScalarOperator C u P - autonomousScalarOperator a u P =
      -(C (P.position 0) (P.velocity 0) - a (P.position 0) (P.velocity 0)) *
        kineticVelocityHessian u P 0 0 := by
  unfold autonomousScalarOperator
  ring

/-- Scalar ellipticity bounds the contraction defect without differentiating coefficients. -/
theorem scalar_borel_error_bound {lam Lam : ℝ} (hlam : 0 < lam)
    {C a : ℝ → ℝ → ℝ} (hC : ∀ x v, lam ≤ C x v ∧ C x v ≤ Lam)
    (ha : ∀ x v, lam ≤ a x v ∧ a x v ≤ Lam) (H : Point → ℝ) (P : Point) :
    scalarBorelError C a H P ≤ 2 * Lam * |H P| := by
  change |(C (P.position 0) (P.velocity 0) - a (P.position 0) (P.velocity 0)) * H P| ≤ _
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  have hl := hC (P.position 0) (P.velocity 0)
  have hr := ha (P.position 0) (P.velocity 0)
  apply abs_le.mpr
  constructor <;> linarith

/-- For a fixed compact set and continuous Hessian, the scalar defect vanishes in Lp. -/
theorem scalar_borel_inner_error {lam Lam : ℝ} (hlam : 0 < lam)
    (a : ℝ → ℝ → ℝ) (ha : Measurable (Function.uncurry a))
    (hb : ∀ x v, lam ≤ a x v ∧ a x v ≤ Lam)
    (C : ℕ → ℝ → ℝ → ℝ)
    (hC : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (C j)) ∧
      ∀ x v, lam ≤ C j x v ∧ C j x v ≤ Lam)
    (hc : ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)),
      Tendsto (fun j => C j z.1 z.2) atTop (𝓝 (a z.1 z.2)))
    (K : Set Point) (hK : IsCompact K) (H : Point → ℝ) (hH : ContinuousOn H K)
    {p : ℝ} (hp : 0 < p) :
    (∀ j, ∀ P, scalarBorelError (C j) a H P ≤ 2 * Lam * |H P|) ∧
    (∀ j, MemLp (scalarBorelError (C j) a H) (ENNReal.ofReal p) (volume.restrict K)) ∧
    Tendsto (fun j => (eLpNorm (scalarBorelError (C j) a H)
      (ENNReal.ofReal p) (volume.restrict K)).toReal) atTop (𝓝 0) := by
  have : IsFiniteMeasureOnCompacts (volume : Measure Point) :=
    Measure.IsFiniteMeasureOnCompacts.map
      (volume : Measure (ℝ × (PDE.Vec 1 × PDE.Vec 1))) (KineticPoint.homeomorphProd 1).symm
  have : IsFiniteMeasure (volume.restrict K) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hK.measure_lt_top⟩
  have hproj : Measurable (fun P : Point => (P.position 0, P.velocity 0)) :=
    (((continuous_apply 0).comp continuous_position).prodMk
      ((continuous_apply 0).comp continuous_velocity)).measurable
  have hHm : AEStronglyMeasurable H (volume.restrict K) :=
    hH.aestronglyMeasurable hK.measurableSet
  have hm j : AEStronglyMeasurable (scalarBorelError (C j) a H) (volume.restrict K) := by
    exact continuous_abs.comp_aestronglyMeasurable
      ((((hC j).1.continuous.measurable.comp hproj).aestronglyMeasurable.restrict.sub
        (ha.comp hproj).aestronglyMeasurable.restrict).mul hHm)
  have hbounds j := scalar_borel_error_bound hlam (hC j).2 hb H
  obtain ⟨B, hB⟩ := hK.bddAbove_image hH.abs
  let M := max B 0
  have hM : 0 ≤ M := le_max_right _ _
  have hHM P (hP : P ∈ K) : |H P| ≤ M :=
    (hB (mem_image_of_mem _ hP)).trans (le_max_left _ _)
  have hLam0 : 0 ≤ Lam := hlam.le.trans (hb 0 0).1 |>.trans (hb 0 0).2
  have hbound j : ∀ᵐ P ∂(volume.restrict K), scalarBorelError (C j) a H P ≤
      2 * Lam * M := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with P hP
    exact (hbounds j P).trans (mul_le_mul_of_nonneg_left (hHM P hP) (by positivity))
  have heconv : ∀ᵐ P ∂(volume.restrict K),
      Tendsto (fun j => scalarBorelError (C j) a H P) atTop (𝓝 0) := by
    filter_upwards [ae_restrict_of_ae (scalar_borel_phase_ae_lift hc)] with P hP
    have ht := ((hP.sub_const (a (P.position 0) (P.velocity 0))).mul_const (H P)).abs
    simpa only [sub_self, zero_mul, abs_zero, scalarBorelError] using ht
  refine ⟨hbounds, ?_, borel_bounded_error_norm_tendsto (volume.restrict K) hp
    (by positivity) (fun j => scalarBorelError (C j) a H) hm
    (fun j => Filter.Eventually.of_forall fun P => abs_nonneg _) hbound heconv⟩
  intro j
  apply (memLp_const (2 * Lam * M)).of_le (hm j)
  filter_upwards [hbound j] with P hP
  simpa only [scalarBorelError, Real.norm_eq_abs, abs_abs,
    abs_of_nonneg (by positivity : 0 ≤ 2 * Lam * M)] using hP

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

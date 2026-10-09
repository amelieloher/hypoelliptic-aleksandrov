module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.OriginJetsBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.Prod

/-! # Local integrability from the anisotropic dimension four -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set MeasureTheory

/-- Each coordinate is bounded by its exact gauge weight. -/
theorem bellmanGauge_coordinate_bounds (q : ℝ × ℝ) :
    |q.1| ≤ bellmanGauge q ^ 3 ∧ |q.2| ≤ bellmanGauge q := by
  have hr := bellmanGauge_nonneg q
  have he := bellmanGauge_pow_six q
  unfold bellmanGaugePower at he
  constructor
  · apply (sq_le_sq₀ (abs_nonneg _) (pow_nonneg hr 3)).mp
    rw [sq_abs, ← pow_mul]
    norm_num only at *
    nlinarith [show 0 ≤ q.2 ^ 6 by positivity]
  · apply (pow_le_pow_iff_left₀ (abs_nonneg _) hr (by decide : 6 ≠ 0)).mp
    rw [pow_abs, abs_of_nonneg (by positivity : 0 ≤ q.2 ^ 6)]
    nlinarith [sq_nonneg q.1]

/-- Negative gauge powers are dominated by a product of one-dimensional powers. -/
theorem bellmanGauge_rpow_product_bound (beta : ℝ) (hb : beta ≤ 0)
    (q : ℝ × ℝ) (hX : q.1 ≠ 0) (hv : q.2 ≠ 0) :
    bellmanGauge q ^ beta ≤ |q.1| ^ (beta / 4) * |q.2| ^ (beta / 4) := by
  have hr := bellmanGauge_nonneg q
  have hcoord := bellmanGauge_coordinate_bounds q
  have hp : |q.1| * |q.2| ≤ bellmanGauge q ^ 4 := by
    calc
      |q.1| * |q.2| ≤ bellmanGauge q ^ 3 * bellmanGauge q :=
        mul_le_mul hcoord.1 hcoord.2 (abs_nonneg _) (pow_nonneg hr _)
      _ = bellmanGauge q ^ 4 := by ring
  have hh := Real.rpow_le_rpow_of_nonpos
    (mul_pos (abs_pos.mpr hX) (abs_pos.mpr hv)) hp (by linarith : beta / 4 ≤ 0)
  rw [Real.mul_rpow (abs_nonneg _) (abs_nonneg _)] at hh
  have he : (bellmanGauge q ^ 4) ^ (beta / 4) = bellmanGauge q ^ beta := by
    rw [← Real.rpow_natCast_mul hr]
    congr 1
    ring
  rwa [he] at hh

/-- Absolute real powers of exponent greater than minus one are locally integrable. -/
theorem bellman_abs_rpow_locallyIntegrable (p : ℝ) (hp : -1 < p) :
    LocallyIntegrable (fun x : ℝ => |x| ^ p) volume := by
  have hm : Measurable (fun x : ℝ => |x| ^ p) :=
    measurable_of_continuousOn_compl_singleton 0
      (continuous_abs.continuousOn.rpow_const (fun x hx => Or.inl
        (abs_pos.mpr (by simpa only [mem_compl_iff, mem_singleton_iff] using hx)).ne'))
  apply locallyIntegrable_of_norm_le_rpow (by simp) (C := 1) (α := -p)
  · simpa using (show -p < 1 by linarith)
  · filter_upwards [] with x
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
      neg_neg, one_mul]
    exact le_rfl
  · exact hm.aestronglyMeasurable

/-- The product power majorant is locally integrable on the actual product volume. -/
theorem bellman_product_rpow_locallyIntegrable (p : ℝ) (hp : -1 < p) :
    LocallyIntegrable (fun q : ℝ × ℝ => |q.1| ^ p * |q.2| ^ p) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  have h1 := (bellman_abs_rpow_locallyIntegrable p hp).integrableOn_isCompact
    (hK.image continuous_fst)
  have h2 := (bellman_abs_rpow_locallyIntegrable p hp).integrableOn_isCompact
    (hK.image continuous_snd)
  have hh := h1.mul_prod h2
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at hh
  change IntegrableOn _ ((Prod.fst '' K) ×ˢ (Prod.snd '' K)) volume at hh
  exact hh.mono_set (fun q hq => ⟨mem_image_of_mem _ hq, mem_image_of_mem _ hq⟩)

/-- Both coordinate axes are null for the genuine product Lebesgue measure. -/
theorem bellman_coordinates_ne_zero_ae :
    ∀ᵐ q : ℝ × ℝ ∂volume, q.1 ≠ 0 ∧ q.2 ≠ 0 := by
  rw [Measure.volume_eq_prod]
  apply (Measure.ae_prod_iff_ae_ae
    ((measurable_fst (measurableSet_singleton (0 : ℝ))).compl.inter
      (measurable_snd (measurableSet_singleton (0 : ℝ))).compl)).mpr
  filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
  filter_upwards [volume.ae_ne (0 : ℝ)] with v hv
  exact ⟨hx, hv⟩

/-- Gauge degree above minus four implies local integrability, including the origin. -/
theorem bellman_gauge_bound_locallyIntegrable (beta : ℝ) (hb : -4 < beta)
    (hb0 : beta ≤ 0) (f : (ℝ × ℝ) → ℝ)
    (hc : ContinuousOn f bellmanPuncturedSet)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ q ∈ bellmanPuncturedSet, |f q| ≤ C * bellmanGauge q ^ beta) :
    LocallyIntegrable f volume := by
  have hm : Measurable f := measurable_of_continuousOn_compl_singleton (0, 0) hc
  have hprod := (bellman_product_rpow_locallyIntegrable (beta / 4)
    (by linarith)).smul C
  apply hprod.mono hm.aestronglyMeasurable
  filter_upwards [bellman_coordinates_ne_zero_ae] with q hq
  have hn : q ∈ bellmanPuncturedSet := by
    intro he
    exact hq.1 (congrArg Prod.fst he)
  change ‖f q‖ ≤ ‖C * (|q.1| ^ (beta / 4) * |q.2| ^ (beta / 4))‖
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (show 0 ≤ C * (|q.1| ^ (beta / 4) * |q.2| ^ (beta / 4)) from
    mul_nonneg hC (mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
      (Real.rpow_nonneg (abs_nonneg _) _)))]
  exact (hbound q hn).trans (mul_le_mul_of_nonneg_left
    (bellmanGauge_rpow_product_bound beta hb0 q hq.1 hq.2) hC)

/-- All three actual derivatives are locally integrable in the degree range of B8c. -/
theorem IsBellmanHomogeneous.origin_jets_locallyIntegrable {alpha : ℝ}
    {phi : (ℝ × ℝ) → ℝ} (h : IsBellmanHomogeneous alpha phi)
    (ha : 0 < alpha) (ha1 : alpha < 1) :
    LocallyIntegrable (bellmanDx phi) volume ∧
    LocallyIntegrable (bellmanDv phi) volume ∧
    LocallyIntegrable (bellmanDvv phi) volume := by
  obtain ⟨_, hX, hv, hvv⟩ := h.origin_jet_bounds
  obtain ⟨CX, hCX, hbX⟩ := hX
  obtain ⟨Cv, hCv, hbv⟩ := hv
  obtain ⟨Cvv, hCvv, hbvv⟩ := hvv
  refine ⟨?_, ?_, ?_⟩
  · exact bellman_gauge_bound_locallyIntegrable (alpha - 3) (by linarith)
      (by linarith) _ h.dx_continuousOn CX hCX hbX
  · exact bellman_gauge_bound_locallyIntegrable (alpha - 1) (by linarith)
      (by linarith) _ (h.directional_contDiffOn (0, 1)).continuousOn Cv hCv hbv
  · exact bellman_gauge_bound_locallyIntegrable (alpha - 2) (by linarith)
      (by linarith) _ h.dvv_continuousOn Cvv hCvv hbvv

end HypoellipticAleksandrov.KineticAleksandrov

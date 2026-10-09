module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ShellGeometry
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith

/-! # Integrability of kinetic powers, including the origin -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Set

/-- Powers above degree minus d are locally integrable in each native vector factor. -/
theorem norm_rpow_locallyIntegrable (d : ℕ) (hd : 1 ≤ d) (p : ℝ) (hp : -1 < p) :
    LocallyIntegrable (fun x : PDE.Vec d => ‖x‖ ^ p) volume := by
  have hdim : Module.finrank ℝ (PDE.Vec d) = d := by
    simp only [PDE.Vec, Module.finrank_pi, Fintype.card_fin]
  apply locallyIntegrable_of_norm_le_rpow (by simpa only [hdim] using hd)
    (C := 1) (α := -p)
  · rw [hdim]
    have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith only [hp, hdR]
  · filter_upwards [] with x
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
      neg_neg, one_mul]
    exact le_rfl
  · exact (measurable_norm.pow measurable_const).aestronglyMeasurable

/-- Products of integrable factor powers are locally integrable on product volume. -/
theorem product_norm_rpow_locallyIntegrable (d : ℕ) (hd : 1 ≤ d) (p : ℝ)
    (hp : -1 < p) :
    LocallyIntegrable (fun q : XV d => ‖q.1‖ ^ p * ‖q.2‖ ^ p) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  have h1 := (norm_rpow_locallyIntegrable d hd p hp).integrableOn_isCompact
    (hK.image continuous_fst)
  have h2 := (norm_rpow_locallyIntegrable d hd p hp).integrableOn_isCompact
    (hK.image continuous_snd)
  have hi := h1.mul_prod h2
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at hi
  change IntegrableOn _ ((Prod.fst '' K) ×ˢ (Prod.snd '' K)) volume at hi
  exact hi.mono_set (fun q hq => ⟨mem_image_of_mem _ hq, mem_image_of_mem _ hq⟩)

/-- Both vector axes are null when the vector dimension is positive. -/
theorem coordinates_ne_zero_ae (d : ℕ) (hd : 1 ≤ d) :
    ∀ᵐ q : XV d ∂volume, q.1 ≠ 0 ∧ q.2 ≠ 0 := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  rw [Measure.volume_eq_prod]
  apply (Measure.ae_prod_iff_ae_ae
    (((measurable_fst (measurableSet_singleton (0 : PDE.Vec d))).compl).inter
      ((measurable_snd (measurableSet_singleton (0 : PDE.Vec d))).compl))).mpr
  filter_upwards [volume.ae_ne (0 : PDE.Vec d)] with x hx
  filter_upwards [volume.ae_ne (0 : PDE.Vec d)] with v hv
  exact ⟨hx, hv⟩

/-- Negative gauge powers have an integrable product majorant of degree beta/4. -/
theorem rho_rpow_product_bound (d : ℕ) (beta : ℝ) (hb : beta ≤ 0)
    (q : XV d) (hx : q.1 ≠ 0) (hv : q.2 ≠ 0) :
    Real.rpow (rho q) beta ≤ ‖q.1‖ ^ (beta / 4) * ‖q.2‖ ^ (beta / 4) := by
  have hr := rho_nonneg q
  have hcoord := rho_coordinate_bounds q
  have hp : ‖q.1‖ * ‖q.2‖ ≤ rho q ^ 4 := by
    calc
      ‖q.1‖ * ‖q.2‖ ≤ rho q ^ 3 * rho q :=
        mul_le_mul ((PDE.norm_le_vecEuclideanNorm _).trans hcoord.1)
          ((PDE.norm_le_vecEuclideanNorm _).trans hcoord.2)
          (norm_nonneg _) (pow_nonneg hr _)
      _ = rho q ^ 4 := by ring
  have hh := Real.rpow_le_rpow_of_nonpos
    (mul_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr hv)) hp
    (by linarith only [hb] : beta / 4 ≤ 0)
  rw [Real.mul_rpow (norm_nonneg _) (norm_nonneg _)] at hh
  have he : (rho q ^ (4 : ℕ)) ^ (beta / 4 : ℝ) = (rho q) ^ beta := by
    rw [← Real.rpow_natCast_mul hr]
    congr 1
    ring
  simp only [Real.rpow_eq_pow]
  rwa [he] at hh

/-- Gauge degree greater than minus four gives local integrability for all d≥1. -/
theorem rho_rpow_locallyIntegrable (d : ℕ) (hd : 1 ≤ d) (beta : ℝ)
    (hb : -4 < beta) (hb0 : beta ≤ 0) :
    LocallyIntegrable (fun q : XV d => Real.rpow (rho q) beta) volume := by
  simp only [Real.rpow_eq_pow]
  have hprod := product_norm_rpow_locallyIntegrable d hd (beta / 4) (by linarith only [hb])
  apply hprod.mono
    (((continuous_rho d).measurable.pow measurable_const).aestronglyMeasurable)
  filter_upwards [coordinates_ne_zero_ae d hd] with q hq
  simp only [Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (rho_nonneg q) _),
    abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
      (Real.rpow_nonneg (norm_nonneg _) _))]
  exact rho_rpow_product_bound d beta hb0 q hq.1 hq.2

/-- Measurable jets with the proved kinetic power bound are locally integrable. -/
theorem locallyIntegrable_of_rho_bound (d : ℕ) (hd : 1 ≤ d) (beta : ℝ)
    (hb : -4 < beta) (hb0 : beta ≤ 0) (f : XV d → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ᵐ q ∂volume, |f q| ≤ C * Real.rpow (rho q) beta) :
    LocallyIntegrable f volume := by
  apply ((rho_rpow_locallyIntegrable d hd beta hb hb0).smul C).mono hf.aestronglyMeasurable
  filter_upwards [hbound] with q hq
  change ‖f q‖ ≤ ‖C * Real.rpow (rho q) beta‖
  simp only [Real.rpow_eq_pow] at hq ⊢
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hC (Real.rpow_nonneg (rho_nonneg _) _))]
  exact hq

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

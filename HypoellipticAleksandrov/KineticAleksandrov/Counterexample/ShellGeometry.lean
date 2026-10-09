module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Geometry
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic.Ring

/-! # The exact spatial--velocity Jacobian of kinetic dilation -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Set

/-- Product Lebesgue volume scales by the reciprocal of the kinetic determinant. -/
theorem map_dilate_volume (d : ℕ) (r : ℝ) (hr : 0 < r) :
    Measure.map (dilate (d := d) r) volume =
      ENNReal.ofReal (r⁻¹ ^ (4 * d)) • volume := by
  rw [Measure.volume_eq_prod]
  change Measure.map (Prod.map (fun x : PDE.Vec d => r ^ 3 • x)
    (fun v : PDE.Vec d => r • v)) ((volume : Measure (PDE.Vec d)).prod volume) = _
  rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_addHaar_smul volume (pow_ne_zero 3 hr.ne'),
    Measure.map_addHaar_smul volume hr.ne',
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    ← ENNReal.ofReal_mul (abs_nonneg _)]
  simp only [Module.finrank_pi, Fintype.card_fin]
  congr 2
  rw [abs_of_pos (inv_pos.mpr (pow_pos (pow_pos hr 3) _)),
    abs_of_pos (inv_pos.mpr (pow_pos hr _)), ← mul_inv, ← pow_mul,
    ← pow_add, inv_pow]
  congr 1
  ring

/-- The gauge's defining Euclidean polynomial is its sixth power. -/
theorem rho_pow_six {d : ℕ} (q : XV d) :
    rho q ^ (6 : ℕ) = PDE.vecNormSq q.1 + PDE.vecNormSq q.2 ^ (3 : ℕ) := by
  unfold rho
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_mul_natCast
    (add_nonneg (PDE.vecNormSq_nonneg _) (pow_nonneg (PDE.vecNormSq_nonneg _) _))]
  norm_num

/-- Euclidean coordinates obey the exact anisotropic gauge weights. -/
theorem rho_coordinate_bounds {d : ℕ} (q : XV d) :
    PDE.vecEuclideanNorm q.1 ≤ rho q ^ 3 ∧ PDE.vecEuclideanNorm q.2 ≤ rho q := by
  have hr := rho_nonneg q
  have he := rho_pow_six q
  have hx := PDE.vecNormSq_nonneg q.1
  have hv := PDE.vecNormSq_nonneg q.2
  constructor
  · apply (sq_le_sq₀ (PDE.vecEuclideanNorm_nonneg _) (pow_nonneg hr _)).mp
    rw [PDE.vecEuclideanNorm_sq, ← pow_mul]
    norm_num only at *
    linarith only [he, pow_nonneg hv 3]
  · apply (pow_le_pow_iff_left₀ (PDE.vecEuclideanNorm_nonneg _) hr
      (by decide : (6 : ℕ) ≠ 0)).mp
    rw [show (6 : ℕ) = 2 * 3 by decide, pow_mul, PDE.vecEuclideanNorm_sq]
    rw [show (2 * 3 : ℕ) = 6 by decide, he]
    exact le_add_of_nonneg_left hx

/-- Bounded gauge sublevels have bounded native product norm. -/
theorem norm_le_of_rho_le {d : ℕ} (R : ℝ) (q : XV d)
    (hq : rho q ≤ R) : ‖q‖ ≤ max (R ^ 3) R := by
  have hb := rho_coordinate_bounds q
  rw [Prod.norm_def]
  exact max_le
    ((PDE.norm_le_vecEuclideanNorm _).trans
      (hb.1.trans ((pow_le_pow_left₀ (rho_nonneg q) hq 3).trans (le_max_left _ _))))
    ((PDE.norm_le_vecEuclideanNorm _).trans (hb.2.trans (hq.trans (le_max_right _ _))))

/-- Every closed gauge sublevel is compact in the native finite-dimensional topology. -/
theorem isCompact_rho_sublevel (d : ℕ) (R : ℝ) :
    IsCompact {q : XV d | rho q ≤ R} := by
  apply Metric.isCompact_of_isClosed_isBounded
    (isClosed_le (continuous_rho d) continuous_const)
  exact isBounded_iff_forall_norm_le.2
    ⟨max (R ^ 3) R, fun q hq => norm_le_of_rho_le R q hq⟩

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

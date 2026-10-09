module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarJetFormulas
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarHessianScaling
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarRescaled
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileHomogeneousBounds
import Mathlib.Tactic

/-! # Genuine compact jet bounds for the scalar construction -/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Filter Asymptotics Set

/-- The source's cancelled position similarity factor. -/
def scalarPositionFactor (gamma : ScalarGamma) (Lam s : ℝ) : ℝ :=
  gamma.1 * F gamma Lam s - s / 3 * deriv (F gamma Lam) s

/-- The cancelled position similarity factor is continuous. -/
theorem scalarPositionFactor_continuous (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam) :
    Continuous (scalarPositionFactor gamma Lam) := by
  have hf := F_contDiff_two gamma Lam hLam
  exact continuous_const.mul hf.continuous |>.sub
    ((continuous_id.div_const 3).mul (hf.continuous_deriv (by norm_num)))

/-- The absolute position jet equals the reflected rescaling of the cancelled factor. -/
theorem scalarGx_abs_rescaled (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam) (q : XV 1) :
    |scalarGx gamma Lam q 0| =
      |scalarRescaled (scalarPositionFactor gamma Lam) (3 * gamma.1 - 3) q| := by
  rcases lt_trichotomy (q.1 0) 0 with hx | hx | hx
  · simp only [scalarGx, hx.ne, ↓reduceIte, scalarRescaled, not_lt.mpr hx.le, hx]
    rw [scalarProfile_dx_negative gamma Lam hLam q hx,
      scalarAnsatz_deriv_x_cancel gamma Lam _ _ hLam (neg_pos.mpr hx), abs_neg]
    simp only [scalarPositionFactor, show (3 * gamma.1 - 3) / 3 = gamma.1 - 1 by ring]
  · simp only [scalarGx, hx, ↓reduceIte, Pi.zero_apply, scalarRescaled, lt_self_iff_false]
  · simp only [scalarGx, hx.ne', ↓reduceIte, scalarRescaled, hx]
    rw [scalarProfile_dx_positive gamma Lam hLam q hx,
      scalarAnsatz_deriv_x_cancel gamma Lam _ _ hLam hx]
    simp only [scalarPositionFactor, show (3 * gamma.1 - 3) / 3 = gamma.1 - 1 by ring]

/-- The absolute velocity jet equals the reflected first-derivative rescaling. -/
theorem scalarGv_abs_rescaled (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam) (q : XV 1) :
    |scalarGv gamma Lam q 0| =
      |scalarRescaled (deriv (F gamma Lam)) (3 * gamma.1 - 1) q| := by
  rcases lt_trichotomy (q.1 0) 0 with hx | hx | hx
  · simp only [scalarGv, hx.ne, ↓reduceIte, scalarRescaled, not_lt.mpr hx.le, hx]
    rw [scalarProfile_dv_negative gamma Lam hLam q hx,
      scalarAnsatz_deriv_v_power gamma Lam _ _ hLam (neg_pos.mpr hx)]
    simp only [neg_mul, neg_neg, show (3 * gamma.1 - 1) / 3 = gamma.1 - 1 / 3 by ring]
  · simp only [scalarGv, hx, ↓reduceIte, Pi.zero_apply, scalarRescaled, lt_self_iff_false]
  · simp only [scalarGv, hx.ne', ↓reduceIte, scalarRescaled, hx]
    rw [scalarProfile_dv_positive gamma Lam hLam q hx,
      scalarAnsatz_deriv_v_power gamma Lam _ _ hLam hx]
    simp only [neg_mul, abs_neg, show (3 * gamma.1 - 1) / 3 = gamma.1 - 1 / 3 by ring]

/-- The absolute Hessian jet equals the reflected second-derivative rescaling. -/
theorem scalarHess_abs_rescaled (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam)
    (q : XV 1) : |scalarHess gamma Lam q 0 0| =
      |scalarRescaled (deriv (deriv (F gamma Lam))) (3 * gamma.1 - 2) q| := by
  rcases lt_trichotomy (q.1 0) 0 with hx | hx | hx
  · simp only [scalarHess, hx.ne, ↓reduceIte, scalarRescaled, not_lt.mpr hx.le, hx]
    rw [scalarProfile_dvv_negative gamma Lam hLam q hx,
      scalarAnsatz_deriv2_v_power gamma Lam _ _ hLam (neg_pos.mpr hx)]
    simp only [show (3 * gamma.1 - 2) / 3 = gamma.1 - 2 / 3 by ring]
  · simp only [scalarHess, hx, ↓reduceIte, Matrix.zero_apply, scalarRescaled,
      lt_self_iff_false]
  · simp only [scalarHess, hx.ne', ↓reduceIte, scalarRescaled, hx]
    rw [scalarProfile_dvv_positive gamma Lam hLam q hx,
      scalarAnsatz_deriv2_v_power gamma Lam _ _ hLam hx]
    simp only [show (3 * gamma.1 - 2) / 3 = gamma.1 - 2 / 3 by ring]

/-- Native supremum norm in dimension one is exactly the sole scalar absolute value. -/
theorem scalar_vec_norm (v : PDE.Vec 1) : ‖v‖ = |v 0| := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (abs_nonneg (v 0))).mpr
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact le_rfl
  · simpa only [Real.norm_eq_abs] using norm_le_pi_norm v 0

/-- Both actual derivative rays can be used in the absolute-value rescaling bound. -/
theorem scalar_positive_power_to_abs (f : ℝ → ℝ) (beta : ℝ)
    (ht : IsBigO atTop f (fun s => Real.rpow s beta)) :
    IsBigO atTop f (fun s => Real.rpow |s| beta) := by
  apply ht.congr' EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  simp only [abs_of_pos hs]

/-- All scalar representative jets are uniformly bounded on compact sets away from zero. -/
theorem scalarJets_compact_bound (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam)
    (hmatch : Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3)) =
      Real.rpow Lam (-gamma.1)) (K : Set (XV 1)) (hK : IsCompact K) (hz : 0 ∉ K) :
    ∃ M : ℝ, ∀ q ∈ K, ‖scalarGx gamma Lam q‖ ≤ M ∧ ‖scalarGv gamma Lam q‖ ≤ M ∧
      ∀ i k, |scalarHess gamma Lam q i k| ≤ M := by
  have hf := F_contDiff_two gamma Lam hLam
  have hd : ContDiff ℝ 1 (deriv (F gamma Lam)) := hf.deriv'
  have hp := F_derivatives_isBigO_atTop gamma Lam hLam
  have hn := F_derivatives_isBigO_atBot gamma Lam hLam hmatch
  obtain ⟨Mx, hx⟩ := scalarRescaled_compact_bound (scalarPositionFactor gamma Lam)
    (3 * gamma.1 - 3) (scalarPositionFactor_continuous gamma Lam hLam)
    (scalar_positive_power_to_abs _ _ (F_position_cancellation_atTop gamma Lam hLam))
    (F_position_cancellation_atBot gamma Lam hLam hmatch) K hK hz
  obtain ⟨Mv, hv⟩ := scalarRescaled_compact_bound (deriv (F gamma Lam)) (3 * gamma.1 - 1)
    hd.continuous (scalar_positive_power_to_abs _ _ hp.1) hn.1 K hK hz
  obtain ⟨Mh, hh⟩ := scalarRescaled_compact_bound (deriv (deriv (F gamma Lam)))
    (3 * gamma.1 - 2) hd.continuous_deriv_one
    (scalar_positive_power_to_abs _ _ hp.2) hn.2 K hK hz
  refine ⟨max Mx (max Mv Mh), ?_⟩
  intro q hq
  constructor
  · rw [scalar_vec_norm, scalarGx_abs_rescaled gamma Lam hLam]
    exact (hx q hq).trans (le_max_left _ _)
  constructor
  · rw [scalar_vec_norm, scalarGv_abs_rescaled gamma Lam hLam]
    exact (hv q hq).trans ((le_max_left _ _).trans (le_max_right _ _))
  · intro i k
    have hi : i = 0 := Subsingleton.elim _ _
    have hk : k = 0 := Subsingleton.elim _ _
    subst i k
    rw [scalarHess_abs_rescaled gamma Lam hLam]
    exact (hh q hq).trans ((le_max_right _ _).trans (le_max_right _ _))

/-- Euclidean normalization in dimension one agrees with the scalar absolute value. -/
theorem scalar_vec_euclidean_norm (v : PDE.Vec 1) : PDE.vecEuclideanNorm v = |v 0| := by
  simp only [PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot, Fin.sum_univ_one,
    ← sq, Real.sqrt_sq_eq_abs]

/-- The selected velocity representative has the required global kinetic gradient bound. -/
theorem scalarGv_gauge_bound (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam)
    (hmatch : Pgamma gamma.1 - Qgamma gamma.1 * Real.rpow Lam (-(1 / 3)) =
      Real.rpow Lam (-gamma.1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : XV 1, q ≠ 0 → PDE.vecEuclideanNorm (scalarGv gamma Lam q) ≤
      C * Real.rpow (rho q) (3 * gamma.1 - 1) := by
  obtain ⟨C, hC, hbound⟩ := homogeneous_component_bound (fun q => scalarGv gamma Lam q 0)
    (3 * gamma.1 - 1)
    (fun r hr q => congrArg (fun w => w 0) (scalarGv_homogeneous gamma Lam r hLam hr q))
    (by
      intro K hK hz
      obtain ⟨M, hM⟩ := scalarJets_compact_bound gamma Lam hLam hmatch K hK hz
      exact ⟨M, fun q hq => by simpa only [scalar_vec_norm] using (hM q hq).2.1⟩)
  refine ⟨C, hC, ?_⟩
  intro q hq
  rw [scalar_vec_euclidean_norm]
  exact hbound q hq

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

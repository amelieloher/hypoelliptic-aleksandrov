module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarClassical
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarNegativeJets
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileBounds
import Mathlib.Tactic

/-!
# Scalar profile equation on the native product

The actual full-product selectors satisfy the source equation off the position axis,
and therefore almost everywhere for native Lebesgue measure.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Filter Set MeasureTheory
open scoped Topology ContDiff

/-- The source formula agrees locally with the positive native ansatz. -/
theorem scalarProfile_eq_positive_nhds (gamma : ScalarGamma) (Lam : ℝ)
    (q : XV 1) (hx : 0 < q.1 0) :
    scalarProfile gamma Lam =ᶠ[𝓝 q] scalarNativeAnsatz gamma Lam := by
  have hc : Continuous (fun z : XV 1 => z.1 0) := by fun_prop
  filter_upwards [hc.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hx)] with z hz
  simp only [scalarProfile, scalarNativeAnsatz, show 0 < z.1 0 from hz, ↓reduceIte]

/-- The source formula agrees locally with the reflected native ansatz. -/
theorem scalarProfile_eq_negative_nhds (gamma : ScalarGamma) (Lam : ℝ)
    (q : XV 1) (hx : q.1 0 < 0) :
    scalarProfile gamma Lam =ᶠ[𝓝 q] fun z => scalarNativeAnsatz gamma Lam (-z) := by
  have hc : Continuous (fun z : XV 1 => z.1 0) := by fun_prop
  filter_upwards [hc.continuousAt.preimage_mem_nhds (Iio_mem_nhds hx)] with z hz
  simp only [scalarProfile, scalarNativeAnsatz, Pi.neg_apply, Prod.fst_neg, Prod.snd_neg,
    not_lt.mpr (show z.1 0 < 0 from hz).le, show z.1 0 < 0 from hz, ↓reduceIte]

/-- The profile is C² at every point off the position axis. -/
theorem scalarProfile_contDiffAt_off_axis (gamma : ScalarGamma) (Lam : ℝ)
    (hLam : 0 < Lam) (q : XV 1) (hx : q.1 0 ≠ 0) :
    ContDiffAt ℝ 2 (scalarProfile gamma Lam) q := by
  rcases lt_or_gt_of_ne hx with hx | hx
  · have hn := scalarNativeAnsatz_contDiffAt gamma Lam hLam (-q) (neg_pos.mpr hx)
    exact (hn.comp q contDiffAt_id.neg).congr_of_eventuallyEq
      (scalarProfile_eq_negative_nhds gamma Lam q hx)
  · exact (scalarNativeAnsatz_contDiffAt gamma Lam hLam q hx).congr_of_eventuallyEq
      (scalarProfile_eq_positive_nhds gamma Lam q hx)

/-- The positive half-plane position selector is the source position derivative. -/
theorem scalarProfile_dx_positive (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam)
    (q : XV 1) (hx : 0 < q.1 0) :
    dx (scalarProfile gamma Lam) q 0 =
      deriv (fun x => scalarAnsatz gamma Lam x (q.2 0)) (q.1 0) := by
  rw [dx_eq_scalar_slice _ q
    ((scalarProfile_contDiffAt_off_axis gamma Lam hLam q hx.ne').differentiableAt
      (by norm_num))]
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Ioi_mem_nhds hx] with x hx
  simp only [scalarPositionSlice, scalarProfile, show 0 < x from hx, ↓reduceIte]

/-- The positive half-plane Hessian selector is the actual source velocity derivative. -/
theorem scalarProfile_dvv_positive (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam)
    (q : XV 1) (hx : 0 < q.1 0) :
    dvv (scalarProfile gamma Lam) q 0 0 =
      deriv (deriv (scalarAnsatz gamma Lam (q.1 0))) (q.2 0) := by
  rw [dvv_eq_scalar_slice _ q (scalarProfile_contDiffAt_off_axis gamma Lam hLam q hx.ne')]
  congr 2
  funext v
  simp only [scalarProfile, scalarVelocitySlice, hx, ↓reduceIte]

/-- The reflected position selector includes the source minus sign. -/
theorem scalarProfile_dx_negative (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam)
    (q : XV 1) (hx : q.1 0 < 0) :
    dx (scalarProfile gamma Lam) q 0 =
      -deriv (fun x => scalarAnsatz gamma Lam x (-q.2 0)) (-q.1 0) := by
  rw [dx_eq_scalar_slice _ q
    ((scalarProfile_contDiffAt_off_axis gamma Lam hLam q hx.ne).differentiableAt
      (by norm_num))]
  have he : (fun x => scalarProfile gamma Lam (scalarPositionSlice q x)) =ᶠ[𝓝 (q.1 0)]
      fun x => scalarAnsatz gamma Lam (-x) (-q.2 0) := by
    filter_upwards [Iio_mem_nhds hx] with x hx
    simp only [scalarPositionSlice, scalarProfile, show x < 0 from hx,
      not_lt.mpr (show x < 0 from hx).le, ↓reduceIte]
  rw [he.deriv_eq]
  exact deriv_comp_neg (fun x => scalarAnsatz gamma Lam x (-q.2 0)) (q.1 0)

/-- The reflected velocity Hessian retains its positive second-derivative sign. -/
theorem scalarProfile_dvv_negative (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam)
    (q : XV 1) (hx : q.1 0 < 0) :
    dvv (scalarProfile gamma Lam) q 0 0 =
      deriv (deriv (scalarAnsatz gamma Lam (-q.1 0))) (-q.2 0) := by
  rw [dvv_eq_scalar_slice _ q (scalarProfile_contDiffAt_off_axis gamma Lam hLam q hx.ne)]
  have he : (fun v => scalarProfile gamma Lam (scalarVelocitySlice q v)) =
      fun v => scalarAnsatz gamma Lam (-q.1 0) (-v) := by
    funext v
    simp only [scalarVelocitySlice, scalarProfile, hx, not_lt.mpr hx.le, ↓reduceIte]
  rw [he]
  exact scalar_deriv2_comp_neg _ _

/-- The native full-product equation holds everywhere off the position axis. -/
theorem scalarProfile_equation_off_axis (gamma : ScalarGamma) (Lam : ℝ)
    (hLam : 0 < Lam) (q : XV 1) (hx : q.1 0 ≠ 0) :
    matrixContraction (scalarProfileCoefficient Lam q) (dvv (scalarProfile gamma Lam) q) =
      PDE.vecDot q.2 (dx (scalarProfile gamma Lam) q) := by
  simp only [matrixContraction, scalarProfileCoefficient, PDE.vecDot,
    Fin.sum_univ_one, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
  change aLambda Lam (q.1 0) (q.2 0) * dvv (scalarProfile gamma Lam) q 0 0 =
    q.2 0 * dx (scalarProfile gamma Lam) q 0
  rcases lt_or_gt_of_ne hx with hx | hx
  · rw [scalarProfile_dx_negative gamma Lam hLam q hx,
      scalarProfile_dvv_negative gamma Lam hLam q hx,
      ← aLambda_reflect Lam (q.1 0) (q.2 0)]
    simpa only [neg_mul, mul_neg] using
      scalar_ansatz_ode gamma Lam (-q.1 0) (-q.2 0) hLam (neg_pos.mpr hx)
  · rw [scalarProfile_dx_positive gamma Lam hLam q hx,
      scalarProfile_dvv_positive gamma Lam hLam q hx]
    exact scalar_ansatz_ode gamma Lam _ _ hLam hx

/-- The source equation holds for native Lebesgue almost every point. -/
theorem scalarProfile_equation_ae (gamma : ScalarGamma) (Lam : ℝ) (hLam : 0 < Lam) :
    ∀ᵐ q ∂volume,
      matrixContraction (scalarProfileCoefficient Lam q) (dvv (scalarProfile gamma Lam) q) =
        PDE.vecDot q.2 (dx (scalarProfile gamma Lam) q) := by
  filter_upwards [coordinates_ne_zero_ae 1 (by omega)] with q hq
  apply scalarProfile_equation_off_axis gamma Lam hLam q
  intro hz
  apply hq.1
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  exact hz

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

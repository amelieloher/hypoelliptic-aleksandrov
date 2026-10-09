module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Flattening
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Shell
public import HypoellipticAleksandrov.Coefficients.Ellipticity
import Mathlib.Tactic.Linarith

/-! # The literal shell source and its positivity -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Set
open scoped MatrixOrder

/-- The literal stationary source formula in the source manuscript. -/
noncomputable def flatSource {d : ℕ} (A : XV d → PDE.Mat d)
    (H : XV d → ℝ) (Psi : ℝ → ℝ) (alpha r : ℝ) (q : XV d) : ℝ :=
  Real.rpow r (-alpha) * deriv (deriv Psi) (H q / Real.rpow r alpha) *
    PDE.vecDot ((A q).mulVec (dv H q)) (dv H q)

/-- The same source formula evaluated on an explicit selected weak velocity jet. -/
noncomputable def flatSourceWithJet {d : ℕ} (A : XV d → PDE.Mat d)
    (H : XV d → ℝ) (gv : XV d → PDE.Vec d) (alpha r : ℝ) (q : XV d) : ℝ :=
  Real.rpow r (-alpha) * deriv (deriv flatteningPsi) (H q / Real.rpow r alpha) *
    PDE.vecDot ((A q).mulVec (gv q)) (gv q)

/-- Matrix upper order bounds the quadratic form in the source's Euclidean norm. -/
theorem quadratic_upper_of_loewner {d : ℕ} (Lam : ℝ) (A : PDE.Mat d)
    (hA : A ≤ Lam • (1 : PDE.Mat d)) (w : PDE.Vec d) :
    PDE.vecDot (A.mulVec w) w ≤ Lam * PDE.vecNormSq w := by
  have hgap : (Lam • (1 : PDE.Mat d) - A).PosSemidef := Matrix.le_iff.mp hA
  have hquad := hgap.dotProduct_mulVec_nonneg w
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul] at hquad
  have hu : PDE.vecDot w (A.mulVec w) ≤ Lam * PDE.vecNormSq w := by
    simpa only [PDE.vecNormSq, PDE.vecDot, dotProduct, mul_comm] using sub_nonneg.mp hquad
  simpa only [PDE.vecDot, mul_comm] using hu

/-- A nonnegative lower ellipticity bound makes the source quadratic form nonnegative. -/
theorem quadratic_nonneg_of_loewner {d : ℕ} (lam : ℝ) (hlam : 0 ≤ lam)
    (A : PDE.Mat d) (hA : lam • (1 : PDE.Mat d) ≤ A) (w : PDE.Vec d) :
    0 ≤ PDE.vecDot (A.mulVec w) w := by
  have h := vecDot_mulVec_lower_of_loewner hA w
  have hn := (mul_nonneg hlam (PDE.vecNormSq_nonneg w)).trans h
  simpa only [PDE.vecDot, mul_comm] using hn

/-- The fixed source vanishes outside the closed profile shell. -/
theorem flatSourceWithJet_eq_zero_off_shell {d : ℕ} (A : XV d → PDE.Mat d)
    (H : XV d → ℝ) (gv : XV d → PDE.Vec d) (alpha r : ℝ) (hr : 0 < r)
    (q : XV d) (hq : q ∉ profileShell H alpha r) :
    flatSourceWithJet A H gv alpha r q = 0 := by
  have hp := Real.rpow_pos_of_pos hr alpha
  have hor : H q < Real.rpow r alpha ∨ 2 * Real.rpow r alpha < H q := by
    simpa only [profileShell, mem_ofPred_eq, not_and_or, not_le] using hq
  unfold flatSourceWithJet
  simp only [Real.rpow_eq_pow] at hor ⊢
  rcases hor with hlo | hhi
  · rw [flatteningPsi_deriv2_eq_zero_of_lt _ ((div_lt_one hp).2 hlo)]
    ring
  · rw [flatteningPsi_deriv2_eq_zero_of_gt _ ((lt_div_iff₀ hp).2 hhi)]
    ring

/-- The selected weak source is measurable under the source's literal coefficient assumptions. -/
theorem measurable_flatSourceWithJet {d : ℕ} (A : XV d → PDE.Mat d)
    (H : XV d → ℝ) (gv : XV d → PDE.Vec d) (alpha r : ℝ)
    (hA : ∀ i k, Measurable (fun q => A q i k)) (hH : Measurable H)
    (hgv : Measurable gv) : Measurable (flatSourceWithJet A H gv alpha r) := by
  have hpsi : Continuous (deriv (deriv flatteningPsi)) := by
    rw [funext deriv_flatteningPsi]
    exact contDiff_flatteningSlope.continuous_deriv (by simp)
  have hg (i : Fin d) : Measurable (fun q => gv q i) := (measurable_pi_apply i).comp hgv
  unfold flatSourceWithJet PDE.vecDot Matrix.mulVec dotProduct
  exact (measurable_const.mul
    (hpsi.measurable.comp (hH.div_const (Real.rpow r alpha)))).mul
    (Finset.measurable_sum _ (fun i _ =>
      (Finset.measurable_sum _ (fun k _ => (hA i k).mul (hg k))).mul (hg i)))

/-- The classical selector source equals the selected weak-jet formula almost everywhere. -/
theorem flatSource_ae_eq_jet_of_profile {d : ℕ} {alpha : ℝ}
    (hprofile : CounterProfileStatement d alpha) (r : ℝ) :
    flatSource (profileMatrix hprofile) (profileFunction hprofile) flatteningPsi alpha r =ᵐ[volume]
      flatSourceWithJet (profileMatrix hprofile) (profileFunction hprofile)
        (profileVelocityJet hprofile) alpha r := by
  have he := (selectedProfile_spec hprofile).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  filter_upwards [he] with q hq
  unfold flatSource flatSourceWithJet
  rw [hq.2.1]

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.GaussianBarrierCutoff
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.MovingFrame
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-! # The source Gaussian barrier with its explicit smooth zero extension -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Filter Set Parabolic Scaling
open scoped Topology

/-- The literal Gaussian formula, used analytically only on the definite covariance strip. -/
def gaussianFormula {d : ℕ} (chi : ℝ → ℝ)
    (lam Lam H h L ell tminus sblock : ℝ) (x v : ℝ → PDE.Vec d)
    (P : KineticPoint d) : ℝ :=
  let s := P.time - tminus
  let sigma := s - sblock
  ell * chi (sigma / h) *
    (Real.exp (-Xi d lam Lam H h * sigma -
      qform lam h sigma (P.position - x s) (P.velocity - v s)) - Real.exp (-L ^ 2))

/-- The source barrier, extended by zero from the positive-definite cutoff strip. -/
def gaussianBarrier {d : ℕ} (lam Lam H h L ell tminus sblock : ℝ)
    (x v : ℝ → PDE.Vec d) (P : KineticPoint d) : ℝ :=
  if -(1 / 128 : ℝ) < (P.time - tminus - sblock) / h then
    gaussianFormula barrierCutoff lam Lam H h L ell tminus sblock x v P
  else 0

/-- Outside the covariance strip the source cutoff kills the entire formula. -/
theorem gaussianBarrier_eq_formula {d : ℕ} (lam Lam H h L ell tminus sblock : ℝ)
    (x v : ℝ → PDE.Vec d) (P : KineticPoint d) :
    gaussianBarrier lam Lam H h L ell tminus sblock x v P =
      gaussianFormula barrierCutoff lam Lam H h L ell tminus sblock x v P := by
  unfold gaussianBarrier
  split_ifs with hs
  · rfl
  · unfold gaussianFormula
    dsimp only
    rw [barrierCutoff_zero (le_of_not_gt hs), mul_zero, zero_mul]

/-- Smoothness of the literal formula at each point of the closed definite strip. -/
theorem contDiffAt_raw_gaussianFormula {d : ℕ} {lam h : ℝ}
    (hlam : 0 < lam) (hh : 0 < h) (Lam H L ell tminus sblock : ℝ)
    {x v : ℝ → PDE.Vec d} (hx : ContDiff ℝ (⊤ : ℕ∞) x)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (Q : ℝ × (PDE.Vec d × PDE.Vec d))
    (hQ : -(1 / 128 : ℝ) ≤ (Q.1 - tminus - sblock) / h) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (rawLift (gaussianFormula barrierCutoff lam Lam H h L ell tminus sblock x v)) Q := by
  have hs : -(h / 128) ≤ Q.1 - tminus - sblock := by
    have hz := (le_div_iff₀ hh).mp hQ
    linarith only [hz]
  have hmap : ContDiff ℝ (⊤ : ℕ∞)
      (fun T : ℝ × (PDE.Vec d × PDE.Vec d) =>
        (T.1 - tminus - sblock, (T.2.1 - x (T.1 - tminus),
          T.2.2 - v (T.1 - tminus)))) := by
    exact ((contDiff_fst.sub contDiff_const).sub contDiff_const).prodMk
      ((contDiff_fst.comp contDiff_snd).sub
        (hx.comp (contDiff_fst.sub contDiff_const)) |>.prodMk
        ((contDiff_snd.comp contDiff_snd).sub
          (hv.comp (contDiff_fst.sub contDiff_const))))
  have hq := (contDiffAt_qform_raw hlam hh hs
    (Q.2.1 - x (Q.1 - tminus)) (Q.2.2 - v (Q.1 - tminus))).comp Q hmap.contDiffAt
  have htime : ContDiff ℝ (⊤ : ℕ∞)
      (fun T : ℝ × (PDE.Vec d × PDE.Vec d) => T.1 - tminus - sblock) := by fun_prop
  have hchi := contDiff_barrierCutoff.comp (htime.div_const h)
  change ContDiffAt ℝ (⊤ : ℕ∞) (fun T : ℝ × (PDE.Vec d × PDE.Vec d) =>
    ell * barrierCutoff ((T.1 - tminus - sblock) / h) *
      (Real.exp (-Xi d lam Lam H h * (T.1 - tminus - sblock) -
        qform lam h (T.1 - tminus - sblock)
          (T.2.1 - x (T.1 - tminus)) (T.2.2 - v (T.1 - tminus))) - Real.exp (-L ^ 2))) Q
  exact (contDiffAt_const.mul hchi.contDiffAt).mul
    (((contDiffAt_const.mul htime.contDiffAt).sub hq).exp.sub contDiffAt_const)

/-- Global smoothness follows by gluing to zero, without a global inverse smoothness claim. -/
theorem contDiff_raw_gaussianBarrier {d : ℕ} {lam h : ℝ}
    (hlam : 0 < lam) (hh : 0 < h) (Lam H L ell tminus sblock : ℝ)
    {x v : ℝ → PDE.Vec d} (hx : ContDiff ℝ (⊤ : ℕ∞) x)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) :
    ContDiff ℝ (⊤ : ℕ∞)
      (rawLift (gaussianBarrier lam Lam H h L ell tminus sblock x v)) := by
  rw [contDiff_iff_contDiffAt]
  intro Q
  by_cases hs : -(1 / 128 : ℝ) ≤ (Q.1 - tminus - sblock) / h
  · have hf := contDiffAt_raw_gaussianFormula hlam hh Lam H L ell tminus sblock hx hv Q hs
    apply hf.congr_of_eventuallyEq
    exact Eventually.of_forall (fun T => gaussianBarrier_eq_formula _ _ _ _ _ _ _ _ _ _ _)
  · have ht : Continuous (fun T : ℝ × (PDE.Vec d × PDE.Vec d) =>
        (T.1 - tminus - sblock) / h) := by fun_prop
    have he : ∀ᶠ T in 𝓝 Q, (T.1 - tminus - sblock) / h < -(1 / 128 : ℝ) :=
      ht.continuousAt.eventually (gt_mem_nhds (lt_of_not_ge hs))
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [he] with T hT
    change gaussianBarrier lam Lam H h L ell tminus sblock x v
      ⟨T.1, T.2.1, T.2.2⟩ = 0
    unfold gaussianBarrier
    exact ite_eq_right (not_lt.mpr hT.le)

end HypoellipticAleksandrov.KineticAleksandrov.Holder

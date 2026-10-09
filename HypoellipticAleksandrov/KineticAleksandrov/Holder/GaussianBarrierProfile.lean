module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.GaussianBarrier
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.MovingFrameOperator
import Mathlib.Tactic

/-! # The smooth Gaussian profile and its literal moving-frame representation -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Parabolic Scaling Filter
open scoped Topology

/-- The same source zero extension in stationary raw coordinates. -/
def gaussianProfile {d : ℕ} (lam Lam H h L ell sblock : ℝ)
    (Q : ℝ × (PDE.Vec d × PDE.Vec d)) : ℝ :=
  gaussianBarrier lam Lam H h L ell 0 sblock (fun _ => 0) (fun _ => 0)
    ⟨Q.1, Q.2.1, Q.2.2⟩

/-- The internally constructed stationary profile is smooth everywhere. -/
theorem contDiff_gaussianProfile {d : ℕ} {lam h : ℝ} (hlam : 0 < lam) (hh : 0 < h)
    (Lam H L ell sblock : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (gaussianProfile (d := d) lam Lam H h L ell sblock) :=
  contDiff_raw_gaussianBarrier hlam hh Lam H L ell 0 sblock contDiff_const contDiff_const

/-- Moving the stationary profile produces exactly the whole-carrier source barrier. -/
theorem gaussianBarrier_eq_movingLift {d : ℕ} (lam Lam H h L ell tminus sblock : ℝ)
    (x v : ℝ → PDE.Vec d) :
    gaussianBarrier lam Lam H h L ell tminus sblock x v =
      movingLift (gaussianProfile lam Lam H h L ell sblock) tminus x v := by
  funext P
  simp only [gaussianBarrier, movingLift, movingCoordinates, gaussianProfile,
    sub_zero, gaussianFormula]

/-- On positive block times the stationary profile is the uncut Gaussian formula. -/
theorem gaussianProfile_of_pos {d : ℕ} (lam Lam H L ell sblock : ℝ) {h s : ℝ}
    (hh : 0 < h) (hs : 0 < s - sblock) (y V : PDE.Vec d) :
    gaussianProfile lam Lam H h L ell sblock (s, (y, V)) =
      ell * (Real.exp (-Xi d lam Lam H h * (s - sblock) -
        qform lam h (s - sblock) y V) - Real.exp (-L ^ 2)) := by
  unfold gaussianProfile
  rw [gaussianBarrier_eq_formula]
  dsimp only [gaussianFormula]
  simp only [sub_zero]
  rw [barrierCutoff_one (div_nonneg hs.le hh.le), mul_one]

/-- The time slice agrees locally with the uncut formula at a positive block time. -/
theorem gaussianProfile_time_eventuallyEq {d : ℕ} (lam Lam H L ell sblock : ℝ)
    {h s : ℝ} (hh : 0 < h) (hs : 0 < s - sblock) (y V : PDE.Vec d) :
    (fun t => gaussianProfile lam Lam H h L ell sblock (t, (y, V))) =ᶠ[𝓝 s]
      (fun t => ell * (Real.exp (-Xi d lam Lam H h * (t - sblock) -
        qform lam h (t - sblock) y V) - Real.exp (-L ^ 2))) := by
  have he : ∀ᶠ t in 𝓝 s, 0 < t - sblock :=
    (continuousAt_id.sub continuousAt_const).eventually (lt_mem_nhds hs)
  filter_upwards [he] with t ht
  exact gaussianProfile_of_pos lam Lam H L ell sblock hh ht y V

end HypoellipticAleksandrov.KineticAleksandrov.Holder

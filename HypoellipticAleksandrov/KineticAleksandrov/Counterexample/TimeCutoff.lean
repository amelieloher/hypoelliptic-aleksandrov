module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Flattening
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Barrier
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The fixed smooth convex positive-part cutoff

Rescaling the flattening primitive gives the cutoff used after subtracting the barrier.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Set
open scoped ContDiff

/-- A fixed smooth replacement of the positive part. -/
def timeCutoffTheta (s : ℝ) : ℝ := flatteningPsi (16 * s + 1) / 16

/-- Smoothness of the cutoff at every finite order. -/
theorem contDiff_timeCutoffTheta : ContDiff ℝ ∞ timeCutoffTheta := by
  exact (contDiff_flatteningPsi.comp
    ((contDiff_const.mul contDiff_id).add contDiff_const)).div_const 16

/-- The cutoff vanishes on the negative half-line. -/
theorem timeCutoffTheta_eq_zero (s : ℝ) (hs : s ≤ 0) : timeCutoffTheta s = 0 := by
  unfold timeCutoffTheta
  rw [flatteningPsi_eq_zero _ (by linarith)]
  norm_num

/-- The cutoff is nonnegative globally. -/
theorem timeCutoffTheta_nonneg (s : ℝ) : 0 ≤ timeCutoffTheta s :=
  div_nonneg (flatteningPsi_nonneg _) (by norm_num)

/-- The exact first derivative of the rescaled primitive. -/
theorem deriv_timeCutoffTheta (s : ℝ) :
    deriv timeCutoffTheta s = flatteningSlope (16 * s + 1) := by
  have h := (contDiff_flatteningSlope.continuous.integral_hasStrictDerivAt
    1 (16 * s + 1)).hasDerivAt
  have hc := h.comp s (((hasDerivAt_id s).const_mul 16).add_const 1)
  have hd := hc.div_const 16
  simpa only [timeCutoffTheta, flatteningPsi, id_eq, mul_one,
    mul_div_cancel_right₀ _ (by norm_num : (16 : ℝ) ≠ 0)] using! hd.deriv

/-- The first derivative lies in the unit interval. -/
theorem timeCutoffTheta_deriv_bounds (s : ℝ) :
    0 ≤ deriv timeCutoffTheta s ∧ deriv timeCutoffTheta s ≤ 1 := by
  rw [deriv_timeCutoffTheta]
  exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- Convexity gives the favorable sign of the second-derivative term. -/
theorem convexOn_timeCutoffTheta : ConvexOn ℝ univ timeCutoffTheta := by
  apply Monotone.convexOn_univ_of_deriv
    (contDiff_timeCutoffTheta.differentiable (by simp))
  intro s t h
  rw [deriv_timeCutoffTheta, deriv_timeCutoffTheta]
  exact monotone_flatteningSlope (by linarith)

/-- The second derivative is nonnegative everywhere. -/
theorem timeCutoffTheta_deriv2_nonneg (s : ℝ) :
    0 ≤ deriv (deriv timeCutoffTheta) s := by
  apply Monotone.deriv_nonneg
  intro a b h
  rw [deriv_timeCutoffTheta, deriv_timeCutoffTheta]
  exact monotone_flatteningSlope (by linarith)

/-- The source's uniform lower comparison with the positive part. -/
theorem timeCutoffTheta_lower (s : ℝ) : s - 1 / 8 ≤ timeCutoffTheta s := by
  by_cases hs : s ≤ 1 / 8
  · exact (sub_nonpos.mpr hs).trans (timeCutoffTheta_nonneg s)
  · unfold timeCutoffTheta
    rw [flatteningPsi_eq_affine _ (by linarith)]
    have h := flatteningOffset_bounds.2
    linarith

/-- The literal time-dependent function before the collar extension. -/
def timeCutoffProfile {d : ℕ} (H : XV d → ℝ) (alpha r mu R : ℝ)
    (P : KineticPoint d) : ℝ :=
  timeCutoffTheta (flatProfile H flatteningPsi flatteningOffset alpha r
    (P.position, P.velocity) - barrier mu R P)

/-- Nonnegativity holds on the whole carrier before any extension. -/
theorem timeCutoffProfile_nonneg {d : ℕ} (H : XV d → ℝ) (alpha r mu R : ℝ)
    (P : KineticPoint d) : 0 ≤ timeCutoffProfile H alpha r mu R P :=
  timeCutoffTheta_nonneg _

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

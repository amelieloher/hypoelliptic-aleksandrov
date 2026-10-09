module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.TerminalMomentBoundsActual
import Mathlib.Tactic

/-! # Real quadratic velocity moments of the actual full-space evolution

The unbounded-test truncation and Fatou proof is reused from the deterministic G3 lane.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov MeasureTheory
open scoped ENNReal

/-- The velocity displacement square is integrable for every realizing full-space kernel. -/
theorem velocity_moment_integrable {lam Lam : ℝ} (hlam : 0 < lam)
    (A : SmoothAutonomous lam Lam) (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (T : NNReal) (z : Z) :
    Integrable (fun w : Z => (w.2 - z.2) ^ 2) (kernelXV E T z) := by
  apply (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
    (Filter.Eventually.of_forall (fun w : Z => sq_nonneg (w.2 - z.2)))).mp
  exact ne_of_lt ((kernelXV_velocity_2_moment hlam A E hE z T).trans_lt
    ENNReal.ofReal_lt_top)

/-- The sharp quadratic moment bound in the source's real-integral normalization. -/
theorem velocity_moment_le {lam Lam : ℝ} (hlam : 0 < lam)
    (A : SmoothAutonomous lam Lam) (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (T : NNReal) (z : Z) :
    (∫ w, (w.2 - z.2) ^ 2 ∂kernelXV E T z) ≤ 2 * Lam * (T : ℝ) := by
  have h := kernelXV_velocity_2_moment hlam A E hE z T
  rw [← ofReal_integral_eq_lintegral_ofReal
    (velocity_moment_integrable hlam A E hE T z)
    (Filter.Eventually.of_forall (fun w : Z => sq_nonneg (w.2 - z.2)))] at h
  have hL : 0 ≤ Lam := (hlam.le.trans (A.bounds 0 0).1).trans (A.bounds 0 0).2
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

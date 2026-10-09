module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureJets
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic

/-! # Normal-factor test jets on the position axis -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- Multiplication by position has the literal product-rule jet. -/
theorem bellman_position_mul_fderiv (g : ℝ × ℝ → ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (q e : ℝ × ℝ) :
    fderiv ℝ (fun z => z.1 * g z) q e = q.1 * fderiv ℝ g q e + e.1 * g q := by
  have hd := (hasFDerivAt_fst (𝕜 := ℝ) (p := q)).smul
    (hg.differentiable (by simp) q).hasFDerivAt
  change HasFDerivAt (fun z => z.1 * g z) _ q at hd
  rw [hd.fderiv]
  change q.1 * fderiv ℝ g q e + e.1 * g q = _
  rfl

/-- The second velocity jet retains the normal position factor. -/
theorem bellman_position_mul_second_velocity (g : ℝ × ℝ → ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (q : ℝ × ℝ) :
    fderiv ℝ (fun z => fderiv ℝ (fun w => w.1 * g w) z (0, 1)) q (0, 1) =
      q.1 * fderiv ℝ (fun z => fderiv ℝ g z (0, 1)) q (0, 1) := by
  have he : (fun z => fderiv ℝ (fun w => w.1 * g w) z (0, 1)) =
      (fun z => z.1 * fderiv ℝ g z (0, 1)) := by
    funext z
    rw [bellman_position_mul_fderiv g hg z (0, 1)]
    simp only [zero_mul, add_zero]
  rw [he, bellman_position_mul_fderiv _ (bellman_contDiff_direction hg (0, 1))]
  simp only [zero_mul, add_zero]

end HypoellipticAleksandrov.KineticAleksandrov

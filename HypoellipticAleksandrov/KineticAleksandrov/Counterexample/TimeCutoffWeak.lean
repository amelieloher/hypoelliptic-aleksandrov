module

public import PDEFoundation.Sobolev.W1p.Composition
public import PDEFoundation.Sobolev.W1p.Algebra
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoff

/-!
# Weak first chain rule for a scalar cutoff of a difference

This uses the vendored representative-level Sobolev calculus. The hypotheses are
ordinary Sobolev regularity of arbitrary functions on an open bounded convex domain.
-/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory
open scoped ENNReal

/-- A bounded-derivative `C¹` cutoff of two Sobolev representatives has the chain-rule
weak gradient, including the derivative of the subtracted function. -/
theorem weakGradient_cutoff_sub {n : ℕ} {D : Set (PDE.Vec n)} {p : ℝ≥0∞}
    (hD : PDE.IsOpenBoundedConvexDomain D) (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u B : PDE.W1pFunction D p) (theta : ℝ → ℝ) (htheta : ContDiff ℝ 1 theta)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ s, |deriv theta s| ≤ M) :
    PDE.HasWeakGradientOn D
      (fun x => theta (u.toFun x - B.toFun x))
      (fun x i => deriv theta (u.toFun x - B.toFun x) * (u.grad x i - B.grad x i)) := by
  let : Fact (1 ≤ p) := ⟨hp⟩
  simpa only [PDE.W1pFunction.sub_toFun, PDE.W1pFunction.sub_grad, Pi.sub_apply] using!
    PDE.W1pFunction.hasWeakGradient_comp_contDiff_of_deriv_bounded
      hD hp hpTop (u - B) htheta hM hbound

/-- The chain rule written directly for functions and their chosen weak derivatives. -/
theorem weakGradient_cutoff_sub_of_memLp {n : ℕ} {D : Set (PDE.Vec n)} {p : ℝ≥0∞}
    (hD : PDE.IsOpenBoundedConvexDomain D) (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u B : PDE.Vec n → ℝ) (Du DB : PDE.Vec n → PDE.Vec n)
    (hu : PDE.MemLpOn D p u) (hB : PDE.MemLpOn D p B)
    (hDu : PDE.GradMemLpOn D p Du) (hDB : PDE.GradMemLpOn D p DB)
    (hwu : PDE.HasWeakGradientOn D u Du) (hwB : PDE.HasWeakGradientOn D B DB)
    (theta : ℝ → ℝ) (htheta : ContDiff ℝ 1 theta)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ s, |deriv theta s| ≤ M) :
    PDE.HasWeakGradientOn D (fun x => theta (u x - B x))
      (fun x i => deriv theta (u x - B x) * (Du x i - DB x i)) := by
  exact weakGradient_cutoff_sub hD hp hpTop
    ⟨u, Du, hu, hDu, hwu⟩ ⟨B, DB, hB, hDB, hwB⟩ theta htheta M hM hbound

/-- The fixed Appendix C cutoff has multiplier bound one in the weak chain rule. -/
theorem weakGradient_timeCutoff_sub {n : ℕ} {D : Set (PDE.Vec n)} {p : ℝ≥0∞}
    (hD : PDE.IsOpenBoundedConvexDomain D) (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u B : PDE.W1pFunction D p) :
    PDE.HasWeakGradientOn D
      (fun x => timeCutoffTheta (u.toFun x - B.toFun x))
      (fun x i => deriv timeCutoffTheta (u.toFun x - B.toFun x) *
        (u.grad x i - B.grad x i)) := by
  apply weakGradient_cutoff_sub hD hp hpTop u B timeCutoffTheta
    (contDiff_timeCutoffTheta.of_le (by simp)) 1 zero_le_one
  intro s
  rw [abs_of_nonneg (timeCutoffTheta_deriv_bounds s).1]
  exact (timeCutoffTheta_deriv_bounds s).2

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

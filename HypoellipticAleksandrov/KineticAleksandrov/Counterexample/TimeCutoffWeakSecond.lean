module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoffWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoffWeakProduct
public import PDEFoundation.Sobolev.W1p.Smooth
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.Ring

/-!
# The second weak chain rule for a scalar cutoff

Only the particular weak derivative of the first jet is required. The first jet need
not have weak derivatives in the other directions, which is relevant for kinetic PDEs.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory
open scoped ENNReal

/-- The second weak chain rule for a `C²` scalar cutoff of a Sobolev difference.
The prescribed mixed second derivative is genuine Sobolev regularity of that difference. -/
theorem weakSecond_cutoff_sub {d : ℕ} {D : Set (PDE.Vec d)}
    (hD : PDE.IsOpenBoundedConvexDomain D) (u B : PDE.W1pFunction D 2)
    (i k : Fin d) (hess : PDE.Vec d → ℝ) (hhess : PDE.MemLpOn D 2 hess)
    (hweak : PDE.HasWeakPartialDerivOn D i (fun x => u.grad x k - B.grad x k) hess)
    (theta : ℝ → ℝ) (htheta : ContDiff ℝ 2 theta)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ s, |deriv (deriv theta) s| ≤ M) :
    PDE.HasWeakPartialDerivOn D i
      (fun x => deriv theta (u.toFun x - B.toFun x) * (u.grad x k - B.grad x k))
      (fun x => deriv theta (u.toFun x - B.toFun x) * hess x +
        deriv (deriv theta) (u.toFun x - B.toFun x) *
          (u.grad x i - B.grad x i) * (u.grad x k - B.grad x k)) := by
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  have hd : ContDiff ℝ 1 (deriv theta) := htheta.deriv'
  let a := (u - B).compContDiffOfDerivBounded hD (by norm_num) (by norm_num)
    hd hM hbound
  have hb : PDE.MemLpOn D 2 (fun x => u.grad x k - B.grad x k) :=
    (u.gradMemLp k).sub (B.gradMemLp k)
  have he := weakPartial_product_sobolev hD a i _ hess hb hhess hweak
  convert he using 1
  · funext x
    rfl
  · funext x
    dsimp only [a, PDE.W1pFunction.compContDiffOfDerivBounded,
      PDE.W1pFunction.sub_toFun, PDE.W1pFunction.sub_grad, Pi.sub_apply]
    ring

/-- The second weak chain rule with a smooth subtracted function. Its Sobolev bounds
and weak derivatives are constructed internally on the bounded convex domain. -/
theorem weakSecond_cutoff_sub_smooth {d : ℕ} {D : Set (PDE.Vec d)}
    (hD : PDE.IsOpenBoundedConvexDomain D) (u : PDE.W1pFunction D 2)
    (B : PDE.Vec d → ℝ) (hB : ContDiff ℝ (⊤ : ℕ∞) B) (i k : Fin d)
    (hess : PDE.Vec d → ℝ) (hhess : PDE.MemLpOn D 2 hess)
    (hweak : PDE.HasWeakPartialDerivOn D i (fun x => u.grad x k) hess)
    (theta : ℝ → ℝ) (htheta : ContDiff ℝ 2 theta)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ s, |deriv (deriv theta) s| ≤ M) :
    PDE.HasWeakPartialDerivOn D i
      (fun x => deriv theta (u.toFun x - B x) *
        (u.grad x k - PDE.classicalGradient B x k))
      (fun x => deriv theta (u.toFun x - B x) *
        (hess x - PDE.classicalGradient (fun y => PDE.classicalGradient B y k) x i) +
        deriv (deriv theta) (u.toFun x - B x) *
          (u.grad x i - PDE.classicalGradient B x i) *
          (u.grad x k - PDE.classicalGradient B x k)) := by
  have : IsFiniteMeasure (PDE.volumeOn D) :=
    hD.isBoundedDomain.isFiniteMeasure_volumeOn
  let b := PDE.W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain (p := 2) hD
    (hB.of_le (by simp))
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun x => PDE.classicalGradient B x k) := by
    exact (hB.contDiff_fderiv_apply (by simp)).comp
      (contDiff_id.prodMk contDiff_const)
  let bg := PDE.W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain (p := 2) hD
    (hg.of_le (by simp))
  have hdiff : PDE.HasWeakPartialDerivOn D i
      (fun x => u.grad x k - b.grad x k)
      (fun x => hess x - bg.grad x i) := by
    simpa only [Pi.sub_apply] using!
      hweak.sub (bg.hasWeakPartialDerivOn i)
        ((u.gradMemLp k).integrable (by norm_num)).locallyIntegrable
        (bg.memLp.integrable (by norm_num)).locallyIntegrable
        (hhess.integrable (by norm_num)).locallyIntegrable
        ((bg.gradMemLp i).integrable (by norm_num)).locallyIntegrable
  have hmem : PDE.MemLpOn D 2 (fun x => hess x - bg.grad x i) :=
    hhess.sub (bg.gradMemLp i)
  simpa only [b, bg, PDE.W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain,
    PDE.W1pFunction.ofContDiffOnIsSobolevRegularDomain] using!
    weakSecond_cutoff_sub hD u b i k _ hmem hdiff theta htheta M hM hbound

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

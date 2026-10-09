module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2CutoffRadial
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Fixed-annulus coordinates for the cutoff Hessian

The shift and regularization shrink with the inverse cutoff radius. The additive
constant is kept as an independent parameter so that all velocity jets remain smooth.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- The cutoff interpolation on a fixed annulus, with independent constant and scale. -/
def rescaledCutoff {d : ℕ} (alpha sigma s t : ℝ) (e z : PDE.Vec d) : ℝ :=
  radialProfile alpha z + radialCutoff 1 z *
    (s + Real.rpow (seedBase (t * sigma) z (t • e)) (alpha / 2) - radialProfile alpha z)

/-- The zero-parameter interpolation is exactly the radial profile. -/
theorem rescaledCutoff_zero {d : ℕ} (alpha sigma : ℝ) (e z : PDE.Vec d) :
    rescaledCutoff alpha sigma 0 0 e z = radialProfile alpha z := by
  simp [rescaledCutoff, seedBase, radialProfile]

/-- The fixed-annulus family is smooth wherever both radial power bases are positive. -/
theorem contDiffAt_rescaledCutoff {d : ℕ} (alpha sigma : ℝ)
    (p : (ℝ × ℝ × PDE.Vec d) × PDE.Vec d) (hz : p.2 ≠ 0)
    (hb : seedBase (p.1.2.1 * sigma) p.2 (p.1.2.1 • p.1.2.2) ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q : (ℝ × ℝ × PDE.Vec d) × PDE.Vec d =>
        rescaledCutoff alpha sigma q.1.1 q.1.2.1 q.1.2.2 q.2) p := by
  have hr : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q : (ℝ × ℝ × PDE.Vec d) × PDE.Vec d => radialProfile alpha q.2) p :=
    (PDE.contDiff_vecNormSq.comp contDiff_snd).contDiffAt.rpow_const_of_ne
      (PDE.vecNormSq_eq_zero_iff.not.mpr hz)
  have hbase : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : (ℝ × ℝ × PDE.Vec d) × PDE.Vec d =>
        seedBase (q.1.2.1 * sigma) q.2 (q.1.2.1 • q.1.2.2)) := by
    unfold seedBase PDE.vecNormSq PDE.vecDot
    fun_prop
  have hs : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q : (ℝ × ℝ × PDE.Vec d) × PDE.Vec d => q.1.1) p := by fun_prop
  exact hr.add (((contDiff_radialCutoff 1).comp contDiff_snd).contDiffAt.mul
    ((hs.add (hbase.contDiffAt.rpow_const_of_ne hb)).sub hr))

/-- Partial velocity derivatives of the fixed-annulus family are smooth jointly. -/
theorem contDiffAt_rescaledCutoff_first {d : ℕ} (alpha sigma : ℝ)
    (p : (ℝ × ℝ × PDE.Vec d) × PDE.Vec d) (hz : p.2 ≠ 0)
    (hb : seedBase (p.1.2.1 * sigma) p.2 (p.1.2.1 • p.1.2.2) ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q : (ℝ × ℝ × PDE.Vec d) × PDE.Vec d =>
        fderiv ℝ (rescaledCutoff alpha sigma q.1.1 q.1.2.1 q.1.2.2) q.2) p := by
  have hf := contDiffAt_rescaledCutoff alpha sigma p hz hb
  have hc : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q : ((ℝ × ℝ × PDE.Vec d) × PDE.Vec d) × PDE.Vec d => (q.1.1, q.2))
      (p, p.2) := by fun_prop
  exact (hf.comp (p, p.2) hc).fderiv contDiffAt_snd (by simp)

/-- The velocity Hessian is continuous jointly at every regular parameter point. -/
theorem continuousAt_rescaledCutoff_hessian {d : ℕ} (alpha sigma : ℝ)
    (p : (ℝ × ℝ × PDE.Vec d) × PDE.Vec d) (hz : p.2 ≠ 0)
    (hb : seedBase (p.1.2.1 * sigma) p.2 (p.1.2.1 • p.1.2.2) ≠ 0)
    (w u : PDE.Vec d) :
    ContinuousAt
      (fun q : (ℝ × ℝ × PDE.Vec d) × PDE.Vec d =>
        fderiv ℝ (fun z =>
          fderiv ℝ (rescaledCutoff alpha sigma q.1.1 q.1.2.1 q.1.2.2) z w) q.2 u) p := by
  have hf := contDiffAt_rescaledCutoff_first alpha sigma p hz hb
  have heval : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q : (ℝ × ℝ × PDE.Vec d) × PDE.Vec d =>
        fderiv ℝ (rescaledCutoff alpha sigma q.1.1 q.1.2.1 q.1.2.2) q.2 w) p :=
    hf.clm_apply contDiffAt_const
  have hc : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun q : ((ℝ × ℝ × PDE.Vec d) × PDE.Vec d) × PDE.Vec d => (q.1.1, q.2))
      (p, p.2) := by fun_prop
  exact (((heval.comp (p, p.2) hc).fderiv (m := 0) contDiffAt_snd (by simp)).clm_apply
    contDiffAt_const).continuousAt

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

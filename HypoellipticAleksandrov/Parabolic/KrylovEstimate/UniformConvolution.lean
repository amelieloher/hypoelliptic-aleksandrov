module

public import HypoellipticAleksandrov.Parabolic.WeakJetMollifier
public import HypoellipticAleksandrov.Parabolic.ParabolicMollifierKernel
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Topology.UniformSpace.HeineCantor

/-! # Uniform approximation of compactly supported continuous representatives -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.KrylovEstimate
open Filter MeasureTheory
open scoped Topology Convolution

/-- Normalized mollification approximates a compactly supported continuous function uniformly. -/
theorem eventually_uniform_parabolicConvolution_close
    {N : ℕ} (f : TimeVelocity N → ℝ) (hf : Continuous f)
    (hc : HasCompactSupport f) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ z,
      |parabolicConvolution f (parabolicMollifier N n) z - f z| ≤ ε := by
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuous_iff.mp
    (hc.uniformContinuous_of_continuous hf) ε hε
  have hn := tendsto_parabolicMollifierScale_zero.eventually (gt_mem_nhds hδ)
  filter_upwards [hn] with n hn z
  have he := (parabolicMollifierBump N n).dist_normed_convolution_le
    hf.aestronglyMeasurable (μ := volume) (x₀ := z) (ε := ε) (by
      intro x hx
      exact (hd (lt_trans hx hn)).le)
  change dist ((parabolicMollifier N n ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
    volume] f) z) (f z) ≤ ε at he
  have heq : (parabolicMollifier N n ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
      volume] f) z = parabolicConvolution f (parabolicMollifier N n) z := by
    rw [convolution_lsmul_swap]
    unfold parabolicConvolution convolution
    congr 1
    funext x
    change parabolicMollifier N n (z - x) * f x = f x * parabolicMollifier N n (z - x)
    exact mul_comm _ _
  simpa only [heq, Real.dist_eq] using he

end HypoellipticAleksandrov.Parabolic.KrylovEstimate

module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitFourier
public import HypoellipticAleksandrov.KineticAleksandrov.Reconstruction.FiberDisintegration
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-! # Disintegration of exit position over its actual time--velocity marginal

The marginal is arbitrary and can be singular. Swapping the coordinates permits the
standard finite-measure disintegration, with no absolute-continuity premise on exit data.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory ProbabilityTheory Parabolic Reconstruction
open scoped ENNReal

variable {d : ℕ}

/-- The actual time--velocity marginal of an exit-coordinate measure. -/
def exitMarginal (ν : Measure (PDE.Vec d × TimeVelocity d)) : Measure (TimeVelocity d) :=
  ν.map Prod.snd

/-- Position conditioned on exit time and velocity, using the standard Borel kernel. -/
def exitPositionKernel (ν : Measure (PDE.Vec d × TimeVelocity d)) [IsFiniteMeasure ν] :
    Kernel (TimeVelocity d) (PDE.Vec d) :=
  (ν.map Prod.swap).condKernel

/-- The conditional position kernel is Markov, including at exceptional exit data. -/
instance exitPositionKernel_isMarkov (ν : Measure (PDE.Vec d × TimeVelocity d))
    [IsFiniteMeasure ν] : IsMarkovKernel (exitPositionKernel ν) := by
  unfold exitPositionKernel
  infer_instance

/-- Projection preserves finiteness without imposing a density on exit time or velocity. -/
instance exitMarginal_isFinite (ν : Measure (PDE.Vec d × TimeVelocity d))
    [IsFiniteMeasure ν] : IsFiniteMeasure (exitMarginal ν) := by
  unfold exitMarginal
  infer_instance

/-- Disintegration reconstructs the full exit measure in the swapped coordinate order. -/
theorem exitPositionKernel_disintegrate (ν : Measure (PDE.Vec d × TimeVelocity d))
    [IsFiniteMeasure ν] :
    exitMarginal ν ⊗ₘ exitPositionKernel ν = ν.map Prod.swap := by
  simpa only [exitMarginal, exitPositionKernel, Measure.fst_map_swap, Measure.snd] using
    (Measure.disintegrate (ν.map Prod.swap) (ν.map Prod.swap).condKernel)

/-- Jointly measurable Fourier representatives from the conditional position kernel. -/
def exitFourierRep (ν : Measure (PDE.Vec d × TimeVelocity d)) [IsFiniteMeasure ν]
    (ξ : PDE.Vec d) (z : TimeVelocity d) : ℂ :=
  fiberFourier (exitPositionKernel ν) ξ z

/-- The conditional Fourier representatives are jointly measurable. -/
theorem measurable_exitFourierRep (ν : Measure (PDE.Vec d × TimeVelocity d))
    [IsFiniteMeasure ν] :
    Measurable (fun p : PDE.Vec d × TimeVelocity d => exitFourierRep ν p.1 p.2) :=
  measurable_fiberFourier (exitPositionKernel ν)

/-- Each conditional characteristic function is continuous in frequency. -/
theorem continuous_exitFourierRep (ν : Measure (PDE.Vec d × TimeVelocity d))
    [IsFiniteMeasure ν] (z : TimeVelocity d) :
    Continuous (fun ξ => exitFourierRep ν ξ z) :=
  continuous_fiberFourier (exitPositionKernel ν) z

/-- Conditional characteristic functions have modulus at most one. -/
theorem norm_exitFourierRep_le_one (ν : Measure (PDE.Vec d × TimeVelocity d))
    [IsFiniteMeasure ν] (ξ : PDE.Vec d) (z : TimeVelocity d) :
    ‖exitFourierRep ν ξ z‖ ≤ 1 :=
  norm_fiberFourier_le (exitPositionKernel ν) ξ z

/-- The Fourier representative is integrable over the actual finite marginal. -/
theorem integrable_exitFourierRep (ν : Measure (PDE.Vec d × TimeVelocity d))
    [IsFiniteMeasure ν] (ξ : PDE.Vec d) :
    Integrable (exitFourierRep ν ξ) (exitMarginal ν) :=
  Integrable.of_bound
    ((measurable_exitFourierRep ν).comp measurable_prodMk_left).aestronglyMeasurable 1
    (Filter.Eventually.of_forall (norm_exitFourierRep_le_one ν ξ))

/-- Integration of the disintegrated representative equals the actual Fourier exit measure. -/
theorem setIntegral_exitFourierRep (ν : Measure (PDE.Vec d × TimeVelocity d))
    [IsFiniteMeasure ν] (ξ : PDE.Vec d) {E : Set (TimeVelocity d)} (hE : MeasurableSet E) :
    (∫ z in E, exitFourierRep ν ξ z ∂exitMarginal ν) = exitFourier ν ξ E := by
  have hd := exitPositionKernel_disintegrate ν
  have hfin : IsFiniteMeasure (exitMarginal ν ⊗ₘ exitPositionKernel ν) :=
    hd.symm ▸ inferInstance
  have hfin' : IsFiniteMeasure
      ((exitMarginal ν).withDensity (fun _ => (1 : ℝ≥0∞)) ⊗ₘ exitPositionKernel ν) := by
    simpa only [withDensity_const, one_smul] using hfin
  have htop : ∀ᵐ _z ∂exitMarginal ν, (1 : ℝ≥0∞) < ⊤ := by simp
  have h := setIntegral_fiberDensity (m := exitMarginal ν) (g := fun _ => 1)
    measurable_const htop
    (exitPositionKernel ν) ξ hE
  simp only [withDensity_const, one_smul, fiberDensity, ENNReal.toReal_one, Complex.ofReal_one,
    one_mul] at h
  change (∫ z in E, exitFourierRep ν ξ z ∂exitMarginal ν) = _ at h
  rw [hd] at h
  rw [h, exitFourier_apply ν ξ E hE, ← integral_indicator (hE.prod MeasurableSet.univ),
    ← integral_indicator (hE.preimage measurable_snd)]
  rw [integral_map measurable_swap.aemeasurable]
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun p => by
      by_cases hp : p.2 ∈ E <;>
        simp [hp, exitPhase, mul_comm])
  · have hc : Continuous (fun p : TimeVelocity d × PDE.Vec d =>
        Complex.exp (-((PDE.vecDot ξ p.2 : ℝ) * Complex.I))) := by
      unfold PDE.vecDot
      fun_prop
    exact (hc.measurable.indicator (hE.prod MeasurableSet.univ)).aestronglyMeasurable

/-- The disintegrated representative is the Radon--Nikodym density of exit Fourier data. -/
theorem exitFourier_eq_withDensity (ν : Measure (PDE.Vec d × TimeVelocity d))
    [IsFiniteMeasure ν] (ξ : PDE.Vec d) :
    exitFourier ν ξ = (exitMarginal ν).withDensityᵥ (exitFourierRep ν ξ) := by
  ext E hE
  rw [withDensityᵥ_apply (integrable_exitFourierRep ν ξ) hE,
    setIntegral_exitFourierRep ν ξ hE]

end HypoellipticAleksandrov.KineticAleksandrov.LocalA

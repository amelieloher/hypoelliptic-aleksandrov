module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitDisintegration
public import Mathlib.MeasureTheory.Function.L1Space.AEEqFun
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Topology.Sequences

/-! # Fourier exit data in the complete space over the actual exit marginal -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Filter Topology Parabolic
open scoped ENNReal

variable {d : ℕ}

/-- Fourier exit data as an element of the complete `L¹` space of its marginal. -/
def exitL1Fourier (ν : Measure (PDE.Vec d × TimeVelocity d)) [IsFiniteMeasure ν]
    (ξ : PDE.Vec d) : Lp ℂ 1 (exitMarginal ν) :=
  (integrable_exitFourierRep ν ξ).toL1 (exitFourierRep ν ξ)

/-- The `L¹` Fourier element has the jointly measurable conditional representative. -/
theorem coe_exitL1Fourier (ν : Measure (PDE.Vec d × TimeVelocity d)) [IsFiniteMeasure ν]
    (ξ : PDE.Vec d) :
    (exitL1Fourier ν ξ : TimeVelocity d → ℂ) =ᵐ[exitMarginal ν] exitFourierRep ν ξ :=
  Integrable.coeFn_toL1 (integrable_exitFourierRep ν ξ)

/-- Total variation of Fourier exit data equals the norm in the complete `L¹` space. -/
theorem norm_exitL1Fourier (ν : Measure (PDE.Vec d × TimeVelocity d)) [IsFiniteMeasure ν]
    (ξ : PDE.Vec d) :
    ‖exitL1Fourier ν ξ‖ = ((exitFourier ν ξ).variation univ).toReal := by
  rw [exitFourier_eq_withDensity ν ξ,
    Measure.variation_withDensityᵥ (integrable_exitFourierRep ν ξ),
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact Integrable.norm_toL1_eq_lintegral_enorm _ _

/-- Frequency continuity holds in `L¹`, without a Banach-space structure on measures. -/
theorem continuous_exitL1Fourier (ν : Measure (PDE.Vec d × TimeVelocity d))
    [IsFiniteMeasure ν] : Continuous (exitL1Fourier ν) := by
  apply continuous_iff_seqContinuous.mpr
  intro ξs ξ hξs
  change Tendsto
    (fun n => (memLp_one_iff_integrable.mpr (integrable_exitFourierRep ν (ξs n))).toLp
      (exitFourierRep ν (ξs n))) atTop
    (𝓝 ((memLp_one_iff_integrable.mpr (integrable_exitFourierRep ν ξ)).toLp
      (exitFourierRep ν ξ)))
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'']
  have ht := tendsto_lintegral_norm_of_dominated_convergence
    (μ := exitMarginal ν) (F := fun n => exitFourierRep ν (ξs n))
    (f := exitFourierRep ν ξ) (bound := fun _ => (1 : ℝ))
    (fun n => (integrable_exitFourierRep ν (ξs n)).aestronglyMeasurable)
    (integrable_const (1 : ℝ)).hasFiniteIntegral
    (fun n => Eventually.of_forall (norm_exitFourierRep_le_one ν (ξs n)))
    (Eventually.of_forall (fun z => (continuous_exitFourierRep ν z).tendsto ξ |>.comp hξs))
  convert ht using 1
  funext n
  rw [eLpNorm_one_eq_lintegral_enorm
    ((integrable_exitFourierRep ν (ξs n)).sub
      (integrable_exitFourierRep ν ξ)).aestronglyMeasurable]
  apply lintegral_congr
  intro z
  exact (ofReal_norm (exitFourierRep ν (ξs n) z - exitFourierRep ν ξ z)).symm

end HypoellipticAleksandrov.KineticAleksandrov.LocalA

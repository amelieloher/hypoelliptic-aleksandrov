module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.GaussianKernelCalculus
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Comap
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # Literal time-integrated Kolmogorov measure

The time and plane measures are pullbacks along the open-subtype embeddings. No value of
an integrand at nonpositive time and no assumed fundamental-solution existence is used.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- Lebesgue measure restricted to positive time, on its actual subtype. -/
def bellmanPositiveTimeVolume : Measure BellmanPositiveTime :=
  Measure.comap Subtype.val (volume.restrict (Ioi (0 : ℝ)))

/-- The positive-time measure is finite on compact subsets. -/
instance bellmanPositiveTimeVolume_finiteOnCompacts :
    IsFiniteMeasureOnCompacts bellmanPositiveTimeVolume := by
  exact IsFiniteMeasureOnCompacts.comap' _ continuous_subtype_val
    (MeasurableEmbedding.subtype_coe measurableSet_Ioi)

/-- The positive-time measure is sigma finite. -/
instance bellmanPositiveTimeVolume_sigmaFinite : SigmaFinite bellmanPositiveTimeVolume := by
  let : LocallyCompactSpace BellmanPositiveTime := isOpen_Ioi.locallyCompactSpace
  infer_instance

/-- Lebesgue measure on the actual punctured position-velocity plane. -/
def bellmanPuncturedVolume : Measure BellmanPuncturedPlane :=
  Measure.comap Subtype.val (volume : Measure (ℝ × ℝ))

/-- The source's nonnegative time-integrated Gaussian density, without a finiteness premise. -/
def bellmanFundamentalDensity (q : BellmanPuncturedPlane) : ENNReal :=
  ∫⁻ t, ENNReal.ofReal (bellmanGaussianKernel t q.val) ∂bellmanPositiveTimeVolume

/-- The literal constant-diffusion fundamental measure on the punctured plane. -/
def bellmanFundamentalMeasure : Measure BellmanPuncturedPlane :=
  bellmanPuncturedVolume.withDensity bellmanFundamentalDensity

/-- Joint continuity of the kernel in strictly positive time and spatial position. -/
theorem continuous_bellmanGaussianKernel :
    Continuous (fun w : BellmanPositiveTime × (ℝ × ℝ) =>
      bellmanGaussianKernel w.1 w.2) := by
  have ht : ∀ w : BellmanPositiveTime × (ℝ × ℝ), w.1.val ≠ 0 :=
    fun w => ne_of_gt w.1.property
  unfold bellmanGaussianKernel bellmanGaussianExponent
  fun_prop (disch := aesop)

/-- Measurability of the time-integrated density follows from Tonelli measurability. -/
theorem measurable_bellmanFundamentalDensity : Measurable bellmanFundamentalDensity := by
  have h : Measurable (fun w : BellmanPuncturedPlane × BellmanPositiveTime =>
      ENNReal.ofReal (bellmanGaussianKernel w.2 w.1.val)) := by
    apply ENNReal.measurable_ofReal.comp
    exact continuous_bellmanGaussianKernel.measurable.comp
      (measurable_snd.prodMk (measurable_subtype_coe.comp measurable_fst))
  exact h.lintegral_prod_right'

end HypoellipticAleksandrov.KineticAleksandrov

module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsLineWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsParametric
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! # Literal first and second parameter jets of position convolution -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Set MeasureTheory Filter
open scoped Topology

/-- The scalar position projection used by the parameter jets. -/
def barrierPositionProjection : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ

/-- The scalar velocity projection used by the parameter jets. -/
def barrierVelocityProjection : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ

/-- The actual position convolution integrand, with the integration variable fixed. -/
def barrierConvolutionIntegrand (κ : ℝ → ℝ) (phi : (ℝ × ℝ) → ℝ)
    (q : ℝ × ℝ) (Y : ℝ) : ℝ := κ (q.1 - Y) * bellmanOriginExtension phi (Y, q.2)

/-- The first parameter jet of the actual convolution integrand. -/
def barrierConvolutionJet (κ : ℝ → ℝ) (phi : (ℝ × ℝ) → ℝ)
    (q : ℝ × ℝ) (Y : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  (deriv κ (q.1 - Y) * bellmanOriginExtension phi (Y, q.2)) • barrierPositionProjection +
    (κ (q.1 - Y) * bellmanDv phi (Y, q.2)) • barrierVelocityProjection

/-- The second parameter jet, displaying only position kernel and velocity source derivatives. -/
def barrierConvolutionSecondJet (κ : ℝ → ℝ) (phi : (ℝ × ℝ) → ℝ)
    (q : ℝ × ℝ) (Y : ℝ) : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ) :=
  ((deriv (deriv κ) (q.1 - Y) * bellmanOriginExtension phi (Y, q.2)) •
      barrierPositionProjection + (deriv κ (q.1 - Y) * bellmanDv phi (Y, q.2)) •
      barrierVelocityProjection).smulRight barrierPositionProjection +
    ((deriv κ (q.1 - Y) * bellmanDv phi (Y, q.2)) • barrierPositionProjection +
      (κ (q.1 - Y) * bellmanDvv phi (Y, q.2)) • barrierVelocityProjection).smulRight
      barrierVelocityProjection

/-- The extension's velocity slice is differentiable at every nonzero position. -/
theorem barrier_slice_hasFDerivAt {alpha : ℝ} {phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha phi) (q : ℝ × ℝ) (Y : ℝ) (hY : Y ≠ 0) :
    HasFDerivAt (fun p : ℝ × ℝ => bellmanOriginExtension phi (Y, p.2))
      (bellmanDv phi (Y, q.2) • barrierVelocityProjection) q := by
  have hq : (Y, q.2) ∈ bellmanPuncturedSet := fun he => hY (congrArg Prod.fst he)
  have hd := (h.1.contDiffAt (bellmanPuncturedSet_isOpen.mem_nhds hq)).differentiableAt
    (by norm_num)
  have hslice := (bellman_hasDerivAt_second hd).congr_of_eventuallyEq
    ((barrierExtension_eventuallyEq phi hq).comp_tendsto
      ((continuous_const.prodMk continuous_id).tendsto q.2))
  exact hslice.comp_hasFDerivAt q hasFDerivAt_snd

/-- The first velocity jet has its actual second slice derivative off the position origin. -/
theorem barrier_dv_slice_hasFDerivAt {alpha : ℝ} {phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha phi) (q : ℝ × ℝ) (Y : ℝ) (hY : Y ≠ 0) :
    HasFDerivAt (fun p : ℝ × ℝ => bellmanDv phi (Y, p.2))
      (bellmanDvv phi (Y, q.2) • barrierVelocityProjection) q := by
  have hq : (Y, q.2) ∈ bellmanPuncturedSet := fun he => hY (congrArg Prod.fst he)
  have hd := ((h.directional_contDiffOn (0, 1)).contDiffAt
    (bellmanPuncturedSet_isOpen.mem_nhds hq)).differentiableAt (by norm_num)
  exact (bellman_hasDerivAt_second hd).comp_hasFDerivAt q hasFDerivAt_snd

/-- The displayed first jet is the actual Fréchet derivative of the integrand. -/
theorem barrierConvolutionIntegrand_hasFDerivAt {alpha : ℝ} {phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha phi) (κ : ℝ → ℝ) (hκ : ContDiff ℝ 2 κ)
    (q : ℝ × ℝ) (Y : ℝ) (hY : Y ≠ 0) :
    HasFDerivAt (fun p => barrierConvolutionIntegrand κ phi p Y)
      (barrierConvolutionJet κ phi q Y) q := by
  have hk := ((hκ.differentiable (by norm_num) (q.1 - Y)).hasDerivAt).comp_hasFDerivAt q
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := q)).sub_const Y)
  have hh := hk.mul (barrier_slice_hasFDerivAt h q Y hY)
  convert hh using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro w
    simp [barrierConvolutionJet, barrierPositionProjection, barrierVelocityProjection]
    ring

/-- The displayed second jet is the actual derivative of the displayed first jet. -/
theorem barrierConvolutionJet_hasFDerivAt {alpha : ℝ} {phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha phi) (κ : ℝ → ℝ) (hκ : ContDiff ℝ 2 κ)
    (q : ℝ × ℝ) (Y : ℝ) (hY : Y ≠ 0) :
    HasFDerivAt (fun p => barrierConvolutionJet κ phi p Y)
      (barrierConvolutionSecondJet κ phi q Y) q := by
  have hk := ((hκ.differentiable (by norm_num) (q.1 - Y)).hasDerivAt).comp_hasFDerivAt q
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := q)).sub_const Y)
  have hk' := ((hκ.differentiable_deriv_two (q.1 - Y)).hasDerivAt).comp_hasFDerivAt q
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := q)).sub_const Y)
  have hp := barrier_slice_hasFDerivAt h q Y hY
  have hp' := barrier_dv_slice_hasFDerivAt h q Y hY
  have hh := ((hk'.mul hp).smul_const barrierPositionProjection).add
    ((hk.mul hp').smul_const barrierVelocityProjection)
  convert hh using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro w
    apply ContinuousLinearMap.ext
    intro u
    simp [barrierConvolutionSecondJet, barrierPositionProjection, barrierVelocityProjection]
    ring

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

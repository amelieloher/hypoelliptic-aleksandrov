module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ScalarAdapters
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import PDEFoundation.Measure.OneDimensionalCoordinate

/-! # Autonomous scalar mollification in position and velocity

Pointwise ellipticity is preserved without an exceptional-set replacement.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory Filter ContinuousLinearMap
open scoped Convolution Topology

/-- Shrinking normalized scalar bumps with fixed inner-to-outer radius ratio. -/
def scalarBorelBump (j : ℕ) : ContDiffBump (0 : ℝ × ℝ) :=
  ⟨(1 / ((j : ℝ) + 1)) / 2, 1 / ((j : ℝ) + 1), by positivity,
    half_lt_self (by positivity)⟩

/-- Mollification in the two physical scalar coordinates. -/
def scalarBorelConvolution (φ : ContDiffBump (0 : ℝ × ℝ))
    (a : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun x v => (φ.normed volume ⋆[lsmul ℝ ℝ, volume] Function.uncurry a) (x, v)

/-- Bounded Borel scalar coefficients are locally integrable. -/
theorem scalar_borel_locallyIntegrable {lam Lam : ℝ} (hlam : 0 < lam)
    (a : ℝ → ℝ → ℝ) (ha : Measurable (Function.uncurry a))
    (hb : ∀ x v, lam ≤ a x v ∧ a x v ≤ Lam) :
    LocallyIntegrable (Function.uncurry a) volume := by
  apply (locallyIntegrable_const Lam).mono ha.aestronglyMeasurable
  filter_upwards with z
  dsimp only [Function.uncurry]
  rw [Real.norm_of_nonneg (hlam.le.trans (hb z.1 z.2).1),
    Real.norm_of_nonneg (hlam.le.trans (hb z.1 z.2).1 |>.trans (hb z.1 z.2).2)]
  exact (hb z.1 z.2).2

/-- Scalar convolution is smooth and retains the original pointwise interval. -/
theorem scalarBorelConvolution_spec {lam Lam : ℝ} (hlam : 0 < lam)
    (a : ℝ → ℝ → ℝ) (ha : Measurable (Function.uncurry a))
    (hb : ∀ x v, lam ≤ a x v ∧ a x v ≤ Lam)
    (φ : ContDiffBump (0 : ℝ × ℝ)) :
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (scalarBorelConvolution φ a)) ∧
      ∀ x v, lam ≤ scalarBorelConvolution φ a x v ∧
        scalarBorelConvolution φ a x v ≤ Lam := by
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure volume volume
  have hloc := scalar_borel_locallyIntegrable hlam a ha hb
  refine ⟨φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
    φ.contDiff_normed hloc, ?_⟩
  intro x v
  have hi := φ.hasCompactSupport_normed.convolutionExists_left
    (μ := volume) (lsmul ℝ ℝ) (φ.continuous_normed (μ := volume)) hloc (x, v)
  have hl := integral_mono ((φ.integrable_normed (μ := volume)).smul_const lam) hi
    (fun y => mul_le_mul_of_nonneg_left (hb ((x, v) - y).1 ((x, v) - y).2).1
      (φ.nonneg_normed y))
  have hu := integral_mono hi ((φ.integrable_normed (μ := volume)).smul_const Lam)
    (fun y => mul_le_mul_of_nonneg_left (hb ((x, v) - y).1 ((x, v) - y).2).2
      (φ.nonneg_normed y))
  simpa only [scalarBorelConvolution, convolution, lsmul_apply, smul_eq_mul,
    integral_mul_const, φ.integral_normed, one_mul] using And.intro hl hu

/-- Smooth autonomous approximations preserve ellipticity and converge almost everywhere. -/
theorem scalar_borel_coefficient_approximation {lam Lam : ℝ} (hlam : 0 < lam)
    (a : ℝ → ℝ → ℝ) (ha : Measurable (Function.uncurry a))
    (hb : ∀ x v, lam ≤ a x v ∧ a x v ≤ Lam) :
    ∃ C : ℕ → ℝ → ℝ → ℝ,
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (C j)) ∧
        ∀ x v, lam ≤ C j x v ∧ C j x v ≤ Lam) ∧
      ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)),
        Tendsto (fun j => C j z.1 z.2) atTop (𝓝 (a z.1 z.2)) := by
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure volume volume
  let C := fun j => scalarBorelConvolution (scalarBorelBump j) a
  refine ⟨C, fun j => scalarBorelConvolution_spec hlam a ha hb _, ?_⟩
  have hr : Tendsto (fun j => (scalarBorelBump j).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hratio : ∀ᶠ j in atTop, (scalarBorelBump j).rOut ≤ 2 * (scalarBorelBump j).rIn := by
    filter_upwards with j
    dsimp only [scalarBorelBump]
    linarith
  exact ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hr hratio
    (scalar_borel_locallyIntegrable hlam a ha hb)

/-- Tonelli lifts position-velocity null sets to physical spacetime. -/
theorem scalar_borel_phase_ae_lift {p : (ℝ × ℝ) → Prop}
    (hp : ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)), p z) :
    ∀ᵐ P ∂(volume : Measure Point), p (P.position 0, P.velocity 0) := by
  have hv := PDE.volumePreserving_vecOneEquivReal.prod PDE.volumePreserving_vecOneEquivReal
  have hpv := hv.quasiMeasurePreserving.ae hp
  have hproj : Measure.QuasiMeasurePreserving
      (Prod.snd : ℝ × (PDE.Vec 1 × PDE.Vec 1) → PDE.Vec 1 × PDE.Vec 1) volume volume :=
    Measure.quasiMeasurePreserving_snd
  have hp' := hproj.ae hpv
  have h := (KineticPoint.measurePreserving_equivProd 1).quasiMeasurePreserving.ae hp'
  change ∀ᵐ P : Point ∂volume, p (P.position 0, P.velocity 0) at h
  exact h

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

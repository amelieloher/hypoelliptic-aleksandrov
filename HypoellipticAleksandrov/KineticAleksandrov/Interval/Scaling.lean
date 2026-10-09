module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.Setting
public import HypoellipticAleksandrov.KineticAleksandrov.Scaling.Radius

/-! # Kinetic scaling on bounded intervals

The interval is the literal affine preimage under `v = v₀ + r Y`.
Transport and ellipticity constants are unchanged; position scales by `r³`.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay
open HypoellipticAleksandrov.KineticAleksandrov.Scaling

/-- The affine preimage of an interval, with no fallback outside that domain. -/
theorem scaledDomain_interval (a c : ℝ) (v₀ : PDE.Vec 1) (r : {r : ℝ // 0 < r}) :
    scaledDomain (PDE.oneDimensionalAxisBox a c) v₀ r =
      PDE.oneDimensionalAxisBox ((a - v₀ 0) / r.1) ((c - v₀ 0) / r.1) := by
  ext Y
  simp only [scaledDomain, mem_ofPred_eq, PDE.mem_oneDimensionalAxisBox_iff,
    PDE.vecOneCoordinate, mem_Ioo, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [div_lt_iff₀ r.2, lt_div_iff₀ r.2]
  constructor <;> intro h <;> constructor <;> linarith only [h.1, h.2]

/-- Rescaled endpoints remain strictly ordered. -/
theorem scaled_interval_endpoints {a c : ℝ} (hac : a < c)
    (v₀ : PDE.Vec 1) (r : {r : ℝ // 0 < r}) :
    (a - v₀ 0) / r.1 < (c - v₀ 0) / r.1 :=
  (div_lt_div_iff_of_pos_right r.2).2 (sub_lt_sub_right hac _)

/-- The literal rescaled interval length is `r⁻¹` times the original length. -/
theorem scaled_interval_length (a c : ℝ) (v₀ : PDE.Vec 1) (r : {r : ℝ // 0 < r}) :
    (c - v₀ 0) / r.1 - (a - v₀ 0) / r.1 = r.1⁻¹ * (c - a) := by
  ring

/-- Admissibility of the rescaled interval. -/
theorem scaled_interval_admissible {a c : ℝ} (hac : a < c)
    (v₀ : PDE.Vec 1) (r : {r : ℝ // 0 < r}) :
    IsAdmissibleEvolutionDomain (scaledDomain (PDE.oneDimensionalAxisBox a c) v₀ r) := by
  rw [scaledDomain_interval]
  exact interval_admissible (scaled_interval_endpoints hac v₀ r)

/-- Source setting and all constants are preserved under interval scaling. -/
theorem scaled_interval_setting (lam Lam m Lb a c σ₀ : ℝ) (hac : a < c)
    (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1)
    (hs : SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b)
    (v₀ : PDE.Vec 1) (r : {r : ℝ // 0 < r}) :
    SourceSetting lam Lam m Lb (scaledDomain (PDE.oneDimensionalAxisBox a c) v₀ r)
      (scaledCoefficient B σ₀ v₀ r) (scaledDrift b v₀ r) := by
  rw [scaledDomain_interval]
  exact sourceSetting_interval (scaled_interval_endpoints hac v₀ r) _ _
    (scaledCoefficient_sectionTwo lam Lam B hs.1 σ₀ v₀ r)
    (scaledDrift_smooth b v₀ r hs.2.1) hs.2.2.1 hs.2.2.2.1
    (scaledDrift_transportBounds b v₀ r hs.2.2.2.2.1)

/-- The source kinetic affine map carries the rescaled stationary interval to the original. -/
theorem mapsDomain_interval (a c σ₀ : ℝ) (v₀ z₀ : PDE.Vec 1)
    (b : PDE.Vec 1 → PDE.Vec 1) (r : {r : ℝ // 0 < r}) :
    (KineticAffineScaling.ofRadius σ₀ v₀ z₀ b r).MapsDomain
      (PDE.oneDimensionalAxisBox a c) stationary
      (scaledDomain (PDE.oneDimensionalAxisBox a c) v₀ r) stationary := by
  intro τ
  ext Y
  simp only [movingDomain, stationary, PDE.mem_translateSet_iff_sub_mem,
    sub_zero, mem_preimage, scaledDomain, mem_ofPred_eq]
  rfl

/-- The source scaled-operator identity for the interval, with arbitrary smooth transport. -/
theorem lop_scaled_interval (σ₀ : ℝ) (v₀ z₀ : PDE.Vec 1)
    (b : PDE.Vec 1 → PDE.Vec 1) (r : {r : ℝ // 0 < r})
    (B : CoefficientField 1) (u : KineticPoint 1 → ℝ) (q : KineticPoint 1)
    (hu : ContDiffAt ℝ 2 (rawLift u) (rawPoint (scaledPoint σ₀ v₀ z₀ b r q))) :
    lop B b u (scaledPoint σ₀ v₀ z₀ b r q) =
      (r.1 ^ 2)⁻¹ * lop (scaledCoefficient B σ₀ v₀ r) (scaledDrift b v₀ r)
        (fun p => u (scaledPoint σ₀ v₀ z₀ b r p)) q :=
  KineticAffineScaling.lop_scaledPoint σ₀ v₀ z₀ b r B u q hu

/-- The rescaled interval realization is the affine pushforward of the original realization. -/
theorem realizes_ofRadius_interval (a c σ₀ : ℝ) (hac : a < c)
    (v₀ z₀ : PDE.Vec 1) (b : PDE.Vec 1 → PDE.Vec 1) (r : {r : ℝ // 0 < r})
    {B : CoefficientField 1}
    {S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary}
    {K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary}
    (hreal : RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary
      (measurableSet_of_isAdmissibleEvolutionDomain (interval_admissible hac))
      (zIndependentCoefficient B) b S K) :
    let hmap := mapsDomain_interval a c σ₀ v₀ z₀ b r
    let hJr := measurableSet_of_isAdmissibleEvolutionDomain
      (scaled_interval_admissible hac v₀ r)
    RealizesTerminalEvolution (scaledDomain (PDE.oneDimensionalAxisBox a c) v₀ r)
      stationary hJr (zIndependentCoefficient (scaledCoefficient B σ₀ v₀ r))
      (scaledDrift b v₀ r)
      (fiberOperator (KineticAffineScaling.pushKernel hmap K) hJr)
      (KineticAffineScaling.pushKernel hmap K) := by
  have h := KineticAffineScaling.realizes_pushKernel
    (mapsDomain_interval a c σ₀ v₀ z₀ b r)
    (isOpen_of_isAdmissibleEvolutionDomain (interval_admissible hac)) continuous_const
    (measurableSet_of_isAdmissibleEvolutionDomain (scaled_interval_admissible hac v₀ r)) hreal
  rw [KineticAffineScaling.ofRadius_coefficient, KineticAffineScaling.ofRadius_drift] at h
  exact h

/-- Fourier affine image and exact total-variation equality on the rescaled interval. -/
theorem realizes_ofRadius_interval_fourier_tv (a c σ₀ : ℝ) (hac : a < c)
    (v₀ z₀ : PDE.Vec 1) (b : PDE.Vec 1 → PDE.Vec 1) (r : {r : ℝ // 0 < r})
    {B : CoefficientField 1}
    {S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary}
    {K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary}
    (hreal : RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary
      (measurableSet_of_isAdmissibleEvolutionDomain (interval_admissible hac))
      (zIndependentCoefficient B) b S K)
    {S' : TerminalOperatorFamily (scaledDomain (PDE.oneDimensionalAxisBox a c) v₀ r)
      stationary}
    {K' : MovingFiberKernel (scaledDomain (PDE.oneDimensionalAxisBox a c) v₀ r) stationary}
    (hreal' : RealizesTerminalEvolution (scaledDomain (PDE.oneDimensionalAxisBox a c) v₀ r)
      stationary (measurableSet_of_isAdmissibleEvolutionDomain
        (scaled_interval_admissible hac v₀ r))
      (zIndependentCoefficient (scaledCoefficient B σ₀ v₀ r)) (scaledDrift b v₀ r) S' K')
    (q' : EvolutionQuery (scaledDomain (PDE.oneDimensionalAxisBox a c) v₀ r) stationary)
    (ξ : PDE.Vec 1) (ν ν' : ComplexMeasure (PDE.Vec 1))
    (hν : IsFourierProjection K (KineticAffineScaling.queryMap
      (mapsDomain_interval a c σ₀ v₀ z₀ b r) q') ξ ν)
    (hν' : IsFourierProjection K' q' (r.1 ^ 3 • ξ) ν') :
    (∀ E : Set (PDE.Vec 1), MeasurableSet E →
      ν E = Complex.exp (-Complex.I *
        ((r.1 ^ 2 * (q'.1.2.1 - q'.1.1) * PDE.vecDot ξ (b v₀) : ℝ) : ℂ)) *
        ν' ((fun Y : PDE.Vec 1 => v₀ + r.1 • Y) ⁻¹' E)) ∧
      totalVariationNorm ν = totalVariationNorm ν' := by
  have hreal'' : RealizesTerminalEvolution (scaledDomain (PDE.oneDimensionalAxisBox a c) v₀ r)
      stationary (measurableSet_of_isAdmissibleEvolutionDomain
        (scaled_interval_admissible hac v₀ r))
      ((KineticAffineScaling.ofRadius σ₀ v₀ z₀ b r).coefficient (zIndependentCoefficient B))
      ((KineticAffineScaling.ofRadius σ₀ v₀ z₀ b r).drift b) S' K' := by
    rw [KineticAffineScaling.ofRadius_coefficient, KineticAffineScaling.ofRadius_drift]
    exact hreal'
  exact KineticAffineScaling.realizes_fourier_tv _ (interval_admissible hac)
    (zeroCurve_piecewiseC1 1) (scaled_interval_admissible hac v₀ r)
    hreal hreal'' q' ξ ν ν' hν hν'

end HypoellipticAleksandrov.KineticAleksandrov.Interval

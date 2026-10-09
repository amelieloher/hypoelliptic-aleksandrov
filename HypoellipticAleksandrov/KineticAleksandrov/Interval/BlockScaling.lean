module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.Block
public import HypoellipticAleksandrov.KineticAleksandrov.Interval.Scaling
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.FrequencyBlocksRadius

/-! # Kinetic scaling of the length-independent interval unit block -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay
open HypoellipticAleksandrov.KineticAleksandrov.Scaling

/-- Arbitrary nonzero frequencies conditions on their kinetic time scale. -/
theorem interval_frequency_blocks
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam m Lb : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hm : 0 < m) (hmLb : m ≤ Lb) :
    ∃ L δ : ℝ, 0 < L ∧ 0 < δ ∧ δ < 1 ∧
      ∀ (a c : ℝ) (_hac : a < c) (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1),
      SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b →
      ∀ (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
      (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
      (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary),
      RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ
        (zIndependentCoefficient B) b S K →
      ∀ (ξ : PDE.Vec 1), ξ ≠ 0 → ∀ (σ : ℝ) (v : PDE.oneDimensionalAxisBox a c),
      ∀ (ht : σ ≤ σ + L * PDE.vecEuclideanNorm ξ ^ (-(2 / 3 : ℝ))),
      TV (intervalFourierKernel K σ
        (σ + L * PDE.vecEuclideanNorm ξ ^ (-(2 / 3 : ℝ))) ht ξ v) ≤ 1 - δ := by
  obtain ⟨L, δ, hL, hδ, hδ1, hunit⟩ := unit_frequency_block_interval
    hH hLE lam Lam m Lb hlam hlamLam hm hmLb
  refine ⟨L, δ, hL, hδ, hδ1, ?_⟩
  intro a c hac B b hs hJ S K hr ξ hξ σ v ht
  obtain ⟨hrpos, hr2, hrunit⟩ := frequency_radius_identities hξ
  let r : {r : ℝ // 0 < r} := ⟨PDE.vecEuclideanNorm ξ ^ (-(1 / 3 : ℝ)), hrpos⟩
  let D := scaledDomain (PDE.oneDimensionalAxisBox a c) v.1 r
  let hmap := mapsDomain_interval a c σ v.1 0 b r
  let hDr := measurableSet_of_isAdmissibleEvolutionDomain (scaled_interval_admissible hac v.1 r)
  let K' := KineticAffineScaling.pushKernel hmap K
  let S' := fiberOperator K' hDr
  have hr' := realizes_ofRadius_interval a c σ hac v.1 0 b r hr
  have hs' := scaled_interval_setting lam Lam m Lb a c σ hac B b hs v.1 r
  have hv' : (0 : PDE.Vec 1) ∈ movingDomain D stationary 0 := by
    rw [movingDomain_stationary]
    change v.1 + r.1 • (0 : PDE.Vec 1) ∈ PDE.oneDimensionalAxisBox a c
    simpa only [smul_zero, add_zero] using v.2
  let q' := movingQuery 0 L hL.le (0 : PDE.Vec 1) 0 hv'
  let ν' := fourierProjection K' q' (r.1 ^ 3 • ξ)
  have hν' := fourierProjection_spec K' q' (r.1 ^ 3 • ξ)
  have hunit' := hunit ((a - v.1 0) / r.1) ((c - v.1 0) / r.1)
    (scaled_interval_endpoints hac v.1 r) (scaledCoefficient B σ v.1 r) (scaledDrift b v.1 r)
  rw [← scaledDomain_interval a c v.1 r] at hunit'
  have hνunit : IsFourierProjection K' (movingQuery 0 (0 + L)
      (by simpa only [zero_add] using hL.le) 0 0 hv') (r.1 ^ 3 • ξ) ν' := by
    simpa only [zero_add] using hν'
  have hbound := hunit' hs' hDr S' K' hr' (r.1 ^ 3 • ξ) hrunit
    0 0 hv' (by simpa only [zero_add] using hL.le) ν' hνunit
  let ν := intervalFourierKernel K σ
    (σ + L * PDE.vecEuclideanNorm ξ ^ (-(2 / 3 : ℝ))) ht ξ v
  have hquery : KineticAffineScaling.queryMap hmap q' =
      movingQuery σ (σ + L * PDE.vecEuclideanNorm ξ ^ (-(2 / 3 : ℝ))) ht v.1 0
        (by simpa only [movingDomain_stationary] using v.2) := by
    apply Subtype.ext
    change (σ + r.1 ^ 2 * 0, σ + r.1 ^ 2 * L,
      v.1 + r.1 • (0 : PDE.Vec 1), (0 : PDE.Vec 1) +
        (r.1 ^ 2 * 0) • b v.1 + r.1 ^ 3 • (0 : PDE.Vec 1)) = _
    change (σ + r.1 ^ 2 * 0, σ + r.1 ^ 2 * L,
      v.1 + r.1 • (0 : PDE.Vec 1), (0 : PDE.Vec 1) +
        (r.1 ^ 2 * 0) • b v.1 + r.1 ^ 3 • (0 : PDE.Vec 1)) =
      (σ, σ + L * PDE.vecEuclideanNorm ξ ^ (-(2 / 3 : ℝ)), v.1, 0)
    simp only [mul_zero, add_zero, smul_zero, zero_smul]
    have hr2' : r.1 ^ 2 = PDE.vecEuclideanNorm ξ ^ (-(2 / 3 : ℝ)) := hr2
    rw [hr2', mul_comm L]
  have hν : IsFourierProjection K (KineticAffineScaling.queryMap hmap q') ξ ν := by
    rw [hquery]
    exact intervalFourierKernel_spec K _ _ ht ξ v
  have htv := (realizes_ofRadius_interval_fourier_tv a c σ hac v.1 0 b r hr hr'
    q' ξ ν ν' hν hν').2
  change (totalVariationNorm ν).toReal ≤ 1 - δ
  rw [htv]
  exact hbound

end HypoellipticAleksandrov.KineticAleksandrov.Interval

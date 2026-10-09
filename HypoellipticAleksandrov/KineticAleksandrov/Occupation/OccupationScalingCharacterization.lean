module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.OccupationScalingKernel
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.OccupationScalingTime
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.OccupationScalingPairing
public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourierOccupation

/-! # Scaling of the bounded-Borel occupation characterization -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic SectionTwo Scaling MeasureTheory Set
open scoped ENNReal

/-- Elapsed-time pairing is the ordinary open-interval pairing with the marginal kernel. -/
theorem occupation_rhs_interval {d : ℕ} (K : WholeKernel d) (σ T : ℝ) (hT : 0 < T)
    (ρ : Measure (PDE.Vec d)) (φ : TimeVelocity d → ℝ) :
    (∫ v, ∫ τ : ElapsedTime (ENNReal.ofReal T),
      ∫ w, φ (τ.1, w) ∂K.firstMarginal
        (wholeSpaceQuery σ (σ + τ.1) (le_add_of_nonneg_right τ.2.1.le) v 0)
      ∂elapsedVolume (ENNReal.ofReal T) ∂ρ) =
    ∫ v, (∫ t in Ioo 0 T, ∫ w, φ (t, w) ∂Green.occupationKernel K σ t v) ∂ρ := by
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun v => ?_
  have hh := Green.integral_elapsed_finite T hT
    (fun t => ∫ w, φ (t, w) ∂Green.occupationKernel K σ t v)
  dsimp only
  rw [← hh]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun τ => ?_
  dsimp only
  rw [Green.occupationKernel_of_nonneg K σ τ.1 τ.2.1.le v]

/-- Bounded-Borel pullback by the forward parabolic dilation. -/
def occupation_scaledTest {d : ℕ} (T : ℝ) (φ : BoundedBorel (TimeVelocity d)) :
    BoundedBorel (TimeVelocity d) :=
  ⟨fun q => φ (parabolicAffine 0 0 (Real.sqrt T) q),
    φ.measurable.comp ((contDiff_infty_parabolicAffine 0 0 (Real.sqrt T)).continuous.measurable),
    by
      obtain ⟨C, hC, hb⟩ := φ.exists_bound
      exact ⟨C, hC, fun q => hb _⟩⟩

/-- The real-interval occupation pairing of the constructed scaled kernel. -/
theorem occupation_rhs_scaled {d : ℕ} (K : WholeKernel d) (σ₀ : ℝ)
    {T : ℝ} (hT : 0 < T) (ρ : Measure (PDE.Vec d))
    (φ : TimeVelocity d → ℝ) :
    let r : {r : ℝ // 0 < r} := ⟨Real.sqrt T, Real.sqrt_pos.mpr hT⟩
    let Φ := KineticAffineScaling.ofRadius σ₀ 0 0 (identityDrift d) r
    let Kt := KineticAffineScaling.pushKernel (KineticAffineScaling.mapsDomain_wholeSpace Φ) K
    (∫ v, (∫ t in Ioo (0 : ℝ) 1,
      ∫ w, φ (parabolicAffine 0 0 (Real.sqrt T) (t, w))
        ∂Green.occupationKernel Kt 0 t v) ∂ρ.map (fun v => (Real.sqrt T)⁻¹ • v)) =
      T⁻¹ * ∫ v, (∫ t in Ioo (0 : ℝ) T,
        ∫ w, φ (t, w) ∂Green.occupationKernel K σ₀ t v) ∂ρ := by
  dsimp only
  let r : {r : ℝ // 0 < r} := ⟨Real.sqrt T, Real.sqrt_pos.mpr hT⟩
  let Φ := KineticAffineScaling.ofRadius σ₀ 0 0 (identityDrift d) r
  let Kt := KineticAffineScaling.pushKernel (KineticAffineScaling.mapsDomain_wholeSpace Φ) K
  have hs : Real.sqrt T ≠ 0 := (Real.sqrt_pos.mpr hT).ne'
  have hsq := Real.sq_sqrt hT.le
  have he : MeasurableEmbedding (fun v : PDE.Vec d => (Real.sqrt T)⁻¹ • v) :=
    (Homeomorph.smulOfNeZero (Real.sqrt T)⁻¹ (inv_ne_zero hs)).measurableEmbedding
  rw [he.integral_map, ← integral_const_mul]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun v => ?_
  dsimp only
  rw [← occupation_integral_time_dilation hT]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have hkernel := firstMarginal_radius_query σ₀ r K t ht.1.le
    ((Real.sqrt T)⁻¹ • v)
  have hcancel : r.1 • ((Real.sqrt T)⁻¹ • v) = v := by
    rw [smul_smul, mul_inv_cancel₀ hs, one_smul]
  have hKT : Green.occupationKernel Kt 0 t ((Real.sqrt T)⁻¹ • v) =
      (Green.occupationKernel K σ₀ (T * t) v).map
        (fun w => (Real.sqrt T)⁻¹ • w) := by
    rw [Green.occupationKernel_of_nonneg Kt 0 t ht.1.le]
    change (KineticAffineScaling.pushKernel
      (KineticAffineScaling.mapsDomain_wholeSpace Φ) K).firstMarginal _ = _
    dsimp only at hkernel
    rw [hcancel] at hkernel
    have hh := Green.occupationKernel_of_nonneg K σ₀
      (T * t) (mul_nonneg hT.le ht.1.le) v
    simpa only [r, hsq, zero_add, hh] using hkernel
  rw [hKT, he.integral_map]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun w => ?_
  dsimp only
  congr 1
  apply Prod.ext
  · change 0 + (Real.sqrt T) ^ 2 * t = T * t
    rw [hsq, zero_add]
  · change 0 + Real.sqrt T • ((Real.sqrt T)⁻¹ • w) = w
    rw [zero_add, smul_smul, mul_inv_cancel₀ hs, one_smul]

/-- A unit-time density for the constructed pushforward yields the original slab density. -/
theorem isOccupationDensity_scaled {d : ℕ} (K : WholeKernel d) (σ₀ : ℝ)
    {T : ℝ} (hT : 0 < T) (ρ : Measure (PDE.Vec d)) (gt : TimeVelocity d → ℝ)
    (hgt : IsOccupationDensity
      (KineticAffineScaling.pushKernel (KineticAffineScaling.mapsDomain_wholeSpace
        (KineticAffineScaling.ofRadius σ₀ 0 0 (identityDrift d)
          ⟨Real.sqrt T, Real.sqrt_pos.mpr hT⟩)) K) 0 1
      (ρ.map (fun v => (Real.sqrt T)⁻¹ • v)) gt) :
    IsOccupationDensity K σ₀ T ρ
      (fun q => T ^ (-(d : ℝ) / 2) *
        gt (parabolicAffine 0 0 (Real.sqrt T)⁻¹ q)) := by
  refine ⟨measurable_const.mul (hgt.1.comp
    ((contDiff_infty_parabolicAffine 0 0 (Real.sqrt T)⁻¹).continuous.measurable)),
    fun q => mul_nonneg (Real.rpow_nonneg hT.le _) (hgt.2.1 _), ?_⟩
  intro φ
  rw [occupation_scaledDensity_pairing hT]
  have hh := hgt.2.2 (occupation_scaledTest T φ)
  change (∫ q in Ioo (0 : ℝ) 1 ×ˢ univ,
    φ (parabolicAffine 0 0 (Real.sqrt T) q) * gt q) = _ at hh
  rw [hh, occupation_rhs_interval _ 0 1 zero_lt_one]
  change T * (∫ v, (∫ t in Ioo (0 : ℝ) 1,
    ∫ w, φ (parabolicAffine 0 0 (Real.sqrt T) (t, w)) ∂_) ∂_) = _
  have hs := occupation_rhs_scaled K σ₀ hT ρ φ
  have hp := occupation_rhs_interval K σ₀ T hT ρ φ
  have hm := congrArg (fun a : ℝ => T * a) hs
  rw [← mul_assoc, mul_inv_cancel₀ hT.ne', one_mul] at hm
  exact hm.trans hp.symm

end HypoellipticAleksandrov.KineticAleksandrov.Occupation

module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitL1FourierMoments
public import HypoellipticAleksandrov.KineticAleksandrov.Reconstruction.FiberInversion

/-! # Joint inverse representatives over the possibly singular exit-data marginal -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic SectionTwo Reconstruction ProbabilityTheory
open scoped ENNReal

/-- The jointly measurable real inverse representative in the original coordinate order. -/
def exitJointDensity {d : ℕ} (ν : Measure (PDE.Vec d × TimeVelocity d))
    [IsFiniteMeasure ν] (p : PDE.Vec d × TimeVelocity d) : ℝ :=
  ((2 * Real.pi) ^ d)⁻¹ * (vecInvIntegral (fun ξ => exitFourierRep ν ξ p.2) p.1).re

/-- The real inverse integral is measurable jointly in position and exit data. -/
theorem measurable_exitJointDensity {d : ℕ} (ν : Measure (PDE.Vec d × TimeVelocity d))
    [IsFiniteMeasure ν] : Measurable (exitJointDensity ν) := by
  unfold exitJointDensity vecInvIntegral
  apply measurable_const.mul
  apply Complex.measurable_re.comp
  have hc : Continuous (fun p : PDE.Vec d × PDE.Vec d =>
      Complex.exp (Complex.I * (PDE.vecDot p.1 p.2 : ℂ))) := by
    unfold PDE.vecDot
    fun_prop
  have hm : Measurable (fun q : (PDE.Vec d × TimeVelocity d) × PDE.Vec d =>
      Complex.exp (Complex.I * (PDE.vecDot q.2 q.1.1 : ℂ)) *
        exitFourierRep ν q.2 q.1.2) :=
    (hc.measurable.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))).mul
      ((measurable_exitFourierRep ν).comp
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
  exact hm.stronglyMeasurable.integral_prod_right.measurable

/-- Joint integrability of the Fourier representatives follows from the actual decay. -/
theorem ballExitFourierRep_integrable_prod
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)
    (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t})
    (hv : P.1.velocity ∈ PDE.euclideanBall v₀ (3 * R / 4))
    (hT : T.1 - P.1.time = R ^ 2 / 8) :
    let ν := ballExit hH hLE hd hlam hLam B hB v₀ hR P T
    Integrable (fun p : PDE.Vec d × TimeVelocity d => exitFourierRep ν p.1 p.2)
      (volume.prod (exitMarginal ν)) := by
  dsimp only
  let ν := ballExit hH hLE hd hlam hLam B hB v₀ hR P T
  apply (integrable_prod_iff (measurable_exitFourierRep ν).aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (integrable_exitFourierRep ν), ?_⟩
  have hnorm : (fun ξ => ∫ z, ‖exitFourierRep ν ξ z‖ ∂exitMarginal ν) =
      fun ξ => ‖exitL1Fourier ν ξ‖ := by
    funext ξ
    exact (L1.norm_of_fun_eq_integral_norm (integrable_exitFourierRep ν ξ)).symm
  rw [hnorm]
  simpa only [pow_zero, one_mul] using
    ballExitL1Fourier_integrable_moments hH hLE hd hlam hLam B hB v₀ hR P T hv hT 0

/-- Almost every conditional position measure has the explicit inverse-integral density. -/
theorem ballExitPositionKernel_density
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)
    (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t})
    (hv : P.1.velocity ∈ PDE.euclideanBall v₀ (3 * R / 4))
    (hT : T.1 - P.1.time = R ^ 2 / 8) :
    let ν := ballExit hH hLE hd hlam hLam B hB v₀ hR P T
    ∀ᵐ z ∂exitMarginal ν,
      exitPositionKernel ν z = volume.withDensity (fun y =>
        ENNReal.ofReal (exitJointDensity ν (y, z))) ∧
      ∀ y, 0 ≤ exitJointDensity ν (y, z) := by
  dsimp only
  let ν := ballExit hH hLE hd hlam hLam B hB v₀ hR P T
  have hi := (ballExitFourierRep_integrable_prod hH hLE hd hlam hLam B hB v₀ hR
    P T hv hT).prod_left_ae
  filter_upwards [hi] with z hz
  have hint : Integrable (vecFourier (exitPositionKernel ν z)) := hz
  refine ⟨?_, ?_⟩
  · exact eq_withDensity_vecInvDensity (exitPositionKernel ν z) hint
  · exact vecInvDensity_nonneg (exitPositionKernel ν z) hint

/-- The joint inverse density reconstructs the actual exit measure over its own marginal. -/
theorem ballExit_eq_withDensity_exitJointDensity
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)
    (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t})
    (hv : P.1.velocity ∈ PDE.euclideanBall v₀ (3 * R / 4))
    (hT : T.1 - P.1.time = R ^ 2 / 8) :
    let ν := ballExit hH hLE hd hlam hLam B hB v₀ hR P T
    ν = (volume.prod (exitMarginal ν)).withDensity
      (fun p => ENNReal.ofReal (exitJointDensity ν p)) := by
  dsimp only
  let ν := ballExit hH hLE hd hlam hLam B hB v₀ hR P T
  have hfib := ballExitPositionKernel_density hH hLE hd hlam hLam B hB v₀ hR P T hv hT
  change ∀ᵐ z ∂exitMarginal ν,
    exitPositionKernel ν z = volume.withDensity
      (fun y => ENNReal.ofReal (exitJointDensity ν (y, z))) ∧
      ∀ y, 0 ≤ exitJointDensity ν (y, z) at hfib
  change ν = (volume.prod (exitMarginal ν)).withDensity
    (fun p => ENNReal.ofReal (exitJointDensity ν p))
  have hm := measurable_exitJointDensity ν
  have hswap : ν.map Prod.swap = ((exitMarginal ν).prod volume).withDensity
      (fun p : TimeVelocity d × PDE.Vec d =>
        ENNReal.ofReal (exitJointDensity ν (p.2, p.1))) := by
    rw [← exitPositionKernel_disintegrate ν]
    ext S hS
    have hS' (z : TimeVelocity d) : MeasurableSet (Prod.mk z ⁻¹' S) :=
      measurable_prodMk_left hS
    rw [Measure.compProd_apply hS, withDensity_apply _ hS,
      ← lintegral_indicator hS, lintegral_prod _]
    · apply lintegral_congr_ae
      filter_upwards [hfib] with z hz
      rw [hz.1, withDensity_apply _ (hS' z), ← lintegral_indicator (hS' z)]
      apply lintegral_congr
      intro y
      by_cases hp : (z, y) ∈ S <;> simp [Set.indicator, hp]
    · exact ((hm.comp measurable_swap).ennreal_ofReal.indicator hS).aemeasurable
  have hmap := congrArg (fun μ : Measure (TimeVelocity d × PDE.Vec d) =>
    μ.map Prod.swap) hswap
  rw [Measure.map_map measurable_swap measurable_swap] at hmap
  have hid : Prod.swap ∘ Prod.swap = (id : PDE.Vec d × TimeVelocity d → _) := rfl
  rw [hid, Measure.map_id] at hmap
  refine hmap.trans ?_
  ext S hS
  rw [Measure.map_apply measurable_swap hS, withDensity_apply _
    (hS.preimage measurable_swap), withDensity_apply _ hS,
    ← lintegral_indicator (hS.preimage measurable_swap), ← lintegral_indicator hS]
  rw [← Measure.prod_swap, lintegral_map]
  · apply lintegral_congr
    intro p
    by_cases hp : p ∈ S <;> simp [Set.indicator, hp]
  · exact ((hm.comp measurable_swap).ennreal_ofReal.indicator
      (hS.preimage measurable_swap))
  · exact measurable_swap

end HypoellipticAleksandrov.KineticAleksandrov.LocalA

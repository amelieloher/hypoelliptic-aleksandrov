module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.SpatialDerivativesBoundary
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.SpatialDerivativesDensity
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.SpatialDerivativesConvolution
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.SpatialDerivativesKernelBounds
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundaryMeasureTranslation

/-! # The actual exit integral is the convolution with the canonical real density -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Filter Parabolic SectionTwo
open scoped ENNReal Convolution

variable (hH : HormanderHypoellipticityStatement)
  (hLE : LiebermanEllipsoidDirichletStatement)
  {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
  (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
  (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)
  (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t})
  (hv : P.1.velocity ∈ PDE.euclideanBall v₀ (3 * R / 4))
  (hT : T.1 - P.1.time = R ^ 2 / 8)

include hv hT

/-- The canonical inverse density is nonnegative for product-almost every exit coordinate. -/
theorem ballExit_density_nonneg :
    let ν := ballExit hH hLE hd hlam hLam B hB v₀ hR P T
    ∀ᵐ p ∂volume.prod (exitMarginal ν), 0 ≤ exitJointDensity ν p := by
  dsimp only
  let ν := ballExit hH hLE hd hlam hLam B hB v₀ hR P T
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_le measurable_const (measurable_exitJointDensity ν))).mpr
  exact Eventually.of_forall fun y =>
    (ballExitPositionKernel_density hH hLE hd hlam hLam B hB v₀ hR P T hv hT).mono
      (fun z hz => hz.2 y)

/-- Compactly extended boundary data pair with the canonical density by literal convolution. -/
theorem ballExit_boundary_convolution
    (H : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ) (hHc : Continuous H)
    (hc : HasCompactSupport H) (M : ℝ) (hb : ∀ q, ‖H q‖ ≤ M) (x : PDE.Vec d) :
    let ν := ballExit hH hLE hd hlam hLam B hB v₀ hR P T
    let f := spatialBoundaryLpData (exitMarginal ν) H hHc hc M hb P.1 v₀
    let G := exitL1Density ν
    (∫ Q, (H (KineticPoint.equivProd d (boundaryPositionShift x Q)) : ℂ)
      ∂ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P T) =
      (f ⋆[spatialDensityPairing (exitMarginal ν), volume] (G ∘ Neg.neg)) x := by
  dsimp only
  let ν := ballExit hH hLE hd hlam hLam B hB v₀ hR P T
  let μ := exitMarginal ν
  let f := spatialBoundaryLpData μ H hHc hc M hb P.1 v₀
  let G := exitL1Density ν
  let F : PDE.Vec d × TimeVelocity d → ℝ :=
    fun p => H (spatialBoundaryCoordinates P.1 v₀ (x + p.1, p.2))
  have hFc : Continuous F := hHc.comp
    ((uniformContinuous_spatialBoundaryCoordinates P.1 v₀).continuous.comp
      ((continuous_const.add continuous_fst).prodMk continuous_snd))
  have hFi : Integrable (fun p => (F p : ℂ)) ν :=
    Integrable.of_bound (Complex.continuous_ofReal.comp hFc).aestronglyMeasurable M
      (Eventually.of_forall fun p => by simpa only [Complex.norm_real] using hb _)
  have hi := spatialDensity_integral volume μ ν (exitJointDensity ν)
    (measurable_exitJointDensity ν)
    (ballExit_density_nonneg hH hLE hd hlam hLam B hB v₀ hR P T hv hT)
    (ballExit_eq_withDensity_exitJointDensity hH hLE hd hlam hLam B hB v₀ hR P T hv hT)
    G (ballExitL1Density_coe hH hLE hd hlam hLam B hB v₀ hR P T hv hT)
    F hFi (fun y => f (x + y))
    (fun y => spatialBoundaryLpData_coe μ H hHc hc M hb P.1 v₀ (x + y))
  have hr : (∫ p, (F p : ℂ) ∂ν) =
      ∫ Q, (H (KineticPoint.equivProd d (boundaryPositionShift x Q)) : ℂ)
        ∂ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P T := by
    change (∫ p, (F p : ℂ) ∂Measure.map (exitCoordinates P.1 v₀)
      (ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P T)) = _
    refine (integral_map (f := fun p => (F p : ℂ))
      (continuous_exitCoordinates P.1 v₀).aemeasurable
      (Complex.continuous_ofReal.comp hFc).aestronglyMeasurable).trans ?_
    apply integral_congr_ae
    filter_upwards [] with Q
    apply congrArg Complex.ofReal
    apply congrArg H
    change (Q.time, (P.1.position + (x +
      (Q.position - P.1.position - (Q.time - P.1.time) • v₀)) +
      (Q.time - P.1.time) • v₀, Q.velocity)) = (Q.time, (Q.position + x, Q.velocity))
    refine Prod.ext ?_ ?_
    · rfl
    · refine Prod.ext ?_ ?_
      · abel
      · rfl
  rw [← hr, hi]
  change (∫ y, spatialDensityPairing μ (f (x + y)) (G y)) =
    ∫ y, spatialDensityPairing μ (f y) (G (-(x - y)))
  have ha := integral_add_left_eq_self x (μ := (volume : Measure (PDE.Vec d)))
    (f := fun y => spatialDensityPairing μ (f y) (G (y - x)))
  simpa only [add_sub_cancel_left, neg_sub] using ha

end HypoellipticAleksandrov.KineticAleksandrov.LocalA

module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.SpatialDerivativesRepresentation
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.SpatialDerivativesSmooth

/-! # Spatial derivatives of the source-local solution controlled by its raw oscillation -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set Filter MeasureTheory Parabolic SectionTwo
open scoped Topology Convolution

/-- The literal three-quarter forward cylinder is contained in the outer cylinder. -/
theorem spatial_inner_subset_outer {d : ℕ} (Z₀ : KineticPoint d) {R : ℝ} (hR : 0 < R) :
    forwardCylinder Z₀ (3 * R / 4) (by positivity) ⊆ forwardCylinder Z₀ R hR := by
  intro P hP
  refine ⟨hP.1, hP.2.1.trans_le ?_, ?_, ?_⟩
  · nlinarith only [sq_nonneg R]
  · exact PDE.euclideanBall_mono (by positivity) (by linarith) hP.2.2.1
  · exact PDE.euclideanBall_mono (by positivity)
      (by nlinarith only [pow_nonneg hR.le 3]) hP.2.2.2

/-- The source-local spatial derivative bound uses the actual canonical density integral. -/
theorem spatial_forward_derivative_bound
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (Z₀ : KineticPoint d) {R : ℝ} (hR : 0 < R)
    (U : KineticPoint d → ℝ)
    (hUc : ContinuousOn U (closure (forwardCylinder Z₀ R hR)))
    (hUs : IsKineticC112On U (forwardCylinder Z₀ R hR))
    (hUe : ∀ Q ∈ forwardCylinder Z₀ R hR,
      forwardKineticOperator (ofTimeVelocityCoefficient B) U Q = 0)
    (P : LocalBallStart Z₀.velocity R)
    (hP : P.1 ∈ forwardCylinder Z₀ (3 * R / 4) (by positivity))
    (T : {t : ℝ // P.1.time < t}) (hT : T.1 - P.1.time = R ^ 2 / 8)
    (m : ℕ) (hm : 1 ≤ m) :
    let G := exitL1Density (ballExit hH hLE hd hlam hLam B hB Z₀.velocity hR P T)
    ‖iteratedFDeriv ℝ m (physicalPositionSlice U P.1) P.1.position‖ ≤
      Holder.oscillationOn U (forwardCylinder Z₀ R hR) *
        ∫ y, ‖iteratedFDeriv ℝ m G y‖ := by
  dsimp only
  let ν := ballExit hH hLE hd hlam hLam B hB Z₀.velocity hR P T
  let μ := exitMarginal ν
  let G := exitL1Density ν
  let M := Holder.oscillationOn U (forwardCylinder Z₀ R hR)
  have hPo := spatial_inner_subset_outer Z₀ hR hP
  obtain ⟨hM, H, hHc, hc, hb, he⟩ := spatialData_local_extension Z₀ P.1 hR hPo U hUc
  let f := spatialBoundaryLpData μ H hHc hc M hb P.1 Z₀.velocity
  let L := spatialDensityPairing μ
  let g := G ∘ Neg.neg
  let W := f ⋆[L, volume] g
  have hGs : ContDiff ℝ (⊤ : ℕ∞) G :=
    ballExitL1Density_contDiff hH hLE hd hlam hLam B hB Z₀.velocity hR P T hP.2.2.1 hT
  have hGc : HasCompactSupport G := spatialDensity_hasCompactSupport G (R ^ 3)
    (ballExitL1Density_zero_outside hH hLE hd hlam hLam B hB Z₀.velocity hR
      P T hP.2.2.1 hT)
  let e := LinearIsometryEquiv.neg ℝ (E := PDE.Vec d)
  have hgc : HasCompactSupport g := hGc.comp_homeomorph e.toHomeomorph
  have hgs : ContDiff ℝ (⊤ : ℕ∞) g := hGs.comp contDiff_id.neg
  have hfc : Continuous f := continuous_spatialBoundaryLpData μ H hHc hc M hb P.1 Z₀.velocity
  have hfb : ∀ y, ‖f y‖ ≤ M := spatialBoundaryLpData_norm_le μ H hHc hc M hM hb P.1 Z₀.velocity
  have hshift : Continuous (fun x : PDE.Vec d => boundaryPositionShift x P.1) := by
    apply KineticPoint.continuous_mk continuous_const
      (continuous_const.add continuous_id) continuous_const
  have hmem : ∀ᶠ x : PDE.Vec d in 𝓝 0,
      boundaryPositionShift x P.1 ∈ forwardCylinder Z₀ (3 * R / 4) (by positivity) :=
    hshift.continuousAt.preimage_mem_nhds
      ((isOpen_forwardCylinder Z₀ _ (by positivity)).mem_nhds
        (by simpa only [boundaryPositionShift, add_zero] using hP))
  let s : PDE.Vec d → ℝ := fun x => U (boundaryPositionShift x P.1) - U P.1
  have hsW : (fun x => (s x : ℂ)) =ᶠ[𝓝 0] W := by
    filter_upwards [hmem] with x hx
    simpa only [s, Complex.ofReal_sub] using spatial_local_convolution hH hLE hd hlam hLam
      B hB Z₀ hR U hUc hUs hUe P hP T hT H hHc hc M hb (U P.1) he x hx
  have hus := spatial_forward_slice_smooth hH B hB Z₀ hR U hUs hUe P.1 hPo
  have hsu : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun x => U (boundaryPositionShift x P.1)) (0 : PDE.Vec d) := by
    have ha : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun x : PDE.Vec d => P.1.position + x) (0 : PDE.Vec d) :=
      contDiffAt_const.add contDiffAt_id
    have hus' : ContDiffAt ℝ (⊤ : ℕ∞) (physicalPositionSlice U P.1)
        (P.1.position + (0 : PDE.Vec d)) := by simpa only [add_zero] using hus
    exact hus'.comp (0 : PDE.Vec d) ha
  have hss : ContDiffAt ℝ (⊤ : ℕ∞) s 0 := hsu.sub contDiffAt_const
  have hnorm : ‖iteratedFDeriv ℝ m (fun x => (s x : ℂ)) 0‖ =
      ‖iteratedFDeriv ℝ m (physicalPositionSlice U P.1) P.1.position‖ := by
    change ‖iteratedFDeriv ℝ m (Complex.ofRealLI ∘ s) 0‖ = _
    rw [Complex.ofRealLI.norm_iteratedFDeriv_comp_left hss (by simp)]
    have hi := iteratedFDeriv_sub_apply (i := m) (hsu.of_le (by simp))
      (contDiffAt_const (c := U P.1))
    change ‖iteratedFDeriv ℝ m
      ((fun x => U (boundaryPositionShift x P.1)) - fun _ => U P.1) 0‖ = _
    rw [hi, iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, sub_zero]
    change ‖iteratedFDeriv ℝ m
      (fun x => physicalPositionSlice U P.1 (P.1.position + x)) 0‖ = _
    rw [iteratedFDeriv_comp_add_left, add_zero]
  have hgnorm (y : PDE.Vec d) : ‖iteratedFDeriv ℝ m g y‖ =
      ‖iteratedFDeriv ℝ m G (-y)‖ := e.norm_iteratedFDeriv_comp_right G y m
  have hgint : (∫ y, ‖iteratedFDeriv ℝ m g y‖) = ∫ y, ‖iteratedFDeriv ℝ m G y‖ := by
    simp_rw [hgnorm]
    exact integral_neg_eq_self (fun y : PDE.Vec d => ‖iteratedFDeriv ℝ m G y‖) volume
  have hd := convolution_iteratedFDeriv_bound volume f hfc.locallyIntegrable
    M hM hfb m L g hgc hgs (0 : PDE.Vec d)
  rw [hgint] at hd
  have hd' : ‖iteratedFDeriv ℝ m W 0‖ ≤ M * ∫ y, ‖iteratedFDeriv ℝ m G y‖ :=
    hd.trans (mul_le_mul_of_nonneg_right
      ((mul_le_mul_of_nonneg_right (spatialDensityPairing_norm_le μ) hM).trans_eq
        (one_mul M)) (integral_nonneg fun _ => norm_nonneg _))
  rw [← hnorm, (hsW.iteratedFDeriv ℝ m).eq_of_nhds]
  exact hd'

end HypoellipticAleksandrov.KineticAleksandrov.LocalA

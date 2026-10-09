module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.SpatialDerivativesExit
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.LocalRepresentationClosure

/-! # The local solution equals its boundary-data convolution at translated inner poles -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic SectionTwo
open scoped Convolution

/-- The local cone representation becomes a convolution against one fixed exit density. -/
theorem spatial_local_convolution
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
    (H : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ) (hHc : Continuous H)
    (hc : HasCompactSupport H) (M : ℝ) (hb : ∀ q, ‖H q‖ ≤ M) (c : ℝ)
    (hHe : ∀ Q ∈ closure (forwardCylinder Z₀ R hR),
      H (KineticPoint.equivProd d Q) = U Q - c)
    (x : PDE.Vec d)
    (hx : boundaryPositionShift x P.1 ∈
      forwardCylinder Z₀ (3 * R / 4) (by positivity)) :
    let ν := ballExit hH hLE hd hlam hLam B hB Z₀.velocity hR P T
    let f := spatialBoundaryLpData (exitMarginal ν) H hHc hc M hb P.1 Z₀.velocity
    let G := exitL1Density ν
    (U (boundaryPositionShift x P.1) - c : ℂ) =
      (f ⋆[spatialDensityPairing (exitMarginal ν), volume] (G ∘ Neg.neg)) x := by
  dsimp only
  let Px := boundaryStartShift x P
  let μx := ballExitRaw hH hLE hd hlam hLam B hB Z₀.velocity hR Px T
  have : IsFiniteMeasure μx :=
    (ballExitRaw_spec hH hLE hd hlam hLam B hB Z₀.velocity hR Px T).1
  have hr := local_cone_representation hH hLE hd hlam hLam B hB Z₀.velocity hR
    Z₀ U hUc hUs hUe Px rfl hx T hT
  have hs := ballExitRaw_local_outer hH hLE hd hlam hLam B hB Z₀ hR Px hx T hT
  have hi : Integrable (fun Q => H (KineticPoint.equivProd d Q)) μx :=
    Integrable.of_bound
      (hHc.comp (KineticPoint.homeomorphProd d).continuous).aestronglyMeasurable M
      (Filter.Eventually.of_forall fun Q => hb _)
  have hm : μx univ = 1 := ballExitRaw_mass hH hLE hd hlam hLam B hB Z₀.velocity hR Px T
  have hre : U Px.1 = (∫ Q, H (KineticPoint.equivProd d Q) ∂μx) + c := by
    calc
      _ = ∫ Q, U Q ∂μx := hr
      _ = ∫ Q, (H (KineticPoint.equivProd d Q) + c) ∂μx := by
        apply integral_congr_ae
        filter_upwards [hs] with Q hQ
        rw [hHe Q hQ]
        exact (sub_add_cancel _ _).symm
      _ = _ := by
        rw [integral_add hi (integrable_const c)]
        simp only [integral_const, Measure.real, hm, ENNReal.toReal_one, one_smul]
  have hre' : (U Px.1 - c : ℂ) =
      ∫ Q, (H (KineticPoint.equivProd d Q) : ℂ) ∂μx := by
    rw [integral_complex_ofReal, hre, Complex.ofReal_add, add_sub_cancel_right]
  refine hre'.trans ?_
  change (∫ Q, (H (KineticPoint.equivProd d Q) : ℂ)
    ∂ballExitRaw hH hLE hd hlam hLam B hB Z₀.velocity hR (boundaryStartShift x P) T) = _
  rw [← ballExitRaw_translation hH hLE hd hlam hLam B hB Z₀.velocity hR x P T]
  refine (integral_map (f := fun Q => (H (KineticPoint.equivProd d Q) : ℂ))
    (boundaryPositionHomeomorph x).measurable.aemeasurable
    (Complex.continuous_ofReal.comp
      (hHc.comp (KineticPoint.homeomorphProd d).continuous)).aestronglyMeasurable).trans ?_
  exact ballExit_boundary_convolution hH hLE hd hlam hLam B hB Z₀.velocity hR P T
    hP.2.2.1 hT H hHc hc M hb x

end HypoellipticAleksandrov.KineticAleksandrov.LocalA

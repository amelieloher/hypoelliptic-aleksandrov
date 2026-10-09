module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ExitFourierRaw
import Mathlib.Probability.Kernel.MeasurableIntegral

/-! # The actual later Fourier family on valid velocities and its measurable test extensions -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory SectionTwo Parabolic ProbabilityTheory

variable (hH : HormanderHypoellipticityStatement)
  (hLE : LiebermanEllipsoidDirichletStatement)
  {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ}
  (hlam : 0 < lam) (hLam : lam ≤ Lam)
  (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
  (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)

/-- The actual later Fourier exit measure, defined only on valid velocities. -/
def ballLaterExitFourier (s T : ℝ) (hsT : s < T) (ξ : PDE.Vec d)
    (v : EvolutionPosition (PDE.euclideanBall v₀ R) (fun _ => 0) s) :
    ComplexMeasure (TimeVelocity d) :=
  exitFourier (ballExit hH hLE hd hlam hLam B hB v₀ hR
    (ballStateStart s (positionStateZero _ _ s v)) ⟨T, hsT⟩) ξ

/-- Each Borel test of the later Fourier family is measurably parameterized by valid velocity. -/
theorem measurable_ballLaterExitFourier_apply (s T : ℝ) (hsT : s < T) (ξ : PDE.Vec d)
    (E : Set (TimeVelocity d)) (hE : MeasurableSet E) :
    Measurable (fun v => ballLaterExitFourier hH hLE hd hlam hLam B hB v₀ hR
      s T hsT ξ v E) := by
  let P : KineticPoint d := ⟨s, 0, 0⟩
  let K := ballBoundaryKernel hH hLE hd hlam hLam B hB v₀ hR s T hsT
  have hm := ((measurable_exitFourierTest P v₀ ξ hE).stronglyMeasurable.integral_kernel
    (κ := K)).measurable.comp (measurable_positionStateZero (PDE.euclideanBall v₀ R)
      (fun _ => 0) s)
  convert hm using 1
  funext v
  exact exitFourier_map_exitCoordinates_apply _ P v₀ ξ E hE

/-- The later actual Fourier exit measure has variation at most one for every valid velocity. -/
theorem ballLaterExitFourier_variation_le_one (s T : ℝ) (hsT : s < T) (ξ : PDE.Vec d)
    (v : EvolutionPosition (PDE.euclideanBall v₀ R) (fun _ => 0) s) :
    (ballLaterExitFourier hH hLE hd hlam hLam B hB v₀ hR s T hsT ξ v).variation univ ≤ 1 :=
  ballExit_fourier_totalVariation_le_one hH hLE hd hlam hLam B hB v₀ hR _ _ ξ

/-- Extending only scalar tests by zero gives a measurable ambient-velocity integrand.
The later exit measures themselves retain their valid-velocity carrier. -/
def ballLaterExitFourierTest (s T : ℝ) (hsT : s < T) (ξ : PDE.Vec d)
    (E : Set (TimeVelocity d)) : PDE.Vec d → ℂ :=
  Function.extend Subtype.val
    (fun v => ballLaterExitFourier hH hLE hd hlam hLam B hB v₀ hR s T hsT ξ v E)
    (fun _ => 0)

/-- The extended scalar Fourier test remains measurable. -/
theorem measurable_ballLaterExitFourierTest (s T : ℝ) (hsT : s < T) (ξ : PDE.Vec d)
    (E : Set (TimeVelocity d)) (hE : MeasurableSet E) :
    Measurable (ballLaterExitFourierTest hH hLE hd hlam hLam B hB v₀ hR s T hsT ξ E) :=
  (MeasurableEmbedding.subtype_coe
    (measurableSet_movingDomain (PDE.isOpen_euclideanBall v₀ R).measurableSet s)).measurable_extend
      (measurable_ballLaterExitFourier_apply hH hLE hd hlam hLam B hB v₀ hR
        s T hsT ξ E hE) measurable_const

/-- On valid velocities the extended scalar test is the actual later measure evaluation. -/
theorem ballLaterExitFourierTest_valid (s T : ℝ) (hsT : s < T) (ξ : PDE.Vec d)
    (E : Set (TimeVelocity d))
    (v : EvolutionPosition (PDE.euclideanBall v₀ R) (fun _ => 0) s) :
    ballLaterExitFourierTest hH hLE hd hlam hLam B hB v₀ hR s T hsT ξ E v.1 =
      ballLaterExitFourier hH hLE hd hlam hLam B hB v₀ hR s T hsT ξ v E :=
  Subtype.val_injective.extend_apply _ _ _

/-- The ambient scalar extension is zero away from the genuine valid-velocity fiber. -/
theorem ballLaterExitFourierTest_invalid (s T : ℝ) (hsT : s < T) (ξ : PDE.Vec d)
    (E : Set (TimeVelocity d)) (v : PDE.Vec d)
    (hv : v ∉ movingDomain (PDE.euclideanBall v₀ R) (fun _ => 0) s) :
    ballLaterExitFourierTest hH hLE hd hlam hLam B hB v₀ hR s T hsT ξ E v = 0 := by
  apply Function.extend_apply'
  rintro ⟨w, hw⟩
  exact hv (hw ▸ w.2)

end HypoellipticAleksandrov.KineticAleksandrov.LocalA

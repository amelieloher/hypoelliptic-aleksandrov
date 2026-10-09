module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceCanonical
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.Assembly

/-! # The canonical ball kernel and its actual parabolic marginal -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open HypoellipticAleksandrov Parabolic SectionTwo Set MeasureTheory

/-- The valid query corresponding to physical starting and terminal times. -/
def ballEvolutionQuery {d : ℕ} {v₀ : PDE.Vec d} {R : ℝ}
    (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t}) :
    EvolutionQuery (PDE.euclideanBall v₀ R) (fun _ => 0) :=
  evolutionQueryOfState _ _ P.1.time T.1 T.2.le (ballStartState P)

/-- The physical ball transition is the master measure at its literal valid query.
Terminal states retain the evolution coordinate order (velocity, position). -/
def ballTransition (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement) {d : ℕ} (hd : 1 ≤ d)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)
    (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t}) :
    Measure (EvolutionAmbientState d) :=
  (localBallKernel hH hLE hd hlam hLam B hB v₀ hR).master (ballEvolutionQuery P T)

/-- The actual uniquely chosen ball kernel inherits the proved full marginal bundle. -/
theorem localBallKernel_marginal (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement) {d : ℕ} (hd : 1 ≤ d)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R) :
    HasParabolicMarginalBundle (PDE.euclideanBall v₀ R) (fun _ => 0)
      (PDE.isOpen_euclideanBall v₀ R).measurableSet (zIndependentCoefficient B)
      (localBallKernel hH hLE hd hlam hLam B hB v₀ hR) := by
  obtain ⟨hBs, hBsym, hBell⟩ := sectionTwoCoefficient_fullBounds lam Lam B hB
  have hb := identityDrift_bounds d
  obtain ⟨S, K, hc, -, -, -, -, hi, -, -, -, -, he, hcomp, -, -, hpar⟩ :=
    exists_terminalEvolution_of_classical hLE hH d hd lam Lam 1 1 hlam hLam
      one_pos le_rfl (PDE.euclideanBall v₀ R) (fun _ => 0)
      (zIndependentCoefficient B) (identityDrift d) (localBall_admissible v₀ hR)
      (zeroCurve_piecewiseC1 d) hBs hBsym hBell (identityDrift_smooth d) hb.1 hb.2
  have hreal : RealizesTerminalEvolution (PDE.euclideanBall v₀ R) (fun _ => 0)
      (PDE.isOpen_euclideanBall v₀ R).measurableSet
      (zIndependentCoefficient B) (identityDrift d) S K := ⟨hc, hi, he, hcomp⟩
  have hk := congrArg Prod.snd
    (localBallEvolution_unique hH hLE hd hlam hLam B hB v₀ hR (S, K) hreal)
  change K = localBallKernel hH hLE hd hlam hLam B hB v₀ hR at hk
  exact hk ▸ hpar

/-- First marginal mass equals joint terminal mass at every physical starting position. -/
theorem ballTransition_mass_eq_marginal (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement) {d : ℕ} (hd : 1 ≤ d)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)
    (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t}) :
    (ballTransition hH hLE hd hlam hLam B hB v₀ hR P T).real univ =
      (parabolicMarginalKernel (localBallKernel hH hLE hd hlam hLam B hB v₀ hR)
        (PDE.isOpen_euclideanBall v₀ R).measurableSet P.1.time T.1 T.2.le
        ⟨P.1.velocity, by simpa only [movingDomain_ball_zero] using P.2⟩).real univ := by
  let K := localBallKernel hH hLE hd hlam hLam B hB v₀ hR
  let hD := (PDE.isOpen_euclideanBall v₀ R).measurableSet
  obtain ⟨Q, hfirst, _⟩ := localBallKernel_marginal hH hLE hd hlam hLam B hB v₀ hR
    (fun _ _ _ _ => rfl)
  rw [Measure.real, Measure.real, hfirst _ _ _ _ P.1.position]
  have hm := K.map_fiberFirstMarginal_eq_firstMarginal hD P.1.time T.1 T.2.le
    (ballStartState P)
  have huniv := congrArg (fun μ : Measure (PDE.Vec d) => μ univ) hm
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ,
    preimage_univ, K.firstMarginal_apply _ _ MeasurableSet.univ] at huniv
  exact congrArg ENNReal.toReal huniv.symm

end HypoellipticAleksandrov.KineticAleksandrov.LocalA

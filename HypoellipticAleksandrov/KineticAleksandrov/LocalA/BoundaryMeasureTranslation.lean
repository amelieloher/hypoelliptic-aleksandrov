module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundaryMeasureCanonical
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundarySolutionTranslation

/-! # Translation covariance of the uniquely characterized ball exit measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory

/-- Physical position translation preserves valid ball starts. -/
def boundaryStartShift {d : ℕ} {v₀ : PDE.Vec d} {R : ℝ}
    (h : PDE.Vec d) (P : LocalBallStart v₀ R) : LocalBallStart v₀ R :=
  ⟨boundaryPositionShift h P.1, P.2⟩

variable (hH : HormanderHypoellipticityStatement)
  (hLE : LiebermanEllipsoidDirichletStatement)
  {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ}
  (hlam : 0 < lam) (hLam : lam ≤ Lam)
  (B : CoefficientField d) (hB : SectionTwo.IsSectionTwoCoefficient lam Lam B)
  (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)

/-- Translating the pole translates the actual ambient exit measure. -/
theorem ballExitRaw_translation (h : PDE.Vec d) (P : LocalBallStart v₀ R)
    (T : {t : ℝ // P.1.time < t}) :
    Measure.map (boundaryPositionShift h) (ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P T) =
      ballExitRaw hH hLE hd hlam hLam B hB v₀ hR (boundaryStartShift h P) T := by
  have hmeas : Measurable (boundaryPositionShift h) :=
    (boundaryPositionHomeomorph h).measurable
  apply ballExitRaw_unique hH hLE hd hlam hLam B hB v₀ hR (boundaryStartShift h P) T
  intro φ hφ hc
  rw [integral_map hmeas.aemeasurable (boundary_probe_continuous φ hφ).aestronglyMeasurable]
  have hc' : HasCompactSupport (φ ∘ boundaryPositionShift h) :=
    hc.comp_homeomorph (boundaryPositionHomeomorph h)
  exact ((ballExitRaw_spec hH hLE hd hlam hLam B hB v₀ hR P T).2.2
    (φ ∘ boundaryPositionShift h) (boundary_shift_smooth h φ hφ) hc').trans
      (ballBoundarySolution_translation hH hLE hd hlam hLam B hB v₀ hR
        h P.1.time T.1 φ hφ hc P.1).symm

/-- Exit coordinates remove a simultaneous physical position translation. -/
theorem ballExit_translation (h : PDE.Vec d) (P : LocalBallStart v₀ R)
    (T : {t : ℝ // P.1.time < t}) :
    ballExit hH hLE hd hlam hLam B hB v₀ hR (boundaryStartShift h P) T =
      ballExit hH hLE hd hlam hLam B hB v₀ hR P T := by
  unfold ballExit
  rw [← ballExitRaw_translation hH hLE hd hlam hLam B hB v₀ hR h P T]
  have hmeas : Measurable (boundaryPositionShift h) :=
    (boundaryPositionHomeomorph h).measurable
  rw [Measure.map_map (continuous_exitCoordinates _ _).measurable hmeas]
  congr 1
  funext Q
  simp only [Function.comp_apply, exitCoordinates, boundaryStartShift, boundaryPositionShift,
    add_sub_add_right_eq_sub]

end HypoellipticAleksandrov.KineticAleksandrov.LocalA

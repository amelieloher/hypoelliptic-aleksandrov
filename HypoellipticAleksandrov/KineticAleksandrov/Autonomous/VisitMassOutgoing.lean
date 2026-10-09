module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitMassEntranceIntegrals

/-! # The quadratic vanishes on every outgoing internal face -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

/-- The source quadratic vanishes on both physical active endpoints. -/
theorem visitQuadratic_frontier_zero (c : Clock) {v : ℝ} (hv : v ∈ frontier c.active) :
    visitQuadratic c v = 0 := by
  have ho : c.vbar - 3 * c.r / 4 < c.vbar + 3 * c.r / 4 := by
    nlinarith [c.positive]
  rw [Clock.active, frontier_Ioo ho] at hv
  rcases hv with hv | hv
  · exact hv ▸ (visitQuadratic_endpoints c).1
  · exact hv ▸ (visitQuadratic_endpoints c).2

/-- Every outgoing visit is concentrated on the zero set of the physical quadratic. -/
theorem visitQuadratic_ae_zero_outgoing
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) (n : ℕ) :
    ∀ᵐ p ∂visitOutgoingPiece hH hLE hlam hLam A c J s T P n,
      visitQuadratic c (p.velocity 0) = 0 := by
  apply (ae_restrict_mem
    (measurableSet_visitBoundary s T (visitActiveInterval c) J)).mono
  intro p hp
  apply visitQuadratic_frontier_zero c
  exact hp.2.2.1

/-- The outgoing contribution to the summed quadratic identity is exactly zero. -/
theorem visitQuadratic_outgoing_integral_zero
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) (n : ℕ) :
    (∫ p, visitQuadratic c (p.velocity 0)
      ∂visitOutgoingPiece hH hLE hlam hLam A c J s T P n) = 0 := by
  rw [integral_congr_ae (visitQuadratic_ae_zero_outgoing hH hLE hlam hLam A c J s T P n)]
  exact integral_zero _ _

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

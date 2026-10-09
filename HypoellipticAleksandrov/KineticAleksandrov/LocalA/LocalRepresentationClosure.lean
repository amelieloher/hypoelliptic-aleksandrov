module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.LocalRepresentation
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.MassRepresentationMass

/-! # The actual local exit law stays in the closure of the original cylinder -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic SectionTwo

/-- The short-time exit cone lies in the closure of the original solution domain. -/
theorem ballExitRaw_local_outer
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (Z₀ : KineticPoint d) {R : ℝ} (hR : 0 < R)
    (P : LocalBallStart Z₀.velocity R)
    (hP : P.1 ∈ forwardCylinder Z₀ (3 * R / 4) (by positivity))
    (T : {t : ℝ // P.1.time < t}) (hT : T.1 - P.1.time = R ^ 2 / 8) :
    ∀ᵐ Q ∂ballExitRaw hH hLE hd hlam hLam B hB Z₀.velocity hR P T,
      Q ∈ closure (forwardCylinder Z₀ R hR) := by
  have ht : T.1 ≤ Z₀.time + R ^ 2 := by
    have hp := hP.2.1
    nlinarith only [hp, hT, sq_pos_of_pos hR]
  filter_upwards [ballExitRaw_cone hH hLE hd hlam hLam B hB Z₀.velocity hR P T,
    ballExitRaw_ae_trace hH hLE hd hlam hLam B hB Z₀.velocity hR P T] with Q hQ htr
  have hq := localTrace_subset_closed T.2.le Z₀.velocity R htr
  have hqt : Q.time ≤ P.1.time + R ^ 2 / 8 := by linarith only [hQ.2.1, hT]
  have hx := local_cone_cutoff_mem Z₀ P.1 Q hR hP hQ.1 hqt hQ.2.2
  apply local_closed_strip_mem_outer Z₀ Q hR hP.1.le ht hq
  apply PDE.euclideanBall_mono (by positivity)
    (by nlinarith only [pow_pos hR 3]) hx

end HypoellipticAleksandrov.KineticAleksandrov.LocalA

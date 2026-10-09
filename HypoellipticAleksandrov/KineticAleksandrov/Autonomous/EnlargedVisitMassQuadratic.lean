module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassTerminal
import Mathlib.Tactic

/-! # Summing the enlarged-strip quadratic identities -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory HypoellipticAleksandrov

/-- Entrance support gives an integrable quadratic with its exact source lower bound. -/
theorem enlargedQuadratic_entrance_lower_integral
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) (hs : s ≤ P.time) (hT : P.time < T) (n : ℕ) :
    5 * c.r ^ 2 / 16 *
      (enlargedVisitEntrance hH hLE hlam hLam A c J s T P n univ).toReal ≤
      ∫ p, visitQuadratic c (p.velocity 0)
        ∂enlargedVisitEntrance hH hLE hlam hLam A c J s T P n := by
  have hm := enlargedVisitEntrance_ae_support hH hLE hlam hLam A c J s T P hs hT n
  have hi : Integrable (fun p => visitQuadratic c (p.velocity 0))
      (enlargedVisitEntrance hH hLE hlam hLam A c J s T P n) := by
    apply Integrable.mono' (integrable_const (9 * c.r ^ 2 / 16))
      (((visitQuadratic_smooth c).continuous.comp
        ((continuous_apply 0).comp continuous_velocity)).measurable.aestronglyMeasurable)
    filter_upwards [hm] with p hp
    change ‖visitQuadratic c (p.velocity 0)‖ ≤ 9 * c.r ^ 2 / 16
    rw [Real.norm_eq_abs, abs_of_nonneg
      ((by positivity : 0 ≤ 5 * c.r ^ 2 / 16).trans
        (visitQuadratic_entrance_lower c hp.2.2))]
    exact visitQuadratic_le c _
  have h := integral_mono_ae (integrable_const (5 * c.r ^ 2 / 16)) hi
    (hm.mono fun _ hp => visitQuadratic_entrance_lower c hp.2.2)
  simpa only [integral_const, smul_eq_mul, Measure.real, mul_comm] using h

/-- Terminal mixtures at the observation horizon are finite for each finite entrance. -/
theorem enlarged_terminalPiece_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) (hs : s ≤ P.time) (hT : P.time < T) (n : ℕ) :
    IsFiniteMeasure ((enlargedVisitEntrance hH hLE hlam hLam A c J s T P n).bind
      (enlargedActiveTerminalFamily hH hLE hlam hLam A c J T)) := by
  rw [enlargedActiveTerminal_bind_eq_restrict hH hLE hlam hLam A c J T _
    ((enlargedVisitEntrance_ae_support hH hLE hlam hLam A c J s T P hs hT n).mono
      fun _ hp => hp.2.1)]
  infer_instance

/-- The terminal contribution has the quadratic maximum times its actual terminal mass. -/
theorem enlargedQuadratic_exit_integral_le_terminal_mass
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) (hs : s ≤ P.time) (hT : P.time < T)
    (hJ : closure c.active ⊆ J.carrier) (n : ℕ) :
    (∫ q, visitQuadratic c (q.velocity 0)
      ∂(enlargedVisitExitKernel hH hLE hlam hLam A (visitActiveUnion c J) T ∘ₘ
        enlargedVisitEntrance hH hLE hlam hLam A c J s T P n)) ≤
    9 * c.r ^ 2 / 16 *
      (((enlargedVisitEntrance hH hLE hlam hLam A c J s T P n).bind
        (enlargedActiveTerminalFamily hH hLE hlam hLam A c J T)) univ).toReal := by
  let mu := enlargedVisitEntrance hH hLE hlam hLam A c J s T P n
  have ht := (enlargedVisitEntrance_ae_support hH hLE hlam hLam A c J s T P hs hT n).mono
    fun _ hp => hp.2.1
  have : IsFiniteMeasure (mu.bind
      (enlargedActiveTerminalFamily hH hLE hlam hLam A c J T)) :=
    enlarged_terminalPiece_isFiniteMeasure hH hLE hlam hLam A c J s T P hs hT n
  have hi := (enlargedQuadratic_integrable_exit hH hLE hlam hLam A c J T mu).restrict
    (s := {q | q.time = T})
  rw [← enlargedActiveTerminal_bind_eq_restrict hH hLE hlam hLam A c J T mu ht] at hi
  rw [enlargedQuadratic_exit_integral_eq_terminal hH hLE hlam hLam A c J T hJ mu ht]
  have h := integral_mono_ae hi (integrable_const (9 * c.r ^ 2 / 16))
    (Filter.Eventually.of_forall fun q => visitQuadratic_le c (q.velocity 0))
  simpa only [integral_const, smul_eq_mul, Measure.real, mul_comm] using h

/-- The exact quadratic count inequality for the canonical finite active pieces. -/
theorem enlargedQuadratic_partial_mass_bound
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) (hs : s ≤ P.time) (hT : P.time < T)
    (hJ : closure c.active ⊆ J.carrier) (N : ℕ) :
    5 * c.r ^ 2 / 16 *
      (∑ n ∈ Finset.range N,
        (enlargedVisitEntrance hH hLE hlam hLam A c J s T P n univ).toReal) ≤
    9 * c.r ^ 2 / 16 *
      (∑ n ∈ Finset.range N,
        (((enlargedVisitEntrance hH hLE hlam hLam A c J s T P n).bind
          (enlargedActiveTerminalFamily hH hLE hlam hLam A c J T)) univ).toReal) +
    2 * Lam *
      (∑ n ∈ Finset.range N,
        (enlargedActivePiece hH hLE hlam hLam A c J s T P n univ).toReal) := by
  have h := Finset.sum_le_sum (s := Finset.range N) (fun n _ => by
    have : IsFiniteMeasure (enlargedActivePiece hH hLE hlam hLam A c J s T P n) :=
      enlargedActivePiece_isFiniteMeasure hH hLE hlam hLam A c J s T P hs hT n
    exact (enlargedQuadratic_entrance_lower_integral
      hH hLE hlam hLam A c J s T P hs hT n).trans
        ((enlargedQuadratic_entrance_green_identity
          hH hLE hlam hLam A c J s T P hs hT hJ n).le.trans
            (add_le_add (enlargedQuadratic_exit_integral_le_terminal_mass
              hH hLE hlam hLam A c J s T P hs hT hJ n)
                (visitCoefficient_integral_le hlam A
                  (enlargedActivePiece hH hLE hlam hLam A c J s T P n)))))
  simpa only [Finset.mul_sum, Finset.sum_add_distrib] using h

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

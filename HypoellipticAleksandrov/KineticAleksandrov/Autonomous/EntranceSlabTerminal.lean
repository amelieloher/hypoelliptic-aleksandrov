module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EntranceSlabFullSpace
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EntranceSlabIntegrated
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionTerminalDomination

/-! # Active-band terminal bound for starts in a time slab -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory HypoellipticAleksandrov

/-- Deleting starts outside a slab preserves the full-space active terminal bound. -/
theorem entranceSlab_partial_terminal_mass_le
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T a b : ℝ)
    (hT : 0 < T) (hb : 0 ≤ b) (hbT : b ≤ T) (hJ : closure c.active ⊆ J.carrier)
    (P : Point) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      (((enlargedVisitEntrance hH hLE hlam hLam A c J P.time (P.time + T) P n).restrict
        {p | p.time ∈ Ioc (P.time + a) (P.time + b)}).bind
          (enlargedActiveTerminalFamily hH hLE hlam hLam A c J (P.time + b))
            {q | q.velocity 0 ∈ c.active}).toReal) ≤
      S hH hLE hlam hLam A b (activeVelocityDatum c) (P.position 0, P.velocity 0) := by
  let gamma := enlargedVisitEntrance hH hLE hlam hLam A c J P.time (P.time + T) P
  let F := enlargedActiveTerminalFamily hH hLE hlam hLam A c J (P.time + b)
  let D : Set Point := {p | p.time ∈ Ioc (P.time + a) (P.time + b)}
  let B : Set Point := {q | q.velocity 0 ∈ c.active}
  let tm := fun n => ((gamma n).restrict D).bind F
  have hB : MeasurableSet B := isOpen_Ioo.measurableSet.preimage
    ((continuous_apply 0).comp continuous_velocity).measurable
  have hm : (∑ n ∈ Finset.range N, tm n) ≤
      enlargedFullSpaceTerminal hH hLE hlam hLam A P (P.time + b) := by
    calc
      _ ≤ ∑ n ∈ Finset.range N, (gamma n).bind F :=
        Finset.sum_le_sum fun n _ => entranceSlabTerminal_restrict_bind_le
          hH hLE hlam hLam A c J (P.time + b) (gamma n) D
      _ ≤ _ := enlarged_active_terminal_le_fullspace hH hLE hlam hLam A c J
        P.time (P.time + T) P le_rfl (by linarith) hJ N (P.time + b)
          (by linarith) (by linarith)
  have hr := ENNReal.toReal_mono
    (measure_ne_top (enlargedFullSpaceTerminal hH hLE hlam hLam A P (P.time + b)) B)
    (hm B)
  rw [visit_partial_real_mass tm N B hB] at hr
  have he := entranceSlab_fullSpaceTerminal_active hH hLE hlam hLam A c P b
  rw [he] at hr
  exact hr.trans_eq (activeVelocityDatum_action_eq hH hLE hlam hLam A c b hb
    (P.position 0, P.velocity 0)).symm

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

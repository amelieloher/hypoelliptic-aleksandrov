module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AutonomyTimeShift
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.Conservation

/-! # Time autonomy of the full-space kernel

Time translation is proved on classical solutions and then transferred by smooth tests.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set MeasureTheory
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

/-- Full-space state membership has no spatial restriction. -/
theorem autonomous_stateSet (t : ℝ) :
    evolutionStateSet autonomousWholeDomain (fun _ => 0) t = univ := by
  change movingDomain (wholeSpace 1) (fun _ => 0) t ×ˢ univ = univ
  rw [movingDomain_wholeSpace, univ_prod_univ]

/-- An ordered query after translating both times by the same amount. -/
def autonomousQueryShift (h : ℝ)
    (q : EvolutionQuery autonomousWholeDomain (fun _ => 0)) :
    EvolutionQuery autonomousWholeDomain (fun _ => 0) :=
  ⟨(q.1.1 + h, q.1.2.1 + h, q.1.2.2),
    by linarith [q.2.1], by rw [autonomous_stateSet]; trivial⟩

/-- Time translation leaves the entire full-space terminal measure unchanged. -/
theorem fullspace_kernel_timeShift {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E) (h : ℝ)
    (q : EvolutionQuery autonomousWholeDomain (fun _ => 0)) :
    E.2.master (autonomousQueryShift h q) = E.2.master q := by
  have : IsFiniteMeasure (E.2.master q) :=
    ⟨(E.2.mass_le_one q).trans_lt ENNReal.one_lt_top⟩
  have : IsFiniteMeasure (E.2.master (autonomousQueryShift h q)) :=
    ⟨(E.2.mass_le_one _).trans_lt ENNReal.one_lt_top⟩
  apply measure_eq_of_smooth_integral_eq isOpen_univ (by simp) (by simp)
  intro φ hφ hφc _hφU hφr
  let F := smoothTestDatum φ hφ hφr
  have hF (τ : ℝ) :
      IsSmoothCompactTerminalDatum autonomousWholeDomain (fun _ => 0) τ F :=
    ⟨hφ, hφc, by rw [autonomous_stateSet]; exact subset_univ _⟩
  obtain ⟨u, hu, hru, _⟩ := hE.1 (q.1.2.1 + h) F (hF _)
  obtain ⟨v, hv, hrv, hvuniq⟩ := hE.1 q.1.2.1 F (hF _)
  have hshift := fullspace_classical_timeShift h q.1.2.1 F u hu
  have hp : (⟨q.1.1, q.1.2.2.1, q.1.2.2.2⟩ : KineticPoint 1) ∈
      evolutionPastClosedCylinder autonomousWholeDomain (fun _ => 0) q.1.2.1 :=
    ⟨q.2.1, subset_closure q.2.2.1⟩
  have heq := hvuniq _ hshift hp
  let p : EvolutionState autonomousWholeDomain (fun _ => 0) q.1.1 :=
    ⟨q.1.2.2, q.2.2⟩
  let ph : EvolutionState autonomousWholeDomain (fun _ => 0) (q.1.1 + h) :=
    ⟨q.1.2.2, by rw [autonomous_stateSet]; trivial⟩
  have hrep (σ τ : ℝ) (hστ : σ ≤ τ)
      (s : EvolutionState autonomousWholeDomain (fun _ => 0) σ) :
      E.1 σ τ hστ (terminalStateDatum F) s =
        ∫ x, F x ∂E.2.master (evolutionQueryOfState _ _ σ τ hστ s) :=
    (hE.2.1 σ τ hστ s (terminalStateDatum F)).trans
      (integral_master_eq_fiber E.2 autonomousWholeDomain_measurable
        σ τ hστ s F F.measurable).symm
  have h1 := (hru (q.1.1 + h) (autonomousQueryShift h q).2.1 ph).trans
    (hrep _ _ _ ph)
  have h2 := (hrv q.1.1 q.2.1 p).trans (hrep _ _ _ p)
  exact h1.symm.trans (heq.trans h2)

/-- Composition holds for the supplied full-space operators on all bounded Borel data. -/
theorem fullspace_operator_composition {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (σ r τ : ℝ) (hσr : σ ≤ r) (hrτ : r ≤ τ) :
    E.1 σ τ (hσr.trans hrτ) = (E.1 σ r hσr).comp (E.1 r τ hrτ) :=
  realizes_composition autonomousWholeDomain_measurable
    (evolutionCoefficient A.a) (identityDrift 1) E.1 E.2 hE σ r τ hσr hrτ

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

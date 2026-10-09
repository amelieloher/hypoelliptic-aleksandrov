module

public import HypoellipticAleksandrov.Statements.TerminalEvolution
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Realization

/-!
# A realizing terminal evolution for a full Section 2 coefficient

Existence of the terminal evolution `(S,K)`. The terminal evolution theorem
`exists_terminalEvolution` (companion paper, Proposition 2.1), specialized to the whole space,
identity drift and zero moving curve
(case (W)), supplies a realization for every smooth symmetric full coefficient `B(σ,v,z)` with
everywhere Loewner bounds.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Assembly

open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

/-- Whole-space, identity-drift realization of the terminal evolution of a smooth symmetric full
coefficient with everywhere Loewner bounds. -/
theorem exists_realization {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ} (hlam : 0 < lam)
    (hLam : lam ≤ Lam) {B : FullKineticCoefficient d} (hB : IsSmoothFullKineticCoefficient B)
    (hBs : IsSymmetricFullKineticCoefficient B) (hell : HasEverywhereLoewnerBounds lam Lam B) :
    ∃ (S : TerminalOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
      (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))),
      RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d)) MeasurableSet.univ
        B (identityDrift d) S K := by
  have hb := identityDrift_bounds d
  obtain ⟨S, K, hc, -, -, -, -, hi, -, -, -, -, he, hcomp, -⟩ :=
    exists_terminalEvolution d hd lam Lam 1 1 hlam hLam one_pos le_rfl (wholeSpace d)
      (fun _ => 0) B (identityDrift d) (wholeSpace_admissible d) (zeroCurve_piecewiseC1 d)
      hB hBs hell (identityDrift_smooth d) hb.1 hb.2
  exact ⟨S, K, ⟨hc, hi, he, hcomp⟩⟩

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Assembly

module

import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TerminalPointValueLinear

/-!
# Comparison of a small-domain solution with a large-domain solution (domain domination ingredient)

Outside-context comparison.  Let `Ω'` (curve `γ'`) be a moving subdomain of `Ω` (curve `γ`) and let
`F ≥ 0` be a terminal datum.  If `u` solves the terminal problem on the large cylinder and `u'` on
the small one, then `u' ≤ u` on the small past closed cylinder.  Indeed `u ≥ 0` on the large
cylinder (comparison with `0 • u`), so `u' - u` is a subsolution of the small problem that is zero
at the terminal slice and nonpositive on the small lateral frontier; the
`growth_comparison` gives the sign.

* `IsClassicalTerminalSolution.nonneg_of_nonneg`: `F ≥ 0` gives `u ≥ 0`.
* `classical_le_of_subdomain`: the comparison.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set

variable {n : ℕ}

/-- A classical terminal solution with nonnegative datum is nonnegative on the past closed
cylinder. -/
theorem IsClassicalTerminalSolution.nonneg_of_nonneg {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    (hΩ : IsOpen Ω) (hγ : Continuous γ) {lam Lam : ℝ} (hlam : 0 < lam)
    {B : FullKineticCoefficient n} (hB : HasEverywhereLoewnerBounds lam Lam B) {Lb : ℝ}
    {b : PDE.Vec n → PDE.Vec n} (hb : HasEuclideanLipschitzDrift Lb b) {τ : ℝ}
    {F : BoundedBorel (EvolutionAmbientState n)} {u : KineticPoint n → ℝ}
    (hu : IsClassicalTerminalSolution Ω γ B b τ F u) (hF : ∀ q, 0 ≤ F q) :
    ∀ p ∈ evolutionPastClosedCylinder Ω γ τ, 0 ≤ u p := by
  intro p hp
  have h0 := IsClassicalTerminalSolution.smul hΩ hγ 0 hu
  have hle := IsClassicalTerminalSolution.le_of_le hΩ hγ hlam hB hb h0 hu
    (fun y z _ => by simpa using hF (y, z)) p hp
  simpa using hle

/-- A solution on a moving subdomain is dominated by the solution on the large domain with the
same nonnegative datum. -/
theorem classical_le_of_subdomain {Ω Ω' : Set (PDE.Vec n)} {γ γ' : ℝ → PDE.Vec n}
    (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω') (hγ : Continuous γ) (hγ' : Continuous γ')
    (hsub : ∀ σ, movingDomain Ω' γ' σ ⊆ movingDomain Ω γ σ) {lam Lam : ℝ} (hlam : 0 < lam)
    {B : FullKineticCoefficient n} (hB : HasEverywhereLoewnerBounds lam Lam B) {Lb : ℝ}
    {b : PDE.Vec n → PDE.Vec n} (hb : HasEuclideanLipschitzDrift Lb b) {τ : ℝ}
    {F : BoundedBorel (EvolutionAmbientState n)} {u u' : KineticPoint n → ℝ}
    (hu : IsClassicalTerminalSolution Ω γ B b τ F u)
    (hu' : IsClassicalTerminalSolution Ω' γ' B b τ F u') (hF : ∀ q, 0 ≤ F q) :
    ∀ p ∈ evolutionPastClosedCylinder Ω' γ' τ, u' p ≤ u p := by
  have hnn := hu.nonneg_of_nonneg hΩ hγ hlam hB hb hF
  have hcl : ∀ t, closure (movingDomain Ω' γ' t) ⊆ closure (movingDomain Ω γ t) :=
    fun t => closure_mono (hsub t)
  have hu0 := (isClassicalViscousTerminalSolution_zero_iff Ω γ B b τ F u).2 hu
  have hu0' := (isClassicalViscousTerminalSolution_zero_iff Ω' γ' B b τ F u').2 hu'
  have hslab' : ∀ a, movingClosedSlab Ω' γ' a τ ⊆ evolutionPastClosedCylinder Ω' γ' τ :=
    fun a p hp => ⟨hp.2.1, hp.2.2⟩
  have hslab : ∀ a, movingClosedSlab Ω' γ' a τ ⊆ evolutionPastClosedCylinder Ω γ τ :=
    fun a p hp => ⟨hp.2.1, hcl _ hp.2.2⟩
  have hact' : ∀ a, movingActiveSlab Ω' γ' a τ ⊆ evolutionPastOpenCylinder Ω' γ' τ :=
    fun a p hp => ⟨hp.2.1, hp.2.2⟩
  have hact : ∀ a, movingActiveSlab Ω' γ' a τ ⊆ evolutionPastOpenCylinder Ω γ τ :=
    fun a p hp => ⟨hp.2.1, hsub _ hp.2.2⟩
  obtain ⟨C', -, hC'⟩ := hu'.1
  obtain ⟨C, -, hC⟩ := hu.1
  intro p₀ hp₀
  have hp₀slab : p₀ ∈ movingClosedSlab Ω' γ' p₀.time τ := ⟨le_rfl, hp₀.1, hp₀.2⟩
  have hres := growth_comparison (a := p₀.time) (T := τ) (u := fun q => u' q - u q) hΩ' hγ'
    hlam hB hb le_rfl zero_le_one ?_ ?_ ?_ ?_ ?_ ?_ p₀ hp₀slab
  · linarith
  · refine ⟨C' + C, fun p hp => ?_⟩
    have h1 := hC' p (hslab' _ hp)
    have h2 := hC p (hslab _ hp)
    have := le_abs_self (u' p)
    have := neg_abs_le (u p)
    linarith
  · exact (hu0'.2.1.mono (hslab' _)).sub (hu0.2.1.mono (hslab _))
  · intro p hp
    exact (hu0'.isSliceRegularAt hΩ' hγ' (hact' _ hp)).sub
      (hu0.isSliceRegularAt hΩ hγ (hact _ hp))
  · intro p hp
    have hr' := hu0'.isSliceRegularAt hΩ' hγ' (hact' _ hp)
    have hr := hu0.isSliceRegularAt hΩ hγ (hact _ hp)
    rw [viscousTransportedOperator_sub hr' hr, hu0'.2.2.2.1 p (hact' _ hp),
      hu0.2.2.2.1 p (hact _ hp)]
    simp
  · intro p hp hpT
    have hterm' : p ∈ evolutionTerminalClosure Ω' γ' τ := ⟨hpT, hpT ▸ hp.2.2⟩
    have hterm : p ∈ evolutionTerminalClosure Ω γ τ := ⟨hpT, hcl _ (hpT ▸ hp.2.2)⟩
    show u' p - u p ≤ 0
    rw [hu0'.2.2.2.2.1 p hterm', hu0.2.2.2.2.1 p hterm]
    simp
  · intro p hp hfr
    have hlat' : p ∈ evolutionLateralFrontier Ω' γ' τ := ⟨hp.2.1, hfr⟩
    show u' p - u p ≤ 0
    rw [hu0'.2.2.2.2.2 p hlat']
    have := hnn p (hslab _ hp)
    linarith

end HypoellipticAleksandrov.KineticAleksandrov

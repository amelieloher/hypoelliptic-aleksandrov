module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.CompositionTraceWeight
import Mathlib.Tactic.Linarith

/-!
# Compact approximation of a genuine intermediate trace

Only the compact cutoff data are eligible inputs to classical terminal existence.
The trace itself is never passed to `hEx`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Function

/-- A strictly earlier classical slice has smooth compact interior approximants with
an arbitrarily small Euclidean weighted error and the same uniform bound. -/
theorem IsClassicalTerminalSolution.exists_compact_slice_approximation
    {n : ℕ} {Ω : Set (PDE.Vec n)} (hΩ : IsOpen Ω) {γ : ℝ → PDE.Vec n}
    {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    {τ r C ε : ℝ} {F : BoundedBorel (EvolutionAmbientState n)} {u : KineticPoint n → ℝ}
    (hu : IsClassicalTerminalSolution Ω γ B b τ F u) (hrτ : r < τ)
    (hC0 : 0 ≤ C) (hC : ∀ p ∈ evolutionPastClosedCylinder Ω γ τ, |u p| ≤ C)
    (hε : 0 < ε) :
    ∃ G : BoundedBorel (EvolutionAmbientState n),
      IsSmoothCompactTerminalDatum Ω γ r G ∧ (∀ x, |G x| ≤ C) ∧
      ∀ p ∈ evolutionTerminalClosure Ω γ r,
        |u p - G (p.position, p.velocity)| ≤ ε * (1 + radialSq p) := by
  let U := evolutionStateSet Ω γ r
  let f : EvolutionAmbientState n → ℝ := fun x => u ⟨r, x.1, x.2⟩
  let g := U.indicator f
  have hU : IsOpen U := (isOpen_movingDomain hΩ r).prod isOpen_univ
  have hg : Continuous g := hu.continuous_zeroExtended_slice hrτ.le
  have hgb : ∀ x, |g x| ≤ C := by
    intro x
    dsimp only [g]
    by_cases hx : x ∈ U
    · rw [indicator_of_mem hx]
      exact hC ⟨r, x.1, x.2⟩ ⟨hrτ.le, subset_closure hx.1⟩
    · rw [indicator_of_notMem hx, abs_zero]
      exact hC0
  obtain ⟨χ, hχ, hc, hs, hr, herr⟩ := exists_smooth_cutoff_weighted_error hU g
    (fun x => 1 + ‖x‖ ^ 2) hg (continuous_const.add (continuous_norm.pow 2))
    (fun x => le_add_of_nonneg_right (sq_nonneg _))
    isCompact_quadratic_weight_sublevel (fun x hx => indicator_of_notMem hx f) hgb hε
  have heq : (fun x => χ x * g x) = (fun x => χ x * f x) := by
    funext x
    dsimp only [g]
    by_cases hx : x ∈ U
    · rw [indicator_of_mem hx]
    · have hz : χ x = 0 := notMem_support.mp
        (fun hxχ => hx (hs (subset_closure hxχ)))
      rw [hz, zero_mul, zero_mul]
  have hprod : ContDiff ℝ (⊤ : ℕ∞) (fun x => χ x * g x) := by
    rw [heq]
    exact contDiff_mul_of_tsupport_subset hU hχ (hu.contDiffOn_slice hrτ) hs
  have hbound : ∀ x, |χ x * g x| ≤ C := by
    intro x
    rw [abs_mul, abs_of_nonneg (hr x).1]
    exact (mul_le_mul_of_nonneg_right (hr x).2 (abs_nonneg _)).trans
      (by simpa only [one_mul] using hgb x)
  let G : BoundedBorel (EvolutionAmbientState n) :=
    ⟨fun x => χ x * g x, hprod.continuous.measurable, ⟨C, hC0, hbound⟩⟩
  refine ⟨G, ⟨hprod, hc.mul_right, tsupport_mul_subset_left.trans hs⟩, hbound, ?_⟩
  intro p hp
  have hgp : g (p.position, p.velocity) = u p := by
    dsimp only [g]
    by_cases hx : (p.position, p.velocity) ∈ U
    · rw [indicator_of_mem hx]
      change u ⟨r, p.position, p.velocity⟩ = u p
      congr 1
      exact KineticPoint.ext hp.1.symm rfl rfl
    · have hnot : p.position ∉ movingDomain Ω γ r :=
        fun hy => hx ⟨hy, mem_univ _⟩
      have hfr : p.position ∈ frontier (movingDomain Ω γ r) := by
        rw [(isOpen_movingDomain hΩ r).frontier_eq]
        exact ⟨hp.2, hnot⟩
      rw [indicator_of_notMem hx]
      exact (hu.2.2.2.2.2 p ⟨hp.1.trans_le hrτ.le, hp.1 ▸ hfr⟩).symm
  have hh := herr (p.position, p.velocity)
  rw [hgp] at hh
  have hw := quadratic_state_weight_le_radial r (p.position, p.velocity)
  have hpident : (⟨r, p.position, p.velocity⟩ : KineticPoint n) = p :=
    KineticPoint.ext hp.1.symm rfl rfl
  rw [hpident] at hw
  change |u p - χ (p.position, p.velocity) * g (p.position, p.velocity)| ≤ _
  rw [hgp]
  exact hh.trans (mul_le_mul_of_nonneg_left hw hε.le)

end HypoellipticAleksandrov.KineticAleksandrov

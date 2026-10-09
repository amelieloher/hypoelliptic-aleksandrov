module

import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.KineticAleksandrov.EvolutionProblem
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonLinear
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonNodes

/-!
# The point value of the terminal evolution

Companion paper, Proposition 2.1 (kernels): at a fixed starting point the map
`F ↦ u(σ, y, z)` is well defined on smooth compactly supported terminal data.

The classical existence theorem (`exists_classical_terminalSolution`, proved elsewhere)
enters only through the premise `ClassicalTerminalExistence`, which is exactly its
conclusion; the premise is discharged by that theorem.

* `ClassicalTerminalExistence`: the classical existence statement as a `Prop`.
* `exists_unique_terminalValue`: existence from the premise and uniqueness by comparison.
* `terminalValue`: the unique value, chosen from the `∃!` statement.
* `terminalValue_spec`, `terminalValue_eq_of_solution`: the full characterization.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set

/-- Premise stating the conclusion of
`exists_classical_terminalSolution` (classical terminal solution for every smooth compactly
supported terminal datum, with the global bound by every uniform bound on the datum, and
uniqueness on the past closed cylinder).  It supplies the existence half of the statement below and
is discharged by that theorem. -/
def ClassicalTerminalExistence {n : ℕ} (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n)
    (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n) : Prop :=
  ∀ (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n)),
    IsSmoothCompactTerminalDatum Ω γ τ F →
    ∃ u : KineticPoint n → ℝ,
      IsClassicalTerminalSolution Ω γ B b τ F u ∧
      (∀ C : ℝ, 0 ≤ C → (∀ q, |F q| ≤ C) →
        ∀ p ∈ evolutionPastClosedCylinder Ω γ τ, |u p| ≤ C) ∧
      (∀ v : KineticPoint n → ℝ,
        IsClassicalTerminalSolution Ω γ B b τ F v →
          EqOn v u (evolutionPastClosedCylinder Ω γ τ))

section Outside

variable {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
  {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n} {τ : ℝ}

/-- Sums of classical terminal solutions solve the problem for the summed data. -/
theorem IsClassicalTerminalSolution.add (hΩ : IsOpen Ω) (hγ : Continuous γ)
    {F G : BoundedBorel (EvolutionAmbientState n)} {u v : KineticPoint n → ℝ}
    (hu : IsClassicalTerminalSolution Ω γ B b τ F u)
    (hv : IsClassicalTerminalSolution Ω γ B b τ G v) :
    IsClassicalTerminalSolution Ω γ B b τ (F + G) (fun q => u q + v q) := by
  have hu' := (isClassicalViscousTerminalSolution_zero_iff Ω γ B b τ F u).2 hu
  have hv' := (isClassicalViscousTerminalSolution_zero_iff Ω γ B b τ G v).2 hv
  refine ((isClassicalViscousTerminalSolution_zero_iff Ω γ B b τ (F + G) _).1 ?_)
  obtain ⟨⟨C₁, hC₁0, hC₁⟩, hc₁, hs₁, hop₁, ht₁, hl₁⟩ := hu'
  obtain ⟨⟨C₂, hC₂0, hC₂⟩, hc₂, hs₂, hop₂, ht₂, hl₂⟩ := hv'
  refine ⟨⟨C₁ + C₂, add_nonneg hC₁0 hC₂0, fun p hp => ?_⟩, hc₁.add hc₂, hs₁.add hs₂, ?_, ?_, ?_⟩
  · exact (abs_add_le _ _).trans (add_le_add (hC₁ p hp) (hC₂ p hp))
  · intro p hp
    have h1 := IsClassicalViscousTerminalSolution.isSliceRegularAt hΩ hγ
      ⟨⟨C₁, hC₁0, hC₁⟩, hc₁, hs₁, hop₁, ht₁, hl₁⟩ hp
    have h2 := IsClassicalViscousTerminalSolution.isSliceRegularAt hΩ hγ
      ⟨⟨C₂, hC₂0, hC₂⟩, hc₂, hs₂, hop₂, ht₂, hl₂⟩ hp
    rw [viscousTransportedOperator_add h1 h2, hop₁ p hp, hop₂ p hp]
    simp
  · intro p hp
    simp only [BoundedBorel.add_apply]
    rw [ht₁ p hp, ht₂ p hp]
  · intro p hp
    show u p + v p = 0
    rw [hl₁ p hp, hl₂ p hp]
    simp

/-- Real multiples of classical terminal solutions solve the problem for the scaled data. -/
theorem IsClassicalTerminalSolution.smul (hΩ : IsOpen Ω) (hγ : Continuous γ) (c : ℝ)
    {F : BoundedBorel (EvolutionAmbientState n)} {u : KineticPoint n → ℝ}
    (hu : IsClassicalTerminalSolution Ω γ B b τ F u) :
    IsClassicalTerminalSolution Ω γ B b τ (c • F) (fun q => c * u q) := by
  have hu' := (isClassicalViscousTerminalSolution_zero_iff Ω γ B b τ F u).2 hu
  refine ((isClassicalViscousTerminalSolution_zero_iff Ω γ B b τ (c • F) _).1 ?_)
  obtain ⟨⟨C, hC0, hC⟩, hc, hs, hop, ht, hl⟩ := hu'
  refine ⟨⟨|c| * C, mul_nonneg (abs_nonneg c) hC0, fun p hp => ?_⟩,
    continuousOn_const.mul hc, contDiffOn_const.mul hs, ?_, ?_, ?_⟩
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hC p hp) (abs_nonneg c)
  · intro p hp
    have h1 := IsClassicalViscousTerminalSolution.isSliceRegularAt hΩ hγ
      ⟨⟨C, hC0, hC⟩, hc, hs, hop, ht, hl⟩ hp
    rw [viscousTransportedOperator_const_mul c h1, hop p hp]
    simp
  · intro p hp
    simp only [BoundedBorel.smul_apply, smul_eq_mul]
    rw [ht p hp]
  · intro p hp
    show c * u p = 0
    rw [hl p hp]
    simp

/-- Two classical terminal solutions with the same datum agree on the past closed cylinder. -/
theorem IsClassicalTerminalSolution.eqOn_of_lam {lam Lam : ℝ} (hΩ : IsOpen Ω)
    (hγ : Continuous γ) (hlam : 0 < lam) (hB : HasEverywhereLoewnerBounds lam Lam B)
    {Lb : ℝ} (hb : HasEuclideanLipschitzDrift Lb b)
    {F : BoundedBorel (EvolutionAmbientState n)} {u v : KineticPoint n → ℝ}
    (hu : IsClassicalTerminalSolution Ω γ B b τ F u)
    (hv : IsClassicalTerminalSolution Ω γ B b τ F v) :
    EqOn u v (evolutionPastClosedCylinder Ω γ τ) := fun _ hp =>
  classical_unique hΩ hγ hlam hB hb le_rfl zero_le_one
    ((isClassicalViscousTerminalSolution_zero_iff Ω γ B b τ F u).2 hu)
    ((isClassicalViscousTerminalSolution_zero_iff Ω γ B b τ F v).2 hv) _ hp

/-- A fixed-time source state at an earlier time lies in the past closed cylinder. -/
theorem mk_mem_evolutionPastClosedCylinder {σ : ℝ} (hστ : σ ≤ τ)
    (p : EvolutionState Ω γ σ) :
    (⟨σ, p.1.1, p.1.2⟩ : KineticPoint n) ∈ evolutionPastClosedCylinder Ω γ τ :=
  ⟨hστ, subset_closure p.2.1⟩

end Outside

section EvolutionData

variable (n : ℕ) (hn : 1 ≤ n) (lam Lam m L_b : ℝ)
variable (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
variable (hm : 0 < m) (hmLb : m ≤ L_b)
variable (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n)
variable (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n)
variable (hΩ : IsAdmissibleEvolutionDomain Ω)
variable (hγ : IsContinuousPiecewiseC1 γ)
variable (hB_smooth : IsSmoothFullKineticCoefficient B)
variable (hB_symm : IsSymmetricFullKineticCoefficient B)
variable (hB_ell : HasEverywhereLoewnerBounds lam Lam B)
variable (hb_smooth : IsSmoothDrift b)
variable (hb_lipschitz : HasEuclideanLipschitzDrift L_b b)
variable (hb_coercive : HasUnitDirectionDriftCoercivity m b)
variable (hEx : ClassicalTerminalExistence Ω γ B b)
include hn hlam hlamLam hm hmLb hΩ hγ hB_smooth hB_symm hB_ell
include hb_smooth hb_lipschitz hb_coercive hEx

/-- The point value of the terminal evolution at the source state `p` is well defined:
there is exactly one real number which is the value at `(σ, p)` of some classical terminal
solution with datum `F`. -/
theorem exists_unique_terminalValue
    (σ τ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω γ σ)
    (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum Ω γ τ F) :
    ∃! x : ℝ, ∃ u : KineticPoint n → ℝ,
      IsClassicalTerminalSolution Ω γ B b τ F u ∧
      u ⟨σ, p.1.1, p.1.2⟩ = x := by
  obtain ⟨u, hu, -, -⟩ := hEx τ F hF
  refine ⟨u ⟨σ, p.1.1, p.1.2⟩, ⟨u, hu, rfl⟩, ?_⟩
  rintro x ⟨v, hv, rfl⟩
  exact IsClassicalTerminalSolution.eqOn_of_lam
    (isOpen_of_isAdmissibleEvolutionDomain hΩ) hγ.1 hlam hB_ell hb_lipschitz hv hu
    (mk_mem_evolutionPastClosedCylinder hστ p)

/-- The unique real value `S σ τ hστ p F hF` of the terminal evolution at the source
state `p`, chosen from the `∃!` statement `exists_unique_terminalValue`. -/
def terminalValue
    (σ τ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω γ σ)
    (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum Ω γ τ F) : ℝ :=
  (exists_unique_terminalValue n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ p F hF).choose

local notation "S" => terminalValue n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx

/-- The chosen value is the value of some classical terminal solution. -/
theorem terminalValue_spec
    (σ τ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω γ σ)
    (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum Ω γ τ F) :
    ∃ u : KineticPoint n → ℝ,
      IsClassicalTerminalSolution Ω γ B b τ F u ∧
      u ⟨σ, p.1.1, p.1.2⟩ = S σ τ hστ p F hF :=
  (exists_unique_terminalValue n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
    σ τ hστ p F hF).choose_spec.1

/-- The chosen value equals the value of every classical terminal solution. -/
theorem terminalValue_eq_of_solution
    (σ τ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω γ σ)
    (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum Ω γ τ F)
    (u : KineticPoint n → ℝ)
    (hu : IsClassicalTerminalSolution Ω γ B b τ F u) :
    S σ τ hστ p F hF = u ⟨σ, p.1.1, p.1.2⟩ :=
  ((exists_unique_terminalValue n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
    σ τ hστ p F hF).choose_spec.2 _ ⟨u, hu, rfl⟩).symm

end EvolutionData

end HypoellipticAleksandrov.KineticAleksandrov

module

import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TerminalPointValue

/-!
# Linearity, positivity and bounds of the terminal point value

Consequences of the unique characterization of `terminalValue` for smooth compactly
supported data: the value is additive, homogeneous, nonnegative on nonnegative data, bounded
by every uniform bound of the datum, equal to the datum at equal times, and continuous in the
source state.  All proofs identify `terminalValue` with the value of a supplied classical
solution (`terminalValue_eq_of_solution`) and use comparison.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set

section Outside

variable {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
  {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n} {τ : ℝ}

/-- Sums of smooth compactly supported terminal data are smooth compactly supported data. -/
theorem IsSmoothCompactTerminalDatum.add {F G : BoundedBorel (EvolutionAmbientState n)}
    (hF : IsSmoothCompactTerminalDatum Ω γ τ F) (hG : IsSmoothCompactTerminalDatum Ω γ τ G) :
    IsSmoothCompactTerminalDatum Ω γ τ (F + G) :=
  ⟨hF.1.add hG.1, hF.2.1.add hG.2.1,
    (tsupport_add (F : EvolutionAmbientState n → ℝ) G).trans (union_subset hF.2.2 hG.2.2)⟩

/-- Real multiples of smooth compactly supported terminal data are such data. -/
theorem IsSmoothCompactTerminalDatum.smul (c : ℝ) {F : BoundedBorel (EvolutionAmbientState n)}
    (hF : IsSmoothCompactTerminalDatum Ω γ τ F) :
    IsSmoothCompactTerminalDatum Ω γ τ (c • F) :=
  ⟨contDiff_const.smul hF.1, hF.2.1.smul_left,
    (tsupport_smul_subset_right (fun _ => c) (F : EvolutionAmbientState n → ℝ)).trans hF.2.2⟩

/-- Comparison of classical terminal solutions with ordered data. -/
theorem IsClassicalTerminalSolution.le_of_le {lam Lam : ℝ} (hΩ : IsOpen Ω)
    (hγ : Continuous γ) (hlam : 0 < lam) (hB : HasEverywhereLoewnerBounds lam Lam B)
    {Lb : ℝ} (hb : HasEuclideanLipschitzDrift Lb b)
    {F₁ F₂ : BoundedBorel (EvolutionAmbientState n)} {u₁ u₂ : KineticPoint n → ℝ}
    (h₁ : IsClassicalTerminalSolution Ω γ B b τ F₁ u₁)
    (h₂ : IsClassicalTerminalSolution Ω γ B b τ F₂ u₂)
    (hF : ∀ y z, y ∈ closure (movingDomain Ω γ τ) → F₁ (y, z) ≤ F₂ (y, z)) :
    ∀ p ∈ evolutionPastClosedCylinder Ω γ τ, u₁ p ≤ u₂ p :=
  classical_comparison hΩ hγ hlam hB hb le_rfl zero_le_one
    ((isClassicalViscousTerminalSolution_zero_iff Ω γ B b τ F₁ u₁).2 h₁)
    ((isClassicalViscousTerminalSolution_zero_iff Ω γ B b τ F₂ u₂).2 h₂) hF

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

local notation "S" => terminalValue n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx

/-- The terminal point value is additive in the datum. -/
theorem terminalValue_add
    (σ τ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω γ σ)
    (F G : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum Ω γ τ F) (hG : IsSmoothCompactTerminalDatum Ω γ τ G) :
    S σ τ hστ p (F + G) (hF.add hG) = S σ τ hστ p F hF + S σ τ hστ p G hG := by
  obtain ⟨u, hu, hu'⟩ := terminalValue_spec n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ p F hF
  obtain ⟨v, hv, hv'⟩ := terminalValue_spec n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ p G hG
  rw [terminalValue_eq_of_solution n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ p (F + G)
    (hF.add hG) _ (IsClassicalTerminalSolution.add
      (isOpen_of_isAdmissibleEvolutionDomain hΩ) hγ.1 hu hv)]
  simp only [hu', hv']

/-- The terminal point value is homogeneous in the datum. -/
theorem terminalValue_smul
    (σ τ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω γ σ) (c : ℝ)
    (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum Ω γ τ F) :
    S σ τ hστ p (c • F) (hF.smul c) = c * S σ τ hστ p F hF := by
  obtain ⟨u, hu, hu'⟩ := terminalValue_spec n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ p F hF
  rw [terminalValue_eq_of_solution n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ p (c • F)
    (hF.smul c) _ (IsClassicalTerminalSolution.smul
      (isOpen_of_isAdmissibleEvolutionDomain hΩ) hγ.1 c hu)]
  simp only [hu']

/-- The terminal point value is nonnegative on nonnegative data. -/
theorem terminalValue_nonneg
    (σ τ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω γ σ)
    (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum Ω γ τ F) (hpos : ∀ q, 0 ≤ F q) :
    0 ≤ S σ τ hστ p F hF := by
  obtain ⟨u, hu, hu'⟩ := terminalValue_spec n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ p F hF
  have h0 := IsClassicalTerminalSolution.smul (isOpen_of_isAdmissibleEvolutionDomain hΩ)
    hγ.1 0 hu
  have hle := IsClassicalTerminalSolution.le_of_le (isOpen_of_isAdmissibleEvolutionDomain hΩ)
    hγ.1 hlam hB_ell hb_lipschitz h0 hu (fun y z _ => by
      simpa using hpos (y, z)) _ (mk_mem_evolutionPastClosedCylinder hστ p)
  rw [← hu']
  simpa using hle

/-- The terminal point value is bounded by every uniform bound of the datum. -/
theorem abs_terminalValue_le
    (σ τ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω γ σ)
    (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum Ω γ τ F) (C : ℝ) (hC : 0 ≤ C)
    (hFC : ∀ q, |F q| ≤ C) :
    |S σ τ hστ p F hF| ≤ C := by
  obtain ⟨u, hu, hbd, -⟩ := hEx τ F hF
  rw [terminalValue_eq_of_solution n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ p F hF u hu]
  exact hbd C hC hFC _ (mk_mem_evolutionPastClosedCylinder hστ p)

/-- At equal times the terminal point value is the datum itself. -/
theorem terminalValue_self
    (σ : ℝ) (p : EvolutionState Ω γ σ)
    (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum Ω γ σ F) :
    S σ σ le_rfl p F hF = F p.1 := by
  obtain ⟨u, hu, -, -⟩ := hEx σ F hF
  rw [terminalValue_eq_of_solution n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ σ le_rfl p F hF
    u hu]
  exact hu.2.2.2.2.1 ⟨σ, p.1.1, p.1.2⟩ ⟨rfl, subset_closure p.2.1⟩

/-- The terminal point value is continuous in the source state. -/
theorem continuous_terminalValue_source
    (σ τ : ℝ) (hστ : σ ≤ τ)
    (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum Ω γ τ F) :
    Continuous (fun p : EvolutionState Ω γ σ => S σ τ hστ p F hF) := by
  obtain ⟨u, hu, -, -⟩ := hEx τ F hF
  have hfun : (fun p : EvolutionState Ω γ σ => S σ τ hστ p F hF) =
      fun p => u ⟨σ, p.1.1, p.1.2⟩ := by
    funext p
    exact terminalValue_eq_of_solution n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ p F hF
      u hu
  rw [hfun]
  have hm : Continuous (fun p : EvolutionState Ω γ σ =>
      (⟨σ, p.1.1, p.1.2⟩ : KineticPoint n)) :=
    KineticPoint.continuous_mk continuous_const
      (continuous_fst.comp continuous_subtype_val) (continuous_snd.comp continuous_subtype_val)
  exact hu.2.1.comp_continuous hm (fun p => mk_mem_evolutionPastClosedCylinder hστ p)

end EvolutionData

end HypoellipticAleksandrov.KineticAleksandrov

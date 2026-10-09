module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TerminalFunctionalProbe
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TerminalPointValueLinear

/-!
# The positive terminal functional on `C_c` of the open fiber

Companion paper, Proposition 2.1 (kernels): at a fixed starting point `F ↦ u(σ, v, z)` is a
positive functional on `C_c(Ω_τ × ℝᵈ)` of norm at most one.

The point value `terminalValue` is a linear functional on the space of smooth compactly
supported probes, bounded by the sup norm and nonnegative on nonnegative probes.  The abstract
extension principle of `TerminalFunctionalExtension` (Hahn–Banach plus an approximate square
root) extends it to a positive functional on `C_c`.  There is no norm instance on
`C_c(X, ℝ)` in Mathlib, so the norm bound `|ℓ f| ≤ ‖f‖` is stated in the equivalent form
`|ℓ f| ≤ c` whenever `0 ≤ c` and `|f x| ≤ c` for all `x`.

* `exists_unique_terminalFunctional`: the terminal functional.
* `terminalFunctional`: the unique functional, chosen from the `∃!` statement.
* `terminalFunctional_spec`, `terminalFunctional_eq_of_spec`: its characterization.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set
open scoped CompactlySupported

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
local notation "S_add" => terminalValue_add n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
local notation "S_smul" => terminalValue_smul n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
local notation "S_nonneg" => terminalValue_nonneg n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
local notation "S_abs_le" => abs_terminalValue_le n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx

/-- The terminal point value depends only on the datum, not on the smoothness proof or the
presentation of the datum. -/
theorem terminalValue_congr
    (σ τ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω γ σ)
    {F G : BoundedBorel (EvolutionAmbientState n)} (h : F = G)
    (hF : IsSmoothCompactTerminalDatum Ω γ τ F) (hG : IsSmoothCompactTerminalDatum Ω γ τ G) :
    S σ τ hστ p F hF = S σ τ hστ p G hG := by
  subst h
  rfl

/-- The terminal point value as a linear functional on smooth compactly supported probes. -/
def terminalProbeValue (σ τ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω γ σ) :
    terminalProbeSubmodule Ω γ τ →ₗ[ℝ] ℝ where
  toFun F := S σ τ hστ p (terminalProbeDatum F) F.2
  map_add' F G := by
    refine (terminalValue_congr n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ p
      (BoundedBorel.ext fun _ => rfl) (terminalProbeDatum_isSmoothCompact (F + G))
      ((terminalProbeDatum_isSmoothCompact F).add
        (terminalProbeDatum_isSmoothCompact G))).trans ?_
    exact S_add σ τ hστ p _ _ (terminalProbeDatum_isSmoothCompact F)
      (terminalProbeDatum_isSmoothCompact G)
  map_smul' c F := by
    refine (terminalValue_congr n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ p
      (F := terminalProbeDatum (c • F)) (G := c • terminalProbeDatum F)
      (BoundedBorel.ext fun _ => rfl) (terminalProbeDatum_isSmoothCompact (c • F))
      ((terminalProbeDatum_isSmoothCompact F).smul c)).trans ?_
    exact S_smul σ τ hστ p c _ (terminalProbeDatum_isSmoothCompact F)

/-- For each source state, the terminal point value extends uniquely to a positive
linear functional on `C_c` of the open terminal fiber, bounded by the sup norm. -/
theorem exists_unique_terminalFunctional
    (σ τ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω γ σ) :
    ∃! ℓ : C_c(EvolutionState Ω γ τ, ℝ) →ₚ[ℝ] ℝ,
      (∀ (f : C_c(EvolutionState Ω γ τ, ℝ)) (c : ℝ), 0 ≤ c → (∀ x, |f x| ≤ c) →
        |ℓ f| ≤ c) ∧
      ∀ (F : BoundedBorel (EvolutionAmbientState n))
        (hF : IsSmoothCompactTerminalDatum Ω γ τ F)
        (f : C_c(EvolutionState Ω γ τ, ℝ)),
        (∀ q, f q = F q.1) → ℓ f = S σ τ hστ p F hF := by
  have hΩo := isOpen_of_isAdmissibleEvolutionDomain hΩ
  obtain ⟨ℓ, hbd, hℓ⟩ := exists_positive_extension_of_dense
    (terminalProbeCcLinear (Ω := Ω) (γ := γ) (τ := τ))
    (terminalProbeValue n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ p)
    (fun F c hc h => S_abs_le σ τ hστ p _ (terminalProbeDatum_isSmoothCompact F) c hc
      (terminalProbe_abs_le hc h))
    (fun F h => S_nonneg σ τ hστ p _ (terminalProbeDatum_isSmoothCompact F)
      (terminalProbe_nonneg h))
    exists_terminalProbe_sq
    (fun f ε hε => exists_terminalProbe_close hΩo f ε hε)
  have hprobe : ∀ (F : BoundedBorel (EvolutionAmbientState n))
      (hF : IsSmoothCompactTerminalDatum Ω γ τ F) (f : C_c(EvolutionState Ω γ τ, ℝ)),
      (∀ q, f q = F q.1) → ℓ f = S σ τ hστ p F hF := by
    intro F hF f hf
    have hfeq : f = terminalProbeCcLinear (terminalProbeOfDatum F hF) :=
      CompactlySupportedContinuousMap.ext fun x => hf x
    rw [hfeq, hℓ]
    exact terminalValue_congr n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ p
      (terminalProbeDatum_ofDatum F hF) (terminalProbeDatum_isSmoothCompact _) hF
  refine ⟨ℓ, ⟨hbd, hprobe⟩, ?_⟩
  rintro ℓ' ⟨hbd', hprobe'⟩
  have hlin : ℓ'.toLinearMap = ℓ.toLinearMap := by
    refine eq_of_bounded_of_dense (terminalProbeCcLinear (Ω := Ω) (γ := γ) (τ := τ))
      ℓ'.toLinearMap ℓ.toLinearMap hbd' hbd (fun F => ?_)
      (fun f ε hε => exists_terminalProbe_close hΩo f ε hε)
    have h1 := hprobe' (terminalProbeDatum F) F.2 (terminalProbeCcLinear F) (fun q => rfl)
    have h2 := hprobe (terminalProbeDatum F) F.2 (terminalProbeCcLinear F) (fun q => rfl)
    exact h1.trans h2.symm
  exact PositiveLinearMap.ext fun f => LinearMap.congr_fun hlin f

/-- The unique positive terminal functional at the source state `p`, chosen from the
`∃!` statement `exists_unique_terminalFunctional`. -/
def terminalFunctional (σ τ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω γ σ) :
    C_c(EvolutionState Ω γ τ, ℝ) →ₚ[ℝ] ℝ :=
  (exists_unique_terminalFunctional n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ p).choose

/-- The chosen functional is sup-norm bounded and reproduces the point value on
every smooth compactly supported probe. -/
theorem terminalFunctional_spec
    (σ τ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω γ σ) :
    (∀ (f : C_c(EvolutionState Ω γ τ, ℝ)) (c : ℝ), 0 ≤ c → (∀ x, |f x| ≤ c) →
      |terminalFunctional n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
        hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ p f| ≤ c) ∧
      ∀ (F : BoundedBorel (EvolutionAmbientState n))
        (hF : IsSmoothCompactTerminalDatum Ω γ τ F)
        (f : C_c(EvolutionState Ω γ τ, ℝ)),
        (∀ q, f q = F q.1) →
          terminalFunctional n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
            hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ p f =
            S σ τ hστ p F hF :=
  (exists_unique_terminalFunctional n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ p).choose_spec.1

/-- Any positive functional with the two characterizing properties is the
chosen one. -/
theorem terminalFunctional_eq_of_spec
    (σ τ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω γ σ)
    (ℓ : C_c(EvolutionState Ω γ τ, ℝ) →ₚ[ℝ] ℝ)
    (hbd : ∀ (f : C_c(EvolutionState Ω γ τ, ℝ)) (c : ℝ), 0 ≤ c → (∀ x, |f x| ≤ c) →
      |ℓ f| ≤ c)
    (hprobe : ∀ (F : BoundedBorel (EvolutionAmbientState n))
      (hF : IsSmoothCompactTerminalDatum Ω γ τ F) (f : C_c(EvolutionState Ω γ τ, ℝ)),
      (∀ q, f q = F q.1) → ℓ f = S σ τ hστ p F hF) :
    ℓ = terminalFunctional n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ p :=
  (exists_unique_terminalFunctional n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ p).unique
    ⟨hbd, hprobe⟩ (terminalFunctional_spec n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ p)

end EvolutionData

end HypoellipticAleksandrov.KineticAleksandrov

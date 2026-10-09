module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.FixedFiberMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TranslationCovarianceSolution

/-!
# Translation covariance of the terminal kernel

Companion paper, Proposition 2.1 (domain covariance), translation half.  Assume that `B` does
not depend on the transported coordinate (`hBz`).  Then shifting a smooth terminal solution in
`z` commutes with the evolution, so the terminal point value is shift-invariant, the terminal
measures are intertwined by the ambient shift (by uniqueness of the terminal measures), and so are
the fixed-time fiber kernels.  Everything is proved for the one terminal family `μ` of terminal
measures.

* `terminalValue_shift`: `S σ τ p (F ∘ shift) = S σ τ (shift p) F`.
* `terminalMeasure_shift`: `map shift (μ (σ, τ, p)) = μ (σ, τ, shift p)` (ambient).
* `terminalFiberKernel_translation`: the fiber-kernel form `map shift (κ σ τ p) = κ σ τ (shift p)`.
* `terminalKernel_translation_of_master_eq`: the translation covariance statement for every moving
  fiber kernel `K` whose master measures are the `μ q`; the master kernel `K₀` is such a kernel by
  definition.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic MeasureTheory Set
open scoped ENNReal ProbabilityTheory

section Outside

variable {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n} {τ : ℝ}

/-- The transported-coordinate shift of a fiber state is Borel. -/
theorem measurable_evolutionStateShift' (σ : ℝ) (h : PDE.Vec n) :
    Measurable (evolutionStateShift Ω γ σ h) :=
  ((measurable_ambientShift h).comp measurable_subtype_coe).subtype_mk

/-- The preimage of the terminal fiber under the ambient shift is the terminal fiber. -/
theorem preimage_ambientShift_evolutionStateSet (h : PDE.Vec n) :
    evolutionAmbientStateShift h ⁻¹' evolutionStateSet Ω γ τ = evolutionStateSet Ω γ τ := by
  ext x
  simp only [evolutionStateSet, evolutionAmbientStateShift, mem_preimage, mem_prod, mem_univ,
    and_true]

/-- Pulling back along the fiber inclusion intertwines the ambient and the fiber shift. -/
theorem comap_map_ambientShift (hU : MeasurableSet (evolutionStateSet Ω γ τ))
    (h : PDE.Vec n) (ν : Measure (EvolutionAmbientState n)) :
    Measure.comap ((↑) : EvolutionState Ω γ τ → EvolutionAmbientState n)
        (ν.map (evolutionAmbientStateShift h)) =
      (Measure.comap ((↑) : EvolutionState Ω γ τ → EvolutionAmbientState n) ν).map
        (evolutionStateShift Ω γ τ h) := by
  have he := MeasurableEmbedding.subtype_coe hU
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply (measurable_evolutionStateShift' τ h) hA, he.comap_apply, he.comap_apply,
    Measure.map_apply (measurable_ambientShift h) (he.measurableSet_image.2 hA)]
  congr 1
  ext x
  constructor
  · rintro ⟨a, ha, hax⟩
    have hxU : x ∈ evolutionStateSet Ω γ τ := by
      have : evolutionAmbientStateShift h x ∈ evolutionStateSet Ω γ τ := hax ▸ a.2
      rwa [← mem_preimage, preimage_ambientShift_evolutionStateSet] at this
    refine ⟨⟨x, hxU⟩, ?_, rfl⟩
    show evolutionStateShift Ω γ τ h ⟨x, hxU⟩ ∈ A
    have : evolutionStateShift Ω γ τ h ⟨x, hxU⟩ = a := Subtype.ext hax.symm
    rwa [this]
  · rintro ⟨a, ha, rfl⟩
    exact ⟨evolutionStateShift Ω γ τ h a, ha, rfl⟩

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
local notation "μ" => terminalMeasure n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
local notation "κ" => terminalFiberKernel n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx

/-- The terminal point value is invariant under shifting the transported coordinate of both the
source and the datum. -/
theorem terminalValue_shift
    (hBz : ∀ (σ : ℝ) (y z z' : PDE.Vec n), B σ y z = B σ y z')
    (σ τ : ℝ) (hστ : σ ≤ τ) (h : PDE.Vec n) (p : EvolutionState Ω γ σ)
    (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum Ω γ τ F) :
    S σ τ hστ p (terminalDatumShift h F) (hF.shift h) =
      S σ τ hστ (evolutionStateShift Ω γ σ h p) F hF := by
  obtain ⟨u, hu, hu'⟩ := terminalValue_spec n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ
    (evolutionStateShift Ω γ σ h p) F hF
  rw [terminalValue_eq_of_solution n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ p _
    (hF.shift h) _ (hu.velocityShift hBz h), ← hu']
  rfl

/-- The ambient push-forward of the terminal measure along the shift of the transported coordinate
is the terminal measure of the shifted source. -/
theorem terminalMeasure_shift
    (hBz : ∀ (σ : ℝ) (y z z' : PDE.Vec n), B σ y z = B σ y z')
    (σ τ : ℝ) (hστ : σ ≤ τ) (h : PDE.Vec n) (p : EvolutionState Ω γ σ) :
    (μ (evolutionQueryOfState Ω γ σ τ hστ p)).map (evolutionAmbientStateShift h) =
      μ (evolutionQueryOfState Ω γ σ τ hστ (evolutionStateShift Ω γ σ h p)) := by
  have hspec := terminalMeasure_spec n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
    (evolutionQueryOfState Ω γ σ τ hστ p)
  have hsh := measurable_ambientShift (n := n) h
  have hU := measurableSet_evolutionStateSet_of_isOpen (γ := γ) (τ := τ)
    (isOpen_of_isAdmissibleEvolutionDomain hΩ)
  refine terminalMeasure_eq_of_spec n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
    (evolutionQueryOfState Ω γ σ τ hστ (evolutionStateShift Ω γ σ h p)) _ ?_ ?_ ?_
  · rw [Measure.map_apply hsh MeasurableSet.univ, preimage_univ]
    exact hspec.1
  · show ((μ (evolutionQueryOfState Ω γ σ τ hστ p)).map (evolutionAmbientStateShift h)).restrict
        (evolutionStateSet Ω γ τ) = _
    rw [Measure.restrict_map hsh hU, preimage_ambientShift_evolutionStateSet]
    exact congrArg (fun ν => ν.map (evolutionAmbientStateShift h)) hspec.2.1
  · intro F hF
    rw [integral_map hsh.aemeasurable F.measurable.aestronglyMeasurable]
    exact (hspec.2.2 (terminalDatumShift h F) (hF.shift h)).trans
      (terminalValue_shift n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
        hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx hBz
        σ τ hστ h p F hF)

/-- Translation covariance at the level of the fixed-time fiber kernel `κ`: the pushforward of `κ σ
τ p` under the transported-coordinate shift is `κ σ τ` of the shifted source. -/
theorem terminalFiberKernel_translation
    (hBz : ∀ (σ : ℝ) (y z z' : PDE.Vec n), B σ y z = B σ y z')
    (σ τ : ℝ) (hστ : σ ≤ τ) (h : PDE.Vec n) (p : EvolutionState Ω γ σ) :
    Measure.map (evolutionStateShift Ω γ τ h) (κ σ τ hστ p) =
      κ σ τ hστ (evolutionStateShift Ω γ σ h p) := by
  have hU := measurableSet_evolutionStateSet_of_isOpen (γ := γ) (τ := τ)
    (isOpen_of_isAdmissibleEvolutionDomain hΩ)
  rw [terminalFiberKernel_apply, terminalFiberKernel_apply,
    ← terminalMeasure_shift n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx hBz σ τ hστ h p,
    comap_map_ambientShift hU]

/-- Translation covariance for every moving fiber kernel `K` whose master measures are the
terminal measures `μ q`; the master kernel `K₀` is such a kernel by definition. -/
theorem terminalKernel_translation_of_master_eq
    (K : MovingFiberKernel Ω γ) (hK : ∀ q, K.master q = μ q)
    (hBz : ∀ (σ : ℝ) (y z z' : PDE.Vec n), B σ y z = B σ y z')
    (σ τ : ℝ) (hστ : σ ≤ τ) (h : PDE.Vec n) (p : EvolutionState Ω γ σ) :
    Measure.map (evolutionStateShift Ω γ τ h)
      (K.fiberKernel (measurableSet_of_isAdmissibleEvolutionDomain hΩ) σ τ hστ p) =
    K.fiberKernel (measurableSet_of_isAdmissibleEvolutionDomain hΩ)
      σ τ hστ (evolutionStateShift Ω γ σ h p) := by
  rw [MovingFiberKernel.fiberKernel_apply, MovingFiberKernel.fiberKernel_apply, hK, hK]
  exact terminalFiberKernel_translation n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx hBz σ τ hστ h p

end EvolutionData

end HypoellipticAleksandrov.KineticAleksandrov

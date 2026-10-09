module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Green
public import HypoellipticAleksandrov.KineticAleksandrov.Reconstruction.Main

/-!
# The slab setting of Proposition 5.3 and the outputs of Lemma 5.1 (case W)

Case W is the whole space `D = ℝ^d`, with stationary curve; the infinite-horizon Green measure
`Γ_μ^∞` lives on `ElapsedTime ⊤ × (ℝ^d × ℝ^d)` with coordinates `(τ, (w, z))`
(`SectionTwo.IsGreenMeasure`).  For `T > 0` the slab is `T < τ < 2T`.

`SlabFourierBounds` is the literal conjunction of the conclusions of Lemma 5.1
(companion paper, Lemma 5.1) for one pair `(μ, T)`:

* the `(τ, w)`-marginal of `Γ_μ^∞` on the slab has a density `g` with
  `‖g‖_{L^γ} ≤ C_γ M T^{β_γ}` for `1 ≤ γ ≤ γ₀ = (d+1)/d`;
* for every `ξ` the Fourier marginal `Φ ↦ ∫_{T<τ<2T} e^{-iξ·z} Φ(τ,w) dΓ` has a density `k^ξ`
  with `‖k^ξ‖_{L^γ} ≤ C_γ M T^{β_γ} exp(-c T |ξ|^{2/3})`, and
  `(2π)^{-d} ∫ ‖k^ξ‖_{L^γ} dξ ≤ C_γ M T^{β_γ - 3d/2}`.

The constants `C_γ` (a function `ℝ → ℝ≥0`) and `c` are the structural constants of the source.
This file only defines the predicate (a premise of the conditional results in
`Green.SlabDensity` and `Green.Main`, discharged by Lemma 5.1) and proves
the elementary measure facts about the slab.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Green

open MeasureTheory Set
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal NNReal

/-- The `(τ, w)` carrier `Y = (0,∞) × ℝ^d` of the position/time marginal. -/
abbrev SlabBase (d : ℕ) := ElapsedTime ⊤ × PDE.Vec d

/-- The carrier `(0,∞) × ℝ^d × ℝ^d` of the infinite-horizon Green measure, `(τ, (w, z))`. -/
abbrev GreenCarrier (d : ℕ) := ElapsedTime ⊤ × EvolutionAmbientState d

/-- Elapsed times in the open slab `T < τ < 2T`. -/
def slabTimeSet (T : ℝ) : Set (ElapsedTime ⊤) := {τ | T < τ.1 ∧ τ.1 < 2 * T}

/-- The slab `(T,2T) × ℝ^d × ℝ^d` inside the Green carrier. -/
def slabSet {d : ℕ} (T : ℝ) : Set (GreenCarrier d) := Prod.fst ⁻¹' slabTimeSet T

/-- Lebesgue measure on the base `(T,2T) × ℝ^d` of the slab, as a measure on `SlabBase d`. -/
def slabBase (d : ℕ) (T : ℝ) : Measure (SlabBase d) :=
  ((elapsedVolume ⊤).restrict (slabTimeSet T)).prod volume

/-- Lebesgue measure on `(0,∞) × ℝ^d × ℝ^d`, the reference measure of the Green density. -/
def greenLebesgue (d : ℕ) : Measure (GreenCarrier d) :=
  (elapsedVolume ⊤).prod (volume : Measure (EvolutionAmbientState d))

/-- The exponent `β_γ = (d+2)/(2γ) - d/2` of Proposition Proposition 4.2. -/
def slabBeta (d : ℕ) (γ : ℝ) : ℝ := ((d : ℝ) + 2) / (2 * γ) - (d : ℝ) / 2

/-- The upper Lebesgue exponent `γ₀ = (d+1)/d`. -/
def slabGamma0 (d : ℕ) : ℝ := ((d : ℝ) + 1) / (d : ℝ)

/-- The slab restriction of `Γ`, regrouped from `(τ, (w, z))` to `((τ, w), z)`. -/
def slabRegroup (d : ℕ) : GreenCarrier d ≃ᵐ SlabBase d × PDE.Vec d :=
  MeasurableEquiv.prodAssoc.symm

/-- **The outputs of Lemma 5.1 (case W) for one `(μ, T)`.**

`M` is the mass of `μ`, `C : ℝ → ℝ≥0` the constants `C_γ`, `c` the decay rate and `Γ` the
infinite-horizon Green measure.  See the module docstring. -/
def SlabFourierBounds (d : ℕ) (C : ℝ → ℝ≥0) (c : ℝ) (M : ℝ≥0∞) (T : ℝ)
    (Γ : Measure (GreenCarrier d)) : Prop :=
  (∃ g : SlabBase d → ℝ≥0∞, AEMeasurable g (slabBase d T) ∧
      (∀ E : Set (SlabBase d), MeasurableSet E →
        Γ {p | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T} =
          ∫⁻ y in E, g y ∂slabBase d T) ∧
      ∀ γ : ℝ, 1 ≤ γ → γ ≤ slabGamma0 d →
        eLpNorm g (ENNReal.ofReal γ) (slabBase d T) ≤
          (C γ : ℝ≥0∞) * M * ENNReal.ofReal (T ^ slabBeta d γ)) ∧
  (∃ k : PDE.Vec d → SlabBase d → ℂ,
      (∀ ξ, Integrable (k ξ) (slabBase d T) ∧
        ∀ E : Set (SlabBase d), MeasurableSet E →
          ∫ y in E, k ξ y ∂slabBase d T =
            ∫ p in {p : GreenCarrier d | (p.1, p.2.1) ∈ E ∧ T < p.1.1 ∧ p.1.1 < 2 * T},
              Complex.exp (-((PDE.vecDot ξ p.2.2 : ℝ) * Complex.I)) ∂Γ) ∧
      ∀ γ : ℝ, 1 ≤ γ → γ ≤ slabGamma0 d →
        (∀ ξ, eLpNorm (k ξ) (ENNReal.ofReal γ) (slabBase d T) ≤
          (C γ : ℝ≥0∞) * M * ENNReal.ofReal (T ^ slabBeta d γ) *
            ENNReal.ofReal (Real.exp (-(c * T * PDE.vecEuclideanNorm ξ ^ ((2 : ℝ) / 3))))) ∧
        ENNReal.ofReal (((2 * Real.pi) ^ d)⁻¹) *
            ∫⁻ ξ, eLpNorm (k ξ) (ENNReal.ofReal γ) (slabBase d T) ≤
          (C γ : ℝ≥0∞) * M * ENNReal.ofReal (T ^ (slabBeta d γ - 3 * (d : ℝ) / 2)))

/-- The slab regrouped measure `Γ.restrict (slab)` on `(SlabBase d) × ℝ^d`. -/
def slabMeasure (d : ℕ) (T : ℝ) (Γ : Measure (GreenCarrier d)) :
    Measure (SlabBase d × PDE.Vec d) :=
  (Γ.restrict (slabSet T)).map (slabRegroup d)

lemma measurableSet_slabTimeSet (T : ℝ) : MeasurableSet (slabTimeSet T) := by
  have h : slabTimeSet T = (Subtype.val : ElapsedTime ⊤ → ℝ) ⁻¹' Set.Ioo T (2 * T) := by
    ext τ; simp [slabTimeSet]
  rw [h]
  exact measurable_subtype_coe measurableSet_Ioo

lemma measurableSet_slabSet {d : ℕ} (T : ℝ) : MeasurableSet (slabSet (d := d) T) :=
  measurable_fst (measurableSet_slabTimeSet T)

/-- The slab has elapsed Lebesgue measure `T`. -/
lemma elapsedVolume_slabTimeSet {T : ℝ} (hT : 0 < T) :
    elapsedVolume ⊤ (slabTimeSet T) = ENNReal.ofReal T := by
  rw [elapsedVolume_apply _ _ (measurableSet_slabTimeSet T)]
  have : (Subtype.val : ElapsedTime ⊤ → ℝ) '' slabTimeSet T = Set.Ioo T (2 * T) := by
    ext t
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      exact hτ
    · intro ht
      exact ⟨⟨t, by linarith [ht.1], ENNReal.ofReal_lt_top⟩, ht, rfl⟩
  rw [this, Real.volume_Ioo]
  congr 1
  ring

instance slabBase_sigmaFinite (d : ℕ) (T : ℝ) : SigmaFinite (slabBase d T) := by
  unfold slabBase; infer_instance

/-- A Green measure has mass at most `M T` on the slab `(T, 2T)`. -/
lemma green_slab_le {d : ℕ} {γ : ℝ → PDE.Vec d} {Ω : Set (PDE.Vec d)}
    (K : MovingFiberKernel Ω γ) (σ₀ : ℝ) (μ : Measure (EvolutionState Ω γ σ₀))
    [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier d))
    (hΓ : IsGreenMeasure K σ₀ ⊤ μ Γ) {T : ℝ} (hT : 0 < T) :
    Γ (slabSet T) ≤ μ univ * ENNReal.ofReal T := by
  have := greenMeasure_timeMarginal_le K σ₀ ⊤ μ Γ hΓ (slabTimeSet T)
    (measurableSet_slabTimeSet T)
  rwa [elapsedVolume_slabTimeSet hT] at this

end HypoellipticAleksandrov.KineticAleksandrov.Green

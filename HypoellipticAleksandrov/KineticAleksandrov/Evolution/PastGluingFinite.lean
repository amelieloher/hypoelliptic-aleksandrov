module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonNodes
import Mathlib.Tactic.Linarith

/-! # Finite-past classical solutions and their uniqueness

The lower time is an artificial cutoff, with no prescribed datum there. Smoothness
and the equation hold strictly above it. Comparison is applied on later closed slabs.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter
open scoped Topology MatrixOrder

/-- Interior raw coordinates of a finite past moving slab. -/
def evolutionFiniteInteriorRaw {n : ℕ} (Ω : Set (PDE.Vec n))
    (γ : ℝ → PDE.Vec n) (a τ : ℝ) : Set (ℝ × (PDE.Vec n × PDE.Vec n)) :=
  {q | a < q.1 ∧ q ∈ evolutionPastInteriorRaw Ω γ τ}

/-- A bounded classical viscous solution on a finite slab, without lower-time data. -/
def IsClassicalViscousFiniteSolution {n : ℕ} (Ω : Set (PDE.Vec n))
    (γ : ℝ → PDE.Vec n) (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n)
    (ε a τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n))
    (u : KineticPoint n → ℝ) : Prop :=
  (∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ movingClosedSlab Ω γ a τ, |u p| ≤ C) ∧
    ContinuousOn u (movingClosedSlab Ω γ a τ) ∧
    ContDiffOn ℝ (⊤ : ℕ∞) (fun q => u ⟨q.1, q.2.1, q.2.2⟩)
      (evolutionFiniteInteriorRaw Ω γ a τ) ∧
    (∀ p ∈ movingActiveSlab Ω γ a τ, a < p.time →
      viscousTransportedOperator B b ε u p = 0) ∧
    (∀ p ∈ evolutionTerminalClosure Ω γ τ, u p = F (p.position, p.velocity)) ∧
    (∀ p ∈ movingClosedSlab Ω γ a τ,
      p.position ∈ frontier (movingDomain Ω γ p.time) → u p = 0)

/-- The strict finite-slab interior is open. -/
theorem isOpen_evolutionFiniteInteriorRaw {n : ℕ} {Ω : Set (PDE.Vec n)}
    (hΩ : IsOpen Ω) {γ : ℝ → PDE.Vec n} (hγ : Continuous γ) (a τ : ℝ) :
    IsOpen (evolutionFiniteInteriorRaw Ω γ a τ) :=
  (isOpen_lt continuous_const continuous_fst).inter (isOpen_evolutionPastInteriorRaw hΩ hγ τ)

/-- Finite-slab smoothness supplies slice regularity strictly above the lower time. -/
theorem IsClassicalViscousFiniteSolution.isSliceRegularAt {n : ℕ}
    {Ω : Set (PDE.Vec n)} (hΩ : IsOpen Ω) {γ : ℝ → PDE.Vec n} (hγ : Continuous γ)
    {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n} {ε a τ : ℝ}
    {F : BoundedBorel (EvolutionAmbientState n)} {u : KineticPoint n → ℝ}
    (hu : IsClassicalViscousFiniteSolution Ω γ B b ε a τ F u)
    {p : KineticPoint n} (hp : p ∈ movingActiveSlab Ω γ a τ) (ha : a < p.time) :
    IsSliceRegularAt u p := by
  apply IsSliceRegularAt.of_contDiffAt
  have hmem : (p.time, p.position, p.velocity) ∈ evolutionFiniteInteriorRaw Ω γ a τ :=
    ⟨ha, hp.2⟩
  exact (hu.2.2.1.contDiffAt
    ((isOpen_evolutionFiniteInteriorRaw hΩ hγ a τ).mem_nhds hmem)).of_le
      (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))

/-- Ordered data give comparison on the common finite past, above both lower endpoints. -/
theorem finite_classical_comparison {n : ℕ} {Ω : Set (PDE.Vec n)} (hΩ : IsOpen Ω)
    {γ : ℝ → PDE.Vec n} (hγ : Continuous γ) {lam Lam : ℝ} (hlam : 0 < lam)
    {B : FullKineticCoefficient n} (hB : HasEverywhereLoewnerBounds lam Lam B)
    {Lb : ℝ} {b : PDE.Vec n → PDE.Vec n} (hb : HasEuclideanLipschitzDrift Lb b)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {a₁ a₂ τ : ℝ}
    {F₁ F₂ : BoundedBorel (EvolutionAmbientState n)} {u₁ u₂ : KineticPoint n → ℝ}
    (h₁ : IsClassicalViscousFiniteSolution Ω γ B b ε a₁ τ F₁ u₁)
    (h₂ : IsClassicalViscousFiniteSolution Ω γ B b ε a₂ τ F₂ u₂)
    (hF : ∀ y z, y ∈ closure (movingDomain Ω γ τ) → F₁ (y, z) ≤ F₂ (y, z)) :
    ∀ p ∈ evolutionPastClosedCylinder Ω γ τ,
      a₁ < p.time → a₂ < p.time → u₁ p ≤ u₂ p := by
  intro p₀ hp₀ ha₁ ha₂
  have hs₁ : movingClosedSlab Ω γ p₀.time τ ⊆ movingClosedSlab Ω γ a₁ τ :=
    fun p hp => ⟨ha₁.le.trans hp.1, hp.2⟩
  have hs₂ : movingClosedSlab Ω γ p₀.time τ ⊆ movingClosedSlab Ω γ a₂ τ :=
    fun p hp => ⟨ha₂.le.trans hp.1, hp.2⟩
  have hr₁ : ∀ p ∈ movingActiveSlab Ω γ p₀.time τ, IsSliceRegularAt u₁ p :=
    fun p hp => h₁.isSliceRegularAt hΩ hγ ⟨ha₁.le.trans hp.1, hp.2⟩ (ha₁.trans_le hp.1)
  have hr₂ : ∀ p ∈ movingActiveSlab Ω γ p₀.time τ, IsSliceRegularAt u₂ p :=
    fun p hp => h₂.isSliceRegularAt hΩ hγ ⟨ha₂.le.trans hp.1, hp.2⟩ (ha₂.trans_le hp.1)
  obtain ⟨C₁, hC₁0, hC₁⟩ := h₁.1
  obtain ⟨C₂, hC₂0, hC₂⟩ := h₂.1
  have hres := growth_comparison (a := p₀.time) (T := τ) (u := fun q => u₁ q - u₂ q)
    hΩ hγ hlam hB hb hε0 hε1 ?_ ?_ ?_ ?_ ?_ ?_ p₀ ⟨le_rfl, hp₀⟩
  · exact sub_nonpos.mp hres
  · refine ⟨C₁ + C₂, fun p hp => ?_⟩
    have h1 := (abs_le.mp (hC₁ p (hs₁ hp))).2
    have h2 := (abs_le.mp (hC₂ p (hs₂ hp))).1
    linarith only [h1, h2]
  · exact (h₁.2.1.mono hs₁).sub (h₂.2.1.mono hs₂)
  · exact fun p hp => (hr₁ p hp).sub (hr₂ p hp)
  · intro p hp
    rw [viscousTransportedOperator_sub (hr₁ p hp) (hr₂ p hp),
      h₁.2.2.2.1 p ⟨ha₁.le.trans hp.1, hp.2⟩ (ha₁.trans_le hp.1),
      h₂.2.2.2.1 p ⟨ha₂.le.trans hp.1, hp.2⟩ (ha₂.trans_le hp.1)]
    simp only [sub_self, le_refl]
  · intro p hp hpT
    have ht : p ∈ evolutionTerminalClosure Ω γ τ := ⟨hpT, hpT ▸ hp.2.2⟩
    rw [h₁.2.2.2.2.1 p ht, h₂.2.2.2.2.1 p ht]
    exact sub_nonpos.mpr (hF _ _ ht.2)
  · intro p hp hfr
    rw [h₁.2.2.2.2.2 p (hs₁ hp) hfr, h₂.2.2.2.2.2 p (hs₂ hp) hfr]
    simp only [sub_self, le_refl]

/-- Finite-past uniqueness makes different lower-time constructions compatible. -/
theorem finite_classical_unique {n : ℕ} {Ω : Set (PDE.Vec n)} (hΩ : IsOpen Ω)
    {γ : ℝ → PDE.Vec n} (hγ : Continuous γ) {lam Lam : ℝ} (hlam : 0 < lam)
    {B : FullKineticCoefficient n} (hB : HasEverywhereLoewnerBounds lam Lam B)
    {Lb : ℝ} {b : PDE.Vec n → PDE.Vec n} (hb : HasEuclideanLipschitzDrift Lb b)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {a₁ a₂ τ : ℝ}
    {F : BoundedBorel (EvolutionAmbientState n)} {u₁ u₂ : KineticPoint n → ℝ}
    (h₁ : IsClassicalViscousFiniteSolution Ω γ B b ε a₁ τ F u₁)
    (h₂ : IsClassicalViscousFiniteSolution Ω γ B b ε a₂ τ F u₂) :
    ∀ p ∈ evolutionPastClosedCylinder Ω γ τ,
      a₁ < p.time → a₂ < p.time → u₁ p = u₂ p := by
  intro p hp ha₁ ha₂
  exact le_antisymm
    (finite_classical_comparison hΩ hγ hlam hB hb hε0 hε1 h₁ h₂
      (fun _ _ _ => le_rfl) p hp ha₁ ha₂)
    (finite_classical_comparison hΩ hγ hlam hB hb hε0 hε1 h₂ h₁
      (fun _ _ _ => le_rfl) p hp ha₂ ha₁)

end HypoellipticAleksandrov.KineticAleksandrov

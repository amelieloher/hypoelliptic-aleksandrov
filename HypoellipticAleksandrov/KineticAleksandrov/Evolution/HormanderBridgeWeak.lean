module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeAdjoint

/-!
# Weak solutions of `Lop` and `L_ε` and the Hörmander weak equation

The notion of the companion paper, (A.2): a locally integrable `u` is a distributional
solution of `Lop u = g` on an open set `Ω` of `ℝ^{1+2d}` if
`∫_Ω u · Lop^* ψ = ∫_Ω g ψ` for every smooth `ψ` with compact support in `Ω`; for
`L_ε = Lop + ε Δ_z` the adjoint is `Lop^* ψ + ε Δ_z ψ`.  `IsDistributionalSolution` packages this
for any adjoint operator, `IsWeakTransportedSolution` and `IsWeakRegularizedSolution` specialise
it to `transportedAdjoint` and `regularizedAdjoint`.

The theorems `hasWeakHormanderEquation_transportedFields_iff` and
`hasWeakHormanderEquation_regularizedFields_iff` show that, for the field families of the bracket
files with zeroth-order coefficient `c = 0`, the carrier `HasWeakHormanderEquation` is
exactly "distributional solution of `Lop u = g`" (resp. `L_ε u = g`) together with the smoothness
of the right-hand side `g` on `Ω` that the carrier records.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory Set

namespace HypoellipticAleksandrov.KineticAleksandrov.Evolution

variable {n : ℕ}

/-- `u` is a distributional solution of `L u = g` on `Ω` for the operator with formal adjoint
`Ladj`: `u` is locally integrable on `Ω` and `∫_Ω u · L^* ψ = ∫_Ω g ψ` for every smooth `ψ` with
compact support in `Ω`. -/
def IsDistributionalSolution (Ladj : (EvolutionVec n → ℝ) → EvolutionVec n → ℝ)
    (Ω : Set (EvolutionVec n)) (u g : EvolutionVec n → ℝ) : Prop :=
  LocallyIntegrableOn u Ω volume ∧
    ∀ ψ : EvolutionVec n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      (∫ x in Ω, u x * Ladj ψ x) = ∫ x in Ω, g x * ψ x

/-- `u` is a distributional solution of `Lop u = g` on `Ω`
(`∫_Ω u · Lop^* ψ = ∫_Ω g ψ`). -/
def IsWeakTransportedSolution (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n)
    (Ω : Set (EvolutionVec n)) (u g : EvolutionVec n → ℝ) : Prop :=
  IsDistributionalSolution (transportedAdjoint B b) Ω u g

/-- `u` is a distributional solution of `L_ε u = g` on `Ω`
(`∫_Ω u · (Lop^* ψ + ε Δ_z ψ) = ∫_Ω g ψ`). -/
def IsWeakRegularizedSolution (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n) (ε : ℝ)
    (Ω : Set (EvolutionVec n)) (u g : EvolutionVec n → ℝ) : Prop :=
  IsDistributionalSolution (regularizedAdjoint B b ε) Ω u g

section Iff

variable {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n} {lam Lam : ℝ}

/-- For the fields of `Lop`, the Hörmander weak equation with `c = 0` is the distributional
equation `Lop u = g` together with smoothness of `g` on `Ω`. -/
theorem hasWeakHormanderEquation_transportedFields_iff (hlam : 0 < lam)
    (hB : IsSmoothFullKineticCoefficient B) (hell : HasEverywhereLoewnerBounds lam Lam B)
    (hb : IsSmoothDrift b) (Ω : Set (EvolutionVec n)) (u g : EvolutionVec n → ℝ) :
    HasWeakHormanderEquation Ω (transportedFields B b) (fun _ => 0) g u ↔
      IsWeakTransportedSolution B b Ω u g ∧ ContDiffOn ℝ (⊤ : ℕ∞) g Ω := by
  have key : ∀ ψ : EvolutionVec n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      hormanderAdjointTest (transportedFields B b) (fun _ => 0) ψ = transportedAdjoint B b ψ :=
    fun ψ hψ => funext (hormanderAdjointTest_transportedFields hlam hB hell hb hψ)
  constructor
  · rintro ⟨hu, hg, h⟩
    refine ⟨⟨hu, fun ψ hψ hc hs => ?_⟩, hg⟩
    simpa only [key ψ hψ] using h ψ hψ hc hs
  · rintro ⟨⟨hu, h⟩, hg⟩
    refine ⟨hu, hg, fun ψ hψ hc hs => ?_⟩
    simpa only [key ψ hψ] using h ψ hψ hc hs

/-- **Weak-form bridge for `Lop`.**  A distributional solution of `Lop u = g` (with `g` smooth on
`Ω`) satisfies the Hörmander weak equation for `transportedFields B b`, `c = 0`. -/
theorem hasWeakHormanderEquation_transportedFields (hlam : 0 < lam)
    (hB : IsSmoothFullKineticCoefficient B) (hell : HasEverywhereLoewnerBounds lam Lam B)
    (hb : IsSmoothDrift b) {Ω : Set (EvolutionVec n)} {u g : EvolutionVec n → ℝ}
    (hu : IsWeakTransportedSolution B b Ω u g) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g Ω) :
    HasWeakHormanderEquation Ω (transportedFields B b) (fun _ => 0) g u :=
  (hasWeakHormanderEquation_transportedFields_iff hlam hB hell hb Ω u g).2 ⟨hu, hg⟩

/-- For the fields of `L_ε` (`ε ≥ 0`), the Hörmander weak equation with `c = 0` is the
distributional equation `L_ε u = g` together with smoothness of `g` on `Ω`. -/
theorem hasWeakHormanderEquation_regularizedFields_iff {ε : ℝ} (hε : 0 ≤ ε) (hlam : 0 < lam)
    (hB : IsSmoothFullKineticCoefficient B) (hell : HasEverywhereLoewnerBounds lam Lam B)
    (hb : IsSmoothDrift b) (Ω : Set (EvolutionVec n)) (u g : EvolutionVec n → ℝ) :
    HasWeakHormanderEquation Ω (regularizedFields B b ε) (fun _ => 0) g u ↔
      IsWeakRegularizedSolution B b ε Ω u g ∧ ContDiffOn ℝ (⊤ : ℕ∞) g Ω := by
  have key : ∀ ψ : EvolutionVec n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      hormanderAdjointTest (regularizedFields B b ε) (fun _ => 0) ψ =
        regularizedAdjoint B b ε ψ :=
    fun ψ hψ => funext (hormanderAdjointTest_regularizedFields hε hlam hB hell hb hψ)
  constructor
  · rintro ⟨hu, hg, h⟩
    refine ⟨⟨hu, fun ψ hψ hc hs => ?_⟩, hg⟩
    simpa only [key ψ hψ] using h ψ hψ hc hs
  · rintro ⟨⟨hu, h⟩, hg⟩
    refine ⟨hu, hg, fun ψ hψ hc hs => ?_⟩
    simpa only [key ψ hψ] using h ψ hψ hc hs

/-- **Weak-form bridge for `L_ε`** (Proposition 2.1).  A distributional
solution of `L_ε u = g` (`∫ u (Lop^* ψ + ε Δ_z ψ) = ∫ g ψ`, `g` smooth on `Ω`) satisfies the
Hörmander weak equation for `regularizedFields B b ε`, `c = 0`. -/
theorem hasWeakHormanderEquation_regularizedFields {ε : ℝ} (hε : 0 ≤ ε) (hlam : 0 < lam)
    (hB : IsSmoothFullKineticCoefficient B) (hell : HasEverywhereLoewnerBounds lam Lam B)
    (hb : IsSmoothDrift b) {Ω : Set (EvolutionVec n)} {u g : EvolutionVec n → ℝ}
    (hu : IsWeakRegularizedSolution B b ε Ω u g) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g Ω) :
    HasWeakHormanderEquation Ω (regularizedFields B b ε) (fun _ => 0) g u :=
  (hasWeakHormanderEquation_regularizedFields_iff hε hlam hB hell hb Ω u g).2 ⟨hu, hg⟩

end Iff

end HypoellipticAleksandrov.KineticAleksandrov.Evolution

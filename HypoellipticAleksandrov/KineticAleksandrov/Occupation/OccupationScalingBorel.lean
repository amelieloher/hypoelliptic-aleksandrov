module

public import HypoellipticAleksandrov.KineticAleksandrov.Scaling.Radius

/-! # Conjugating the scalar marginal operator family under radius scaling -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation
open SectionTwo Scaling MeasureTheory

/-- Measurable pullback is a real-linear map on bounded Borel data. -/
def occupation_borelComap {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (f : α → β) (hf : Measurable f) : BoundedBorel β →ₗ[ℝ] BoundedBorel α where
  toFun g := ⟨fun x => g (f x), g.measurable.comp hf, by
    obtain ⟨C, hC, hb⟩ := g.exists_bound
    exact ⟨C, hC, fun x => hb _⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Evaluation of measurable bounded-Borel pullback. -/
@[simp] theorem occupation_borelComap_apply {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (f : α → β) (hf : Measurable f)
    (g : BoundedBorel β) (x : α) : occupation_borelComap f hf g x = g (f x) := rfl

/-- The whole-space scalar position equivalence at the two corresponding times. -/
def occupation_positionEquiv {d : ℕ} (Φ : KineticAffineScaling d) (t : ℝ) :
    EvolutionPosition (wholeSpace d) (fun _ => (0 : PDE.Vec d)) t ≃ᵐ
      EvolutionPosition (wholeSpace d) (fun _ => (0 : PDE.Vec d)) (Φ.time t) :=
  (wholeSpacePositionEquiv d t).trans
    (Φ.positionHomeo.toMeasurableEquiv.trans (wholeSpacePositionEquiv d (Φ.time t)).symm)

/-- Conjugation of the original scalar operators by their fixed-time position equivalences. -/
def occupation_pushParabolicFamily {d : ℕ} (Φ : KineticAffineScaling d)
    (Q : ParabolicOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d))) :
    ParabolicOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)) :=
  fun σ τ hστ =>
    (occupation_borelComap (occupation_positionEquiv Φ σ)
      (occupation_positionEquiv Φ σ).measurable).comp
      ((Q (Φ.time σ) (Φ.time τ) (Φ.time_le_iff.mpr hστ)).comp
        (occupation_borelComap (occupation_positionEquiv Φ τ).symm
          (occupation_positionEquiv Φ τ).symm.measurable))

/-- The conjugated scalar family inherits the original endpoint identity. -/
theorem occupation_pushParabolicFamily_endpoint {d : ℕ} (Φ : KineticAffineScaling d)
    (Q : ParabolicOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (hQ : ∀ σ, Q σ σ le_rfl = LinearMap.id) (σ : ℝ) :
    occupation_pushParabolicFamily Φ Q σ σ le_rfl = LinearMap.id := by
  ext f y
  simp only [occupation_pushParabolicFamily, LinearMap.comp_apply,
    occupation_borelComap_apply]
  rw [hQ]
  exact congrArg f ((occupation_positionEquiv Φ σ).symm_apply_apply y)

/-- The conjugated scalar family preserves positive data. -/
theorem occupation_pushParabolicFamily_positive {d : ℕ} (Φ : KineticAffineScaling d)
    (Q : ParabolicOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (hQ : ∀ σ τ hστ f, 0 ≤ f → 0 ≤ Q σ τ hστ f)
    (σ τ : ℝ) (hστ : σ ≤ τ)
    (f : BoundedBorel (EvolutionPosition (wholeSpace d) (fun _ => 0) τ)) (hf : 0 ≤ f) :
    0 ≤ occupation_pushParabolicFamily Φ Q σ τ hστ f := by
  intro y
  change 0 ≤ Q (Φ.time σ) (Φ.time τ) (Φ.time_le_iff.mpr hστ)
    (occupation_borelComap (occupation_positionEquiv Φ τ).symm
      (occupation_positionEquiv Φ τ).symm.measurable f)
    (occupation_positionEquiv Φ σ y)
  have hf0 : 0 ≤ occupation_borelComap (occupation_positionEquiv Φ τ).symm
      (occupation_positionEquiv Φ τ).symm.measurable f := by
    intro x
    change 0 ≤ f ((occupation_positionEquiv Φ τ).symm x)
    exact hf ((occupation_positionEquiv Φ τ).symm x)
  exact hQ (Φ.time σ) (Φ.time τ) (Φ.time_le_iff.mpr hστ) _ hf0
    (occupation_positionEquiv Φ σ y)

/-- The conjugated scalar family retains its sub-Markov contraction. -/
theorem occupation_pushParabolicFamily_contraction {d : ℕ} (Φ : KineticAffineScaling d)
    (Q : ParabolicOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (hQ : ∀ σ τ hστ, Q σ τ hστ 1 ≤ 1) (σ τ : ℝ) (hστ : σ ≤ τ) :
    occupation_pushParabolicFamily Φ Q σ τ hστ 1 ≤ 1 := by
  intro y
  exact hQ (Φ.time σ) (Φ.time τ) (Φ.time_le_iff.mpr hστ)
    (occupation_positionEquiv Φ σ y)

/-- The conjugated scalar family retains composition. -/
theorem occupation_pushParabolicFamily_composition {d : ℕ} (Φ : KineticAffineScaling d)
    (Q : ParabolicOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (hQ : ∀ σ r τ hσr hrτ, Q σ τ (hσr.trans hrτ) =
      (Q σ r hσr).comp (Q r τ hrτ))
    (σ r τ : ℝ) (hσr : σ ≤ r) (hrτ : r ≤ τ) :
    occupation_pushParabolicFamily Φ Q σ τ (hσr.trans hrτ) =
      (occupation_pushParabolicFamily Φ Q σ r hσr).comp
        (occupation_pushParabolicFamily Φ Q r τ hrτ) := by
  ext f y
  have hcancel (g : BoundedBorel
      (EvolutionPosition (wholeSpace d) (fun _ => (0 : PDE.Vec d)) (Φ.time r))) :
      occupation_borelComap (occupation_positionEquiv Φ r).symm
        (occupation_positionEquiv Φ r).symm.measurable
        (occupation_borelComap (occupation_positionEquiv Φ r)
          (occupation_positionEquiv Φ r).measurable g) = g := by
    ext x
    exact congrArg g ((occupation_positionEquiv Φ r).apply_symm_apply x)
  simp only [occupation_pushParabolicFamily, LinearMap.comp_apply,
    occupation_borelComap_apply]
  rw [show Q (Φ.time σ) (Φ.time τ) (Φ.time_le_iff.mpr (hσr.trans hrτ)) =
      (Q (Φ.time σ) (Φ.time r) (Φ.time_le_iff.mpr hσr)).comp
        (Q (Φ.time r) (Φ.time τ) (Φ.time_le_iff.mpr hrτ)) from hQ _ _ _ _ _]
  simp only [LinearMap.comp_apply]
  rw [hcancel]

end HypoellipticAleksandrov.KineticAleksandrov.Occupation

module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BracketCoord
public import HypoellipticAleksandrov.Geometry.KineticPointMeasure
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# The coordinate bridge between packed space and `KineticPoint`

The transported operator lives on the packed space `ℝ^{1+2d} = EvolutionVec n` (the Hörmander
bracket files), while the project's `transportedForwardOperator` lives on `KineticPoint n`,
read as `(σ, y, z)` = `(time, position, velocity)`.  `KineticPoint n` carries no vector-space
structure, so the bridge is:

* `evolutionProdCLE n : EvolutionVec n ≃L[ℝ] ℝ × (PDE.Vec n × PDE.Vec n)`, the continuous linear
  equivalence unpacking `(σ, v, z)`;
* `evolutionHomeomorph n : EvolutionVec n ≃ₜ KineticPoint n`, `x ↦ ⟨σ, v, z⟩`, its composite
  with the project's `KineticPoint.homeomorphProd`;
* `evolutionMeasurableEquiv n`, the measurable equivalence of `evolutionHomeomorph n`, which is
  measure preserving for Lebesgue measure on `EvolutionVec n` and the `KineticPoint` volume of
  `Geometry/KineticPointMeasure.lean` (`measurePreserving_evolutionHomeomorph`).
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory
open HypoellipticAleksandrov

namespace HypoellipticAleksandrov.KineticAleksandrov.Evolution

variable {n : ℕ}

variable (n) in
/-- The linear equivalence unpacking `(σ, v, z) ∈ ℝ^{1+2d}` into `ℝ × (ℝ^d × ℝ^d)`. -/
def evolutionProdLinearEquiv : EvolutionVec n ≃ₗ[ℝ] ℝ × (PDE.Vec n × PDE.Vec n) where
  toFun x := (timeCoord n x, (diffusedCoord n x, transportedCoord n x))
  invFun a := packPoint a.1 a.2.1 a.2.2
  map_add' x y := by simp
  map_smul' c x := by simp
  left_inv x := packPoint_coords x
  right_inv a := by simp

variable (n) in
/-- The continuous linear equivalence unpacking `(σ, v, z) ∈ ℝ^{1+2d}` into
`ℝ × (ℝ^d × ℝ^d)` (time, diffused, transported). -/
def evolutionProdCLE : EvolutionVec n ≃L[ℝ] ℝ × (PDE.Vec n × PDE.Vec n) :=
  (evolutionProdLinearEquiv n).toContinuousLinearEquiv

@[simp] theorem evolutionProdCLE_apply (x : EvolutionVec n) :
    evolutionProdCLE n x = (timeCoord n x, (diffusedCoord n x, transportedCoord n x)) := rfl

@[simp] theorem evolutionProdCLE_symm_apply (a : ℝ × (PDE.Vec n × PDE.Vec n)) :
    (evolutionProdCLE n).symm a = packPoint a.1 a.2.1 a.2.2 := rfl

variable (n) in
/-- The homeomorphism `ℝ^{1+2d} ≃ₜ KineticPoint n`, `(σ, v, z) ↦ ⟨σ, v, z⟩`: the position
field of the kinetic point is the diffused coordinate `v` and its velocity field is the
transported coordinate `z`. -/
def evolutionHomeomorph : EvolutionVec n ≃ₜ KineticPoint n :=
  (evolutionProdCLE n).toHomeomorph.trans (KineticPoint.homeomorphProd n).symm

theorem evolutionHomeomorph_apply (x : EvolutionVec n) :
    evolutionHomeomorph n x = ⟨timeCoord n x, diffusedCoord n x, transportedCoord n x⟩ := rfl

theorem evolutionHomeomorph_symm_apply (z : KineticPoint n) :
    (evolutionHomeomorph n).symm z = packPoint z.time z.position z.velocity := rfl

@[simp] theorem time_evolutionHomeomorph (x : EvolutionVec n) :
    (evolutionHomeomorph n x).time = timeCoord n x := rfl

@[simp] theorem position_evolutionHomeomorph (x : EvolutionVec n) :
    (evolutionHomeomorph n x).position = diffusedCoord n x := rfl

@[simp] theorem velocity_evolutionHomeomorph (x : EvolutionVec n) :
    (evolutionHomeomorph n x).velocity = transportedCoord n x := rfl

@[simp] theorem equivProd_evolutionHomeomorph (x : EvolutionVec n) :
    KineticPoint.equivProd n (evolutionHomeomorph n x) = evolutionProdCLE n x := rfl

variable (n) in
/-- The measurable equivalence `ℝ^{1+2d} ≃ᵐ ℝ × (ℝ^d × ℝ^d)` along the packing. -/
def evolutionProdMeasurableEquiv : EvolutionVec n ≃ᵐ ℝ × (PDE.Vec n × PDE.Vec n) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + n + 1) => ℝ) 0).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
      ((MeasurableEquiv.piCongrLeft (fun _ : Fin (n + n) => ℝ) finSumFinEquiv).symm.trans
        (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin n => ℝ))))

theorem evolutionProdMeasurableEquiv_apply (x : EvolutionVec n) :
    evolutionProdMeasurableEquiv n x = evolutionProdCLE n x := rfl

/-- Lebesgue measure on `ℝ^{1+2d}` is product Lebesgue measure on `ℝ × (ℝ^d × ℝ^d)`. -/
theorem measurePreserving_evolutionProdMeasurableEquiv :
    MeasurePreserving (evolutionProdMeasurableEquiv n) volume volume := by
  have h1 := volume_preserving_piFinSuccAbove (fun _ : Fin (n + n + 1) => ℝ) 0
  have h2 := (volume_measurePreserving_piCongrLeft (fun _ : Fin (n + n) => ℝ) finSumFinEquiv).symm
  have h3 := volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin n ⊕ Fin n => ℝ)
  exact h1.trans ((MeasurePreserving.id volume).prod (h2.trans h3))

variable (n) in
/-- The measurable equivalence `ℝ^{1+2d} ≃ᵐ KineticPoint n` of `evolutionHomeomorph`. -/
def evolutionMeasurableEquiv : EvolutionVec n ≃ᵐ KineticPoint n :=
  (evolutionHomeomorph n).toMeasurableEquiv

@[simp] theorem evolutionMeasurableEquiv_apply (x : EvolutionVec n) :
    evolutionMeasurableEquiv n x = evolutionHomeomorph n x := rfl

@[simp] theorem evolutionMeasurableEquiv_symm_apply (z : KineticPoint n) :
    (evolutionMeasurableEquiv n).symm z = (evolutionHomeomorph n).symm z := rfl

/-- **Measure preservation.**  Lebesgue measure on `ℝ^{1+2d}` is carried by `(σ, v, z) ↦ ⟨σ, v, z⟩`
to the `KineticPoint` volume of `Geometry/KineticPointMeasure.lean`. -/
theorem measurePreserving_evolutionHomeomorph :
    MeasurePreserving (evolutionHomeomorph n) volume volume := by
  have h1 := measurePreserving_evolutionProdMeasurableEquiv (n := n)
  have h2 := (KineticPoint.measurePreserving_equivProd n).symm
    (KineticPoint.homeomorphProd n).toMeasurableEquiv
  exact h1.trans h2

theorem measurePreserving_evolutionMeasurableEquiv :
    MeasurePreserving (evolutionMeasurableEquiv n) volume volume :=
  measurePreserving_evolutionHomeomorph

end HypoellipticAleksandrov.KineticAleksandrov.Evolution

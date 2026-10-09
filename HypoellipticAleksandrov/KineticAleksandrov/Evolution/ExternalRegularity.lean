module

public import HypoellipticAleksandrov.KineticAleksandrov.ClassicalInputs
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BracketHormander
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeTransfer

/-!
# Hörmander regularity for `L_ε` and for the transported operator

Consequences of Hörmander's hypoellipticity theorem (`HormanderHypoellipticityStatement`),
taken as an explicit hypothesis `hH`.

* `exists_smooth_viscous_kinetic_representative` (Proposition 2.1): for `ε > 0`, a locally
  integrable distributional solution of `L_ε u = 0` on an open set
  `U ⊆ KineticPoint n` has a representative that is smooth in packed coordinates on the preimage
  of `U` and equals `u` almost everywhere on `U`.
* `exists_smooth_kinetic_representative` (Proposition 2.1): the same for
  `ε = 0`, i.e. for the transported operator, using the drift coercivity for the bracket check.
* `eqOn_of_ae_eq_of_continuousOn_kinetic`: a continuous candidate agrees pointwise with such a
  smooth representative (the identification step used after continuity is established).

The conclusion is an almost-everywhere smooth representative, not pointwise smoothness of `u`.
The statements below use only the standing hypotheses that the proofs need
(`0 < lam`, `B` smooth, Loewner bounds, `b` smooth, and for `ε = 0` also `0 < m` with drift
coercivity); the standing hypotheses of the evolution problem therefore specialise to them.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory Set
open HypoellipticAleksandrov
open scoped MatrixOrder

namespace HypoellipticAleksandrov.KineticAleksandrov.Evolution

variable {n : ℕ}

/-- **Smooth representative** (Proposition 2.1).  Assuming Hörmander's theorem
`hH`, a locally integrable distributional solution `u` of `L_ε u = 0` (`ε > 0`) on an open
`U ⊆ KineticPoint n` has a representative `v`, smooth in packed coordinates on the preimage of `U`,
with `u = v` almost everywhere on `U`. -/
theorem exists_smooth_viscous_kinetic_representative
    (hH : HormanderHypoellipticityStatement) {lam Lam : ℝ}
    {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n} (hlam : 0 < lam)
    (hB_smooth : IsSmoothFullKineticCoefficient B)
    (hB_ell : HasEverywhereLoewnerBounds lam Lam B) (hb_smooth : IsSmoothDrift b)
    (U : Set (KineticPoint n)) (hU : IsOpen U) (ε : ℝ) (hε : 0 < ε) (u : KineticPoint n → ℝ)
    (hu : IsKineticWeakRegularizedSolution B b ε U u (fun _ => 0)) :
    ∃ v : KineticPoint n → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) (v ∘ evolutionHomeomorph n) (evolutionHomeomorph n ⁻¹' U) ∧
        u =ᵐ[volume.restrict U] v := by
  obtain ⟨hX, hspan⟩ :=
    hormander_hypotheses_regularizedFields hlam hB_smooth hB_ell hb_smooth hε
      (evolutionHomeomorph n ⁻¹' U)
  have hEq := hasWeakHormanderEquation_comp_regularizedFields hε.le hlam hB_smooth hB_ell
    hb_smooth hu (contDiffOn_const (c := (0 : ℝ)))
  exact exists_kinetic_representative
    (hH ((evolutionHomeomorph n).continuous.isOpen_preimage U hU) _ _ _ _ hX hspan
      contDiffOn_const hEq)

/-- **Smooth representative** (Proposition 2.1, Hörmander part).  Assuming the Hörmander
theorem `hH`, a locally integrable distributional solution `u` of `Lop u = 0` for the transported
operator on an open `U ⊆ KineticPoint n` has a representative `v`, smooth in packed coordinates
on the preimage of `U`, with `u = v` almost everywhere on `U`.  The bracket check uses `0 < m` and
unit-direction drift coercivity. -/
theorem exists_smooth_kinetic_representative
    (hH : HormanderHypoellipticityStatement) {lam Lam m : ℝ}
    {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n} (hlam : 0 < lam)
    (hB_smooth : IsSmoothFullKineticCoefficient B)
    (hB_ell : HasEverywhereLoewnerBounds lam Lam B) (hb_smooth : IsSmoothDrift b)
    (hm : 0 < m) (hb_coercive : HasUnitDirectionDriftCoercivity m b)
    (U : Set (KineticPoint n)) (hU : IsOpen U) (u : KineticPoint n → ℝ)
    (hu : IsKineticWeakTransportedSolution B b U u (fun _ => 0)) :
    ∃ v : KineticPoint n → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) (v ∘ evolutionHomeomorph n) (evolutionHomeomorph n ⁻¹' U) ∧
        u =ᵐ[volume.restrict U] v := by
  obtain ⟨hX, hspan⟩ :=
    hormander_hypotheses_transportedFields hlam hB_smooth hB_ell hb_smooth hm hb_coercive
      (evolutionHomeomorph n ⁻¹' U)
  have hEq := hasWeakHormanderEquation_comp_transportedFields hlam hB_smooth hB_ell
    hb_smooth hu (contDiffOn_const (c := (0 : ℝ)))
  exact exists_kinetic_representative
    (hH ((evolutionHomeomorph n).continuous.isOpen_preimage U hU) _ _ _ _ hX hspan
      contDiffOn_const hEq)

/-- Identification of a continuous candidate with a smooth representative: two functions that
are continuous in packed coordinates on the preimage of an open `U` and agree almost everywhere
on `U` agree at every point of `U`. -/
theorem eqOn_of_ae_eq_of_continuousOn_kinetic {U : Set (KineticPoint n)} (hU : IsOpen U)
    {v w : KineticPoint n → ℝ}
    (hv : ContinuousOn (v ∘ evolutionHomeomorph n) (evolutionHomeomorph n ⁻¹' U))
    (hw : ContinuousOn (w ∘ evolutionHomeomorph n) (evolutionHomeomorph n ⁻¹' U))
    (hae : v =ᵐ[volume.restrict U] w) : EqOn v w U := by
  have h := Measure.eqOn_open_of_ae_eq (ae_eq_comp_evolutionHomeomorph_iff.2 hae)
    ((evolutionHomeomorph n).continuous.isOpen_preimage U hU) hv hw
  intro x hx
  have := h (show (evolutionHomeomorph n).symm x ∈ evolutionHomeomorph n ⁻¹' U by simpa using hx)
  simpa using this

end HypoellipticAleksandrov.KineticAleksandrov.Evolution

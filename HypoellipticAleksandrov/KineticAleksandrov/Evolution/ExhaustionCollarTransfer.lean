module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationWeakRegularity
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.StraightenedTransferClassical

/-!
# Finite-domain classical transfer without an interior smoothness premise

The actual scalar C1,2 Dirichlet solution has joint first differentiability. That is
sufficient for the slice regularity and pointwise equation used by compact comparison.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set
open scoped Topology

/-- The actual scalar Dirichlet solution transfers to a slice-regular kinetic solution
on its finite open cylinder; no Hörmander or joint C2 premise is needed. -/
theorem straightenedPullback_dirichlet_sliceRegular
    {n : ℕ} {D : Set (PDE.Vec (n + n))} (hD : IsOpen D)
    {g : ℝ → PDE.Vec n} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n} {ε a τ : ℝ}
    {F : BoundedBorel (EvolutionAmbientState n)} {u : TimeVelocity (n + n) → ℝ}
    (hu : IsClassicalBackwardDirichletSolution a τ D
      (straightenedCoefficient B g ε) (straightenedDrift b g)
      (fun _ _ => 0) (fun _ _ => 0) (fun x => F (g τ + spatialY x, spatialZ x))
      (fun _ => 0) u) :
    ∀ p ∈ straightenedPoint g ⁻¹' scalarParabolicOpenCylinder a τ D,
      IsSliceRegularAt (straightenedPullback g u) p ∧
      viscousTransportedOperator B b ε (straightenedPullback g u) p = 0 := by
  intro p hp
  have ho : IsOpen (scalarParabolicOpenCylinder a τ D) := isOpen_Ioo.prod hD
  have hd := scalarC12_differentiableAt ho hu.2.1 hp
  have hs := hu.2.1.spatialSlice_contDiffAt hp
  have hgd := (hg.differentiable (by simp)) p.time
  refine ⟨isSliceRegularAt_straightenedPullback hgd hd hs, ?_⟩
  rw [viscousTransportedOperator_straightenedPullback hgd hd hs]
  simpa only [scalarParabolicZeroOrderOperator, zero_mul, add_zero] using hu.2.2.1 _ hp

/-- The straightening map, with its explicit inverse, is a homeomorphism on the literal
kinetic and scalar time-spatial carriers. -/
def straightenedPointHomeomorph {n : ℕ} (g : ℝ → PDE.Vec n) (hg : Continuous g) :
    KineticPoint n ≃ₜ TimeVelocity (n + n) where
  toFun := straightenedPoint g
  invFun q := ⟨q.1, g q.1 + spatialY q.2, spatialZ q.2⟩
  left_inv p := by
    ext <;> simp [straightenedPoint]
  right_inv q := by
    rcases q with ⟨t, x⟩
    simp [straightenedPoint]
  continuous_toFun := continuous_straightenedPoint hg
  continuous_invFun := KineticPoint.continuous_mk continuous_fst
    ((hg.comp continuous_fst).add
      ((contDiff_spatialY (m := 0)).continuous.comp continuous_snd))
    ((contDiff_spatialZ (m := 0)).continuous.comp continuous_snd)

/-- A bounded finite spatial cylinder remains compact in absolute moving coordinates. -/
theorem isCompact_straightened_closedCylinder {n : ℕ} {D : Set (PDE.Vec (n + n))}
    (hD : Bornology.IsBounded D) {g : ℝ → PDE.Vec n} (hg : Continuous g) (a τ : ℝ) :
    IsCompact (straightenedPoint g ⁻¹' scalarParabolicClosedCylinder a τ D) :=
  (straightenedPointHomeomorph g hg).isCompact_preimage.mpr
    (isCompact_Icc.prod hD.isCompact_closure)

end HypoellipticAleksandrov.KineticAleksandrov

module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifyWeakCoordinates

/-! # Native-coordinate compact-test identities for the construction -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory

/-- A packed weak directional derivative transfers back to the native spatial carrier.
The measure-preserving chart introduces no Jacobian factor. -/
theorem construction_weak_directional_native {d : ℕ}
    (u g : PDE.Vec (d + d) → ℝ) (z : PDE.Vec (d + d))
    (hweak : ∀ test : PDE.Vec (d + d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) test →
      HasCompactSupport test →
      (∫ x, u x * fderiv ℝ test x z) = -(∫ x, g x * test x))
    (test : XV d → ℝ) (ht : ContDiff ℝ (⊤ : ℕ∞) test)
    (hs : HasCompactSupport test) :
    (∫ q, u ((spatialCoordinateCLE d).symm q) *
      fderiv ℝ test q (spatialCoordinateCLE d z)) =
      -(∫ q, g ((spatialCoordinateCLE d).symm q) * test q) := by
  let e := spatialCoordinateCLE d
  let psi := test ∘ e
  have hp : ContDiff ℝ (⊤ : ℕ∞) psi := ht.comp e.contDiff
  have hc : HasCompactSupport psi := hs.comp_homeomorph e.toHomeomorph
  have hd : ∀ x, fderiv ℝ psi x z = fderiv ℝ test (e x) (e z) := by
    intro x
    have he := (ht.differentiable (by simp) (e x)).hasFDerivAt.comp x e.hasFDerivAt
    rw [he.fderiv]
    rfl
  have hL := (measurePreserving_spatialCoordinate d).integral_comp'
    (fun q => u (e.symm q) * fderiv ℝ test q (e z))
  have hR := (measurePreserving_spatialCoordinate d).integral_comp'
    (fun q => g (e.symm q) * test q)
  have hLn : (∫ x, u x * fderiv ℝ psi x z) =
      ∫ q, u (e.symm q) * fderiv ℝ test q (e z) := by
    simpa only [spatialCoordinateMeasurableEquiv_apply,
      hd, e, ContinuousLinearEquiv.symm_apply_apply] using! hL
  have hRn : (∫ x, g x * psi x) = ∫ q, g (e.symm q) * test q := by
    simpa only [spatialCoordinateMeasurableEquiv_apply,
      psi, Function.comp_apply, e, ContinuousLinearEquiv.symm_apply_apply] using! hR
  exact hLn.symm.trans ((hweak psi hp hc).trans (congrArg Neg.neg hRn))

/-- Local integrability transfers to the native carrier through the same chart. -/
theorem construction_locallyIntegrable_native {d : ℕ} (f : PDE.Vec (d + d) → ℝ)
    (hf : LocallyIntegrable f volume) :
    LocallyIntegrable (fun q => f ((spatialCoordinateCLE d).symm q)) volume := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  let e := spatialCoordinateMeasurableEquiv d
  have hK' : IsCompact (e.symm '' K) :=
    hK.image (spatialCoordinateCLE d).symm.continuous
  have hi := hf.integrableOn_isCompact hK'
  have hm := (measurePreserving_spatialCoordinate d).symm.restrict_image_emb
    e.symm.measurableEmbedding K
  have he := hm.integrable_comp_of_integrable hi
  simpa only [Function.comp_def, e] using! he

/-- Almost-everywhere statements transfer to the native carrier without exceptional mass. -/
theorem construction_ae_native {d : ℕ} (prop : PDE.Vec (d + d) → Prop)
    (hp : ∀ᵐ x ∂volume, prop x) :
    ∀ᵐ q ∂volume, prop ((spatialCoordinateCLE d).symm q) :=
  (measurePreserving_spatialCoordinate d).symm.quasiMeasurePreserving.ae hp

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

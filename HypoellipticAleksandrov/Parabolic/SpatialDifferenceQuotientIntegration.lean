module

public import PDEFoundation.Ambient.Basis
public import PDEFoundation.Measure.AffineVolume

/-!
# Spatial difference-quotient integration

This file gives the coefficient-free set-integral transposition identity for a
backward spatial difference quotient against a compactly supported function.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace HypoellipticAleksandrov.Parabolic

/-- A backward spatial difference quotient transposes to the forward quotient
over a raw set containing the support of the test function and its shift. -/
theorem setIntegral_mul_backwardSpatialDifferenceQuotient_eq
    {d : ℕ} (Ω : Set (PDE.Vec d))
    (k : Fin d) (h : ℝ) (f g : PDE.Vec d → ℝ)
    (hf : Continuous f) (hg : Continuous g)
    (hgcompact : HasCompactSupport g)
    (hgΩ : tsupport g ⊆ Ω)
    (hgshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport g) Ω) :
    (∫ y in Ω, f y *
      ((g (y + (-h) • PDE.basisVec k) - g y) / h) ∂volume) =
      ∫ y in Ω,
        ((f (y + h • PDE.basisVec k) - f y) / h) * g y ∂volume := by
  rcases eq_or_ne h 0 with rfl | hh
  · simp
  let z : PDE.Vec d := h • PDE.basisVec k
  let F : PDE.Vec d → ℝ := fun y => f (y + z) * g y
  let G : PDE.Vec d → ℝ := fun y => f y * g y
  have hFcont : Continuous F := by
    change Continuous ((fun y => f (y + z)) * g)
    exact (hf.comp (continuous_id.add continuous_const)).mul hg
  have hGcont : Continuous G := by
    change Continuous (f * g)
    exact hf.mul hg
  have hFsupport : HasCompactSupport F := by
    change HasCompactSupport ((fun y => f (y + z)) * g)
    exact hgcompact.mul_left
  have hGsupport : HasCompactSupport G := by
    change HasCompactSupport (f * g)
    exact hgcompact.mul_left
  have hF : Integrable F volume := hFcont.integrable_of_hasCompactSupport hFsupport
  have hG : Integrable G volume := hGcont.integrable_of_hasCompactSupport hGsupport
  have hFshift : Integrable (fun y => F (y - z)) volume := by
    exact (hFcont.comp (continuous_id.sub continuous_const)).integrable_of_hasCompactSupport
      (hFsupport.comp_homeomorph (Homeomorph.subRight z))
  have hshift : (∫ y, F (y - z) ∂volume) = ∫ y, F y ∂volume := by
    let hμ : MeasurePreserving (fun y : PDE.Vec d => y + -z) volume volume :=
      measurePreserving_add_right volume (-z)
    simpa [sub_eq_add_neg] using
      hμ.integral_comp (Homeomorph.addRight (-z)).measurableEmbedding F
  calc
    (∫ y in Ω, f y * ((g (y + (-h) • PDE.basisVec k) - g y) / h) ∂volume) =
        ∫ y, (F (y - z) - G y) / h ∂volume := by
      rw [show (fun y => f y * ((g (y + (-h) • PDE.basisVec k) - g y) / h)) =
          fun y => (F (y - z) - G y) / h by
        funext y
        dsimp [F, G, z]
        rw [neg_smul]
        simp only [sub_eq_add_neg]
        ring_nf]
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      have hnot : y - z ∉ tsupport g := by
        intro hsupport
        apply hy
        have := hgshift hsupport
        simpa [z, sub_eq_add_neg, add_assoc] using this
      have hnot' : y ∉ tsupport g := by
        intro hsupport
        exact hy (hgΩ hsupport)
      dsimp [F, G, z]
      rw [image_eq_zero_of_notMem_tsupport hnot]
      rw [image_eq_zero_of_notMem_tsupport hnot']
      ring
    _ = ((∫ y, F (y - z) ∂volume) - ∫ y, G y ∂volume) / h := by
      rw [integral_div, integral_sub hFshift hG]
    _ = ((∫ y, F y ∂volume) - ∫ y, G y ∂volume) / h := by rw [hshift]
    _ = ∫ y, (F y - G y) / h ∂volume := by
      rw [← integral_sub hF hG, ← integral_div]
    _ = ∫ y in Ω, ((f (y + h • PDE.basisVec k) - f y) / h) * g y ∂volume := by
      rw [show (fun y => ((f (y + h • PDE.basisVec k) - f y) / h) * g y) =
          fun y => (F y - G y) / h by
        funext y
        dsimp [F, G, z]
        ring]
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      have hnot : y ∉ tsupport g := by
        intro hsupport
        exact hy (hgΩ hsupport)
      dsimp [F, G]
      rw [image_eq_zero_of_notMem_tsupport hnot]
      ring

end HypoellipticAleksandrov.Parabolic

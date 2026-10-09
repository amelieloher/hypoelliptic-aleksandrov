module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionExtensionSecond

/-! # Mollification of the literal zero extension and its selected spatial jets -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory

/-- The selected first representative on the native carrier. -/
def constructionExtendedNativeGradient {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R m t : ℝ)
    (q : XV d) (i : Fin (d + d)) : ℝ :=
  constructionExtendedPackedGradient h r mu R m t ((spatialCoordinateCLE d).symm q) i

/-- The selected second velocity representative on the native carrier. -/
def constructionExtendedNativeHessian {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R m t : ℝ)
    (q : XV d) (i k : Fin d) : ℝ :=
  constructionExtendedPackedHessian h r mu R m t ((spatialCoordinateCLE d).symm q) i k

/-- Spatial convolution differentiates to convolution of the selected first representatives. -/
theorem construction_mollified_first_jet {d : ℕ} (hd : 1 ≤ d)
    {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r mu R m : ℝ)
    (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R) (hm : m < R ^ 2)
    (hscale : 2 * Real.rpow r alpha ≤ 1)
    (hmargin : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 ≤ m)
    (t : ℝ) (i : Fin (d + d)) (phi : ContDiffBump (0 : XV d)) (q : XV d) :
    fderiv ℝ (spatialMollify phi (fun y =>
      zeroExtendedProfile (profileFunction h) alpha r mu R ⟨t, y.1, y.2⟩)) q
        (spatialCoordinateCLE d (PDE.basisVec i)) =
      spatialMollify phi (fun y => constructionExtendedNativeGradient h r mu R m t y i) q := by
  have hc := continuous_zeroExtendedProfile_spatial_of_profile h r mu R hr hmu hR hscale
    (fun y hy => (hmargin y hy).trans_lt hm) t
  exact mollify_weak_directional_jet phi _ _ hc.locallyIntegrable _
    (construction_zero_extension_weak_native hd ha ha1 h r mu R m hr hmu hR hm
      hscale hmargin t i) q

/-- The first velocity representative differentiates after convolution to the selected Hessian. -/
theorem construction_mollified_velocityJet_derivative {d : ℕ} (hd : 1 ≤ d)
    {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r)
    (mu R m t : ℝ) (i k : Fin d) (phi : ContDiffBump (0 : XV d)) (q : XV d) :
    fderiv ℝ (spatialMollify phi (fun y =>
      constructionExtendedNativeGradient h r mu R m t y (Fin.natAdd d k))) q
      (0, PDE.basisVec i) =
      spatialMollify phi (fun y => constructionExtendedNativeHessian h r mu R m t y i k) q := by
  have hL := construction_locallyIntegrable_native _
    (construction_extendedGradient_locallyIntegrable h r hr mu R m t (Fin.natAdd d k))
  apply mollify_weak_directional_jet phi _ _ hL _ _ q
  intro test ht hs
  have he := construction_weak_directional_native
    (fun x => constructionExtendedPackedGradient h r mu R m t x (Fin.natAdd d k))
    (fun x => constructionExtendedPackedHessian h r mu R m t x i k)
    (PDE.basisVec (Fin.natAdd d i))
    (construction_extended_velocityJet_weak hd ha ha1 h r hr mu R m t i k) test ht hs
  simpa only [spatialCoordinate_basis_velocity, constructionExtendedNativeGradient,
    constructionExtendedNativeHessian] using! he

/-- The actual second velocity derivatives of the mollified value use the same Hessian. -/
theorem construction_mollified_second_velocity_jet {d : ℕ} (hd : 1 ≤ d)
    {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r mu R m : ℝ)
    (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R) (hm : m < R ^ 2)
    (hscale : 2 * Real.rpow r alpha ≤ 1)
    (hmargin : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 ≤ m)
    (t : ℝ) (i k : Fin d) (phi : ContDiffBump (0 : XV d)) (q : XV d) :
    dvv (spatialMollify phi (fun y =>
      zeroExtendedProfile (profileFunction h) alpha r mu R ⟨t, y.1, y.2⟩)) q i k =
      spatialMollify phi (fun y => constructionExtendedNativeHessian h r mu R m t y i k) q := by
  have he : (fun y => dv (spatialMollify phi (fun z =>
      zeroExtendedProfile (profileFunction h) alpha r mu R ⟨t, z.1, z.2⟩)) y k) =
      spatialMollify phi (fun y => constructionExtendedNativeGradient h r mu R m t y
        (Fin.natAdd d k)) := by
    funext y
    have hj := construction_mollified_first_jet hd ha ha1 h r mu R m hr hmu hR hm
      hscale hmargin t (Fin.natAdd d k) phi y
    rw [spatialCoordinate_basis_velocity] at hj
    simpa only [dv, PDE.basisVec] using! hj
  change fderiv ℝ (fun y => dv (spatialMollify phi (fun z =>
    zeroExtendedProfile (profileFunction h) alpha r mu R ⟨t, z.1, z.2⟩)) y k) q
      (0, PDE.basisVec i) = _
  rw [he]
  exact construction_mollified_velocityJet_derivative hd ha ha1 h r hr mu R m t i k phi q

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

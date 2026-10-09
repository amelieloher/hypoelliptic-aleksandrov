module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionCutoff
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionLocalBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionNativeWeak
public import PDEFoundation.Sobolev.WeakDerivative.Product

/-! # First weak derivatives of the literal zero extension -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory Set

/-- The smooth velocity cutoff in packed coordinates. -/
def constructionPackedCutoff (d : ℕ) (m R : ℝ) (x : PDE.Vec (d + d)) : ℝ :=
  constructionVelocityCutoff m R (spatialCoordinateCLE d x)

/-- The selected first weak derivative of the actual extended profile. -/
def constructionExtendedPackedGradient {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R m t : ℝ)
    (x : PDE.Vec (d + d)) (i : Fin (d + d)) : ℝ :=
  constructionPackedCutoff d m R x * spatialPackedCutoffGradient h r mu R t x i +
    spatialPackedCutoffValue h r mu R t x *
      fderiv ℝ (constructionPackedCutoff d m R) x (PDE.basisVec i)

/-- The packed multiplier is smooth at every finite order. -/
theorem contDiff_providerPackedCutoff (d : ℕ) (m R : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (constructionPackedCutoff d m R) :=
  (contDiff_providerVelocityCutoff d m R).comp (spatialCoordinateCLE d).contDiff

/-- The exact zero extension satisfies the first compact-test identities globally. -/
theorem construction_zero_extension_weak_first {d : ℕ} (hd : 1 ≤ d)
    {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r mu R m : ℝ)
    (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R) (hm : m < R ^ 2)
    (hscale : 2 * Real.rpow r alpha ≤ 1)
    (hmargin : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 ≤ m)
    (t : ℝ) (i : Fin (d + d)) (test : PDE.Vec (d + d) → ℝ)
    (ht : ContDiff ℝ (⊤ : ℕ∞) test) (hs : HasCompactSupport test) :
    (∫ x, zeroExtendedProfile (profileFunction h) alpha r mu R
        ⟨t, (spatialCoordinateCLE d x).1, (spatialCoordinateCLE d x).2⟩ *
      fderiv ℝ test x (PDE.basisVec i)) =
      -(∫ x, constructionExtendedPackedGradient h r mu R m t x i * test x) := by
  have hw := weakPartial_on_of_global univ i (spatialPackedCutoffValue h r mu R t)
    (fun x => spatialPackedCutoffGradient h r mu R t x i)
    (spatialPackedCutoff_weak_first_of_profile hd ha ha1 h r hr mu R t i)
  have hu : LocallyIntegrable (spatialPackedCutoffValue h r mu R t)
      (PDE.volumeOn univ) := by
    simpa only [PDE.volumeOn, Measure.restrict_univ] using
      (construction_cutoffValue_continuous h r mu R t).locallyIntegrable
  have hg : LocallyIntegrable (fun x => spatialPackedCutoffGradient h r mu R t x i)
      (PDE.volumeOn univ) := by
    simpa only [PDE.volumeOn, Measure.restrict_univ] using
      construction_cutoffGradient_locallyIntegrable h r hr mu R t i
  have he := hw.mul_contDiff (contDiff_providerPackedCutoff d m R) hu hg
    test ht hs (subset_univ _)
  have hz : ∀ x : PDE.Vec (d + d),
      zeroExtendedProfile (profileFunction h) alpha r mu R
        ⟨t, (spatialCoordinateCLE d x).1, (spatialCoordinateCLE d x).2⟩ =
      constructionPackedCutoff d m R x * spatialPackedCutoffValue h r mu R t x := by
    intro x
    exact construction_zero_extension_eq_cutoff h r mu R m hr hmu hR hm hscale hmargin _
  simpa only [Measure.restrict_univ, constructionExtendedPackedGradient, ← hz] using! he

/-- The same selected representatives satisfy the first identities on the native carrier. -/
theorem construction_zero_extension_weak_native {d : ℕ} (hd : 1 ≤ d)
    {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r mu R m : ℝ)
    (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R) (hm : m < R ^ 2)
    (hscale : 2 * Real.rpow r alpha ≤ 1)
    (hmargin : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 ≤ m)
    (t : ℝ) (i : Fin (d + d)) (test : XV d → ℝ)
    (ht : ContDiff ℝ (⊤ : ℕ∞) test) (hs : HasCompactSupport test) :
    (∫ q, zeroExtendedProfile (profileFunction h) alpha r mu R ⟨t, q.1, q.2⟩ *
      fderiv ℝ test q (spatialCoordinateCLE d (PDE.basisVec i))) =
      -(∫ q, constructionExtendedPackedGradient h r mu R m t
        ((spatialCoordinateCLE d).symm q) i * test q) := by
  have he := construction_weak_directional_native
    (fun x => zeroExtendedProfile (profileFunction h) alpha r mu R
      ⟨t, (spatialCoordinateCLE d x).1, (spatialCoordinateCLE d x).2⟩)
    (fun x => constructionExtendedPackedGradient h r mu R m t x i) (PDE.basisVec i)
    (construction_zero_extension_weak_first hd ha ha1 h r mu R m hr hmu hR hm
      hscale hmargin t i) test ht hs
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using! he

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

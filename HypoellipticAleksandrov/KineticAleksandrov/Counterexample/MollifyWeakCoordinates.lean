module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifyCoordinates
public import PDEFoundation.Sobolev.WeakDerivative
public import PDEFoundation.Geometry.ConvexDomain
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifyWeakJets
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Transfer of native weak identities into the existing Sobolev chart -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory

/-- A global weak directional derivative transfers through the native spatial chart.
The chart preserves measure, so no determinant or normalization factor occurs. -/
theorem weak_directional_spatialCoordinate {d : ℕ} (u g : XV d → ℝ)
    (w : XV d) (z : PDE.Vec (d + d)) (hz : spatialCoordinateCLE d z = w)
    (hweak : ∀ test : XV d → ℝ, ContDiff ℝ (⊤ : ℕ∞) test →
      HasCompactSupport test →
      (∫ q, u q * fderiv ℝ test q w) = -(∫ q, g q * test q))
    (test : PDE.Vec (d + d) → ℝ) (ht : ContDiff ℝ (⊤ : ℕ∞) test)
    (hs : HasCompactSupport test) :
    (∫ x, u (spatialCoordinateCLE d x) * fderiv ℝ test x z) =
      -(∫ x, g (spatialCoordinateCLE d x) * test x) := by
  let e := spatialCoordinateCLE d
  let psi := test ∘ e.symm
  have hp : ContDiff ℝ (⊤ : ℕ∞) psi := ht.comp e.symm.contDiff
  have hc : HasCompactSupport psi := hs.comp_homeomorph e.symm.toHomeomorph
  have hd : ∀ x, fderiv ℝ psi (e x) w = fderiv ℝ test x z := by
    intro x
    have he := (ht.differentiable (by simp) (e.symm (e x))).hasFDerivAt.comp (e x)
      e.symm.hasFDerivAt
    have he' : HasFDerivAt psi ((fderiv ℝ test x).comp e.symm.toContinuousLinearMap)
        (e x) := by
      simpa only [psi, e.symm_apply_apply] using! he
    rw [he'.fderiv]
    change fderiv ℝ test x (e.symm w) = fderiv ℝ test x z
    rw [← hz]
    simp only [e, ContinuousLinearEquiv.symm_apply_apply]
  have hL := (measurePreserving_spatialCoordinate d).integral_comp'
    (fun q => u q * fderiv ℝ psi q w)
  have hR := (measurePreserving_spatialCoordinate d).integral_comp'
    (fun q => g q * psi q)
  have hLn : (∫ x, u (e x) * fderiv ℝ test x z) =
      ∫ q, u q * fderiv ℝ psi q w := by
    simpa only [spatialCoordinateMeasurableEquiv_apply, ← hd] using! hL
  have hRn : (∫ x, g (e x) * test x) = ∫ q, g q * psi q := by
    simpa only [spatialCoordinateMeasurableEquiv_apply, psi, Function.comp_apply,
      e, ContinuousLinearEquiv.symm_apply_apply] using! hR
  exact hLn.trans ((hweak psi hp hc).trans (congrArg Neg.neg hRn.symm))

/-- A global weak coordinate identity restricts to any domain for tests supported inside it. -/
theorem weakPartial_on_of_global {d : ℕ} (D : Set (PDE.Vec d)) (i : Fin d)
    (u g : PDE.Vec d → ℝ)
    (hweak : ∀ test : PDE.Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) test →
      HasCompactSupport test →
      (∫ x, u x * fderiv ℝ test x (PDE.basisVec i)) = -(∫ x, g x * test x)) :
    PDE.HasWeakPartialDerivOn D i u g := by
  intro test ht hc hs
  have hL : (∫ x in D, u x * fderiv ℝ test x (PDE.basisVec i)) =
      ∫ x, u x * fderiv ℝ test x (PDE.basisVec i) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (hs h))]
    simp only [zero_apply, mul_zero]
  have hR : (∫ x in D, g x * test x) = ∫ x, g x * test x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), mul_zero]
  rw [hL, hR]
  exact hweak test ht hc

/-- A first jet has the corresponding weak derivative when first and second
integration-by-parts identities use the same representatives. -/
theorem weak_first_jet_of_second {d : ℕ} (u g h : XV d → ℝ) (w z : XV d)
    (hfirst : ∀ test : XV d → ℝ, ContDiff ℝ (⊤ : ℕ∞) test →
      HasCompactSupport test →
      (∫ q, u q * fderiv ℝ test q w) = -(∫ q, g q * test q))
    (hsecond : ∀ test : XV d → ℝ, ContDiff ℝ (⊤ : ℕ∞) test →
      HasCompactSupport test →
      (∫ q, u q * fderiv ℝ (fun x => fderiv ℝ test x z) q w) =
        ∫ q, h q * test q)
    (test : XV d → ℝ) (ht : ContDiff ℝ (⊤ : ℕ∞) test)
    (hs : HasCompactSupport test) :
    (∫ q, g q * fderiv ℝ test q z) = -(∫ q, h q * test q) := by
  have hdt : ContDiff ℝ (⊤ : ℕ∞) (fun q => fderiv ℝ test q z) :=
    (ht.contDiff_fderiv_apply (by simp)).comp (contDiff_id.prodMk contDiff_const)
  have ha := hfirst (fun q => fderiv ℝ test q z) hdt
    (hs.fderiv_apply (𝕜 := ℝ) z)
  rw [hsecond test ht hs] at ha
  simpa only [neg_neg] using (congrArg Neg.neg ha).symm

/-- Weak coordinate identities on all bounded convex neighborhoods give the global
compact-test identity, by enclosing each actual test support in a metric ball. -/
theorem weakPartial_global_of_locals {d : ℕ} (i : Fin d) (u g : PDE.Vec d → ℝ)
    (hweak : ∀ D : Set (PDE.Vec d), PDE.IsOpenBoundedConvexDomain D →
      PDE.HasWeakPartialDerivOn D i u g)
    (test : PDE.Vec d → ℝ) (ht : ContDiff ℝ (⊤ : ℕ∞) test)
    (hs : HasCompactSupport test) :
    (∫ x, u x * fderiv ℝ test x (PDE.basisVec i)) = -(∫ x, g x * test x) := by
  obtain ⟨R, _, hR⟩ := hs.isCompact.isBounded.subset_ball_lt 0 (0 : PDE.Vec d)
  let D := Metric.ball (0 : PDE.Vec d) R
  have hD : PDE.IsOpenBoundedConvexDomain D :=
    ⟨Metric.isOpen_ball, PDE.Bornology.IsBounded.isBoundedDomain
      (Metric.isBounded_ball : Bornology.IsBounded D), convex_ball _ _⟩
  have he := hweak D hD test ht hs hR
  have hL : (∫ x in D, u x * fderiv ℝ test x (PDE.basisVec i)) =
      ∫ x, u x * fderiv ℝ test x (PDE.basisVec i) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (hR h))]
    simp only [zero_apply, mul_zero]
  have hR' : (∫ x in D, g x * test x) = ∫ x, g x * test x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hR h)), mul_zero]
  rwa [hL, hR'] at he

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

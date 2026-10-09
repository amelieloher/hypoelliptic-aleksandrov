module

public import PDEFoundation.Sobolev.WeakDerivative

/-!
# Linear algebra for weak first derivatives

The Bochner integral is not additive on arbitrary non-integrable functions.
Accordingly, the raw addition and subtraction lemmas below explicitly require
local integrability, with respect to the restricted measure, of both value
representatives and both weak-derivative representatives.

Negation and real scalar multiplication need no such hypotheses: the total
Bochner integral commutes with these operations without an integrability
assumption. These raw lemmas are the analytic input for the
representative-level `W^{1,p}` module structure when `1 ≤ p`.
-/

@[expose] public section

namespace PDE

namespace HasWeakPartialDerivOn

/-- Zero has zero weak partial derivative. -/
theorem zero {d : ℕ} {U : Set (Vec d)} {i : Fin d} :
    HasWeakPartialDerivOn U i (0 : Vec d → ℝ) 0 := by
  intro φ _hφSmooth _hφCompact _hφSupport
  simp only [Pi.zero_apply, zero_mul, MeasureTheory.integral_zero, neg_zero]

/-- Weak partial differentiation commutes with addition.

The four local-integrability assumptions are needed to apply additivity of the
Bochner integral to the two test-function pairings.
-/
theorem add {d : ℕ} {U : Set (Vec d)} {i : Fin d}
    {u v gi hi : Vec d → ℝ}
    (hu : HasWeakPartialDerivOn U i u gi)
    (hv : HasWeakPartialDerivOn U i v hi)
    (huLoc : MeasureTheory.LocallyIntegrable u (volumeOn U))
    (hvLoc : MeasureTheory.LocallyIntegrable v (volumeOn U))
    (hgiLoc : MeasureTheory.LocallyIntegrable gi (volumeOn U))
    (hhiLoc : MeasureTheory.LocallyIntegrable hi (volumeOn U)) :
    HasWeakPartialDerivOn U i (u + v) (gi + hi) := by
  intro φ hφSmooth hφCompact hφSupport
  let dφ : Vec d → ℝ :=
    fun x => (fderiv ℝ φ x) (basisVec i)
  have hdφContinuous : Continuous dφ := by
    simpa only [dφ] using
      (hφSmooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφCompact : HasCompactSupport dφ := by
    simpa only [dφ] using
      hφCompact.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have huIntegrable :
      MeasureTheory.Integrable (fun x => u x * dφ x) (volumeOn U) := by
    simpa only [smul_eq_mul] using
      huLoc.integrable_smul_right_of_hasCompactSupport
        hdφContinuous hdφCompact
  have hvIntegrable :
      MeasureTheory.Integrable (fun x => v x * dφ x) (volumeOn U) := by
    simpa only [smul_eq_mul] using
      hvLoc.integrable_smul_right_of_hasCompactSupport
        hdφContinuous hdφCompact
  have hgiIntegrable :
      MeasureTheory.Integrable (fun x => gi x * φ x) (volumeOn U) := by
    simpa only [smul_eq_mul] using
      hgiLoc.integrable_smul_right_of_hasCompactSupport
        hφSmooth.continuous hφCompact
  have hhiIntegrable :
      MeasureTheory.Integrable (fun x => hi x * φ x) (volumeOn U) := by
    simpa only [smul_eq_mul] using
      hhiLoc.integrable_smul_right_of_hasCompactSupport
        hφSmooth.continuous hφCompact
  have huWeak := hu φ hφSmooth hφCompact hφSupport
  have hvWeak := hv φ hφSmooth hφCompact hφSupport
  change
    (∫ x, u x * dφ x ∂(volumeOn U)) =
      -(∫ x, gi x * φ x ∂(volumeOn U)) at huWeak
  change
    (∫ x, v x * dφ x ∂(volumeOn U)) =
      -(∫ x, hi x * φ x ∂(volumeOn U)) at hvWeak
  change
    (∫ x, (u + v) x * dφ x ∂(volumeOn U)) =
      -(∫ x, (gi + hi) x * φ x ∂(volumeOn U))
  calc
    (∫ x, (u + v) x * dφ x ∂(volumeOn U)) =
        ∫ x, u x * dφ x + v x * dφ x ∂(volumeOn U) := by
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall fun x => by
            simp only [Pi.add_apply, add_mul]
    _ = (∫ x, u x * dφ x ∂(volumeOn U)) +
          ∫ x, v x * dφ x ∂(volumeOn U) := by
            rw [MeasureTheory.integral_add huIntegrable hvIntegrable]
    _ = (-(∫ x, gi x * φ x ∂(volumeOn U))) +
          (-(∫ x, hi x * φ x ∂(volumeOn U))) := by
            rw [huWeak, hvWeak]
    _ = -((∫ x, gi x * φ x ∂(volumeOn U)) +
          ∫ x, hi x * φ x ∂(volumeOn U)) :=
      (neg_add _ _).symm
    _ = -(∫ x, gi x * φ x + hi x * φ x ∂(volumeOn U)) := by
          rw [MeasureTheory.integral_add hgiIntegrable hhiIntegrable]
    _ = -(∫ x, (gi + hi) x * φ x ∂(volumeOn U)) := by
          congr 1
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall fun x => by
            simp only [Pi.add_apply, add_mul]

/-- Weak partial differentiation commutes with real scalar multiplication. -/
theorem smul {d : ℕ} {U : Set (Vec d)} {i : Fin d}
    {u gi : Vec d → ℝ}
    (h : HasWeakPartialDerivOn U i u gi) (c : ℝ) :
    HasWeakPartialDerivOn U i (c • u) (c • gi) := by
  intro φ hφSmooth hφCompact hφSupport
  let dφ : Vec d → ℝ :=
    fun x => (fderiv ℝ φ x) (basisVec i)
  have hWeak := h φ hφSmooth hφCompact hφSupport
  change
    (∫ x, u x * dφ x ∂(volumeOn U)) =
      -(∫ x, gi x * φ x ∂(volumeOn U)) at hWeak
  change
    (∫ x, (c • u) x * dφ x ∂(volumeOn U)) =
      -(∫ x, (c • gi) x * φ x ∂(volumeOn U))
  calc
    (∫ x, (c • u) x * dφ x ∂(volumeOn U)) =
        ∫ x, c * (u x * dφ x) ∂(volumeOn U) := by
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall fun x => by
            simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
    _ = c * ∫ x, u x * dφ x ∂(volumeOn U) := by
          rw [MeasureTheory.integral_const_mul]
    _ = c * (-(∫ x, gi x * φ x ∂(volumeOn U))) := by
          rw [hWeak]
    _ = -(c * ∫ x, gi x * φ x ∂(volumeOn U)) := by
          rw [mul_neg]
    _ = -(∫ x, c * (gi x * φ x) ∂(volumeOn U)) := by
          rw [MeasureTheory.integral_const_mul]
    _ = -(∫ x, (c • gi) x * φ x ∂(volumeOn U)) := by
          congr 1
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall fun x => by
            simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- Weak partial differentiation commutes with negation. -/
theorem neg {d : ℕ} {U : Set (Vec d)} {i : Fin d}
    {u gi : Vec d → ℝ}
    (h : HasWeakPartialDerivOn U i u gi) :
    HasWeakPartialDerivOn U i (-u) (-gi) := by
  change HasWeakPartialDerivOn U i
    (fun x => -u x) (fun x => -gi x)
  have hs := h.smul (-1)
  change HasWeakPartialDerivOn U i
    (fun x => (-1 : ℝ) * u x) (fun x => (-1 : ℝ) * gi x) at hs
  simpa only [neg_one_mul] using hs

/-- Weak partial differentiation commutes with subtraction.

As for addition, local integrability of both values and both weak partial
representatives is essential.
-/
theorem sub {d : ℕ} {U : Set (Vec d)} {i : Fin d}
    {u v gi hi : Vec d → ℝ}
    (hu : HasWeakPartialDerivOn U i u gi)
    (hv : HasWeakPartialDerivOn U i v hi)
    (huLoc : MeasureTheory.LocallyIntegrable u (volumeOn U))
    (hvLoc : MeasureTheory.LocallyIntegrable v (volumeOn U))
    (hgiLoc : MeasureTheory.LocallyIntegrable gi (volumeOn U))
    (hhiLoc : MeasureTheory.LocallyIntegrable hi (volumeOn U)) :
    HasWeakPartialDerivOn U i (u - v) (gi - hi) := by
  simpa only [sub_eq_add_neg] using
    hu.add hv.neg huLoc hvLoc.neg hgiLoc hhiLoc.neg

end HasWeakPartialDerivOn

namespace HasWeakGradientOn

/-- The zero vector field is a weak gradient of the zero function. -/
theorem zero {d : ℕ} {U : Set (Vec d)} :
    HasWeakGradientOn U (0 : Vec d → ℝ) 0 := by
  intro i
  exact HasWeakPartialDerivOn.zero

/-- Weak gradients commute with addition under the local-integrability
hypotheses needed coordinatewise by the raw Bochner identities. -/
theorem add {d : ℕ} {U : Set (Vec d)}
    {u v : Vec d → ℝ} {Du Dv : Vec d → Vec d}
    (hu : HasWeakGradientOn U u Du)
    (hv : HasWeakGradientOn U v Dv)
    (huLoc : MeasureTheory.LocallyIntegrable u (volumeOn U))
    (hvLoc : MeasureTheory.LocallyIntegrable v (volumeOn U))
    (hDuLoc : ∀ i, MeasureTheory.LocallyIntegrable
      (fun x => Du x i) (volumeOn U))
    (hDvLoc : ∀ i, MeasureTheory.LocallyIntegrable
      (fun x => Dv x i) (volumeOn U)) :
    HasWeakGradientOn U (u + v) (Du + Dv) := by
  intro i
  simpa only [Pi.add_apply] using!
    (hu i).add (hv i) huLoc hvLoc (hDuLoc i) (hDvLoc i)

/-- Weak gradients commute with real scalar multiplication. -/
theorem smul {d : ℕ} {U : Set (Vec d)}
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (h : HasWeakGradientOn U u Du) (c : ℝ) :
    HasWeakGradientOn U (c • u) (c • Du) := by
  intro i
  simpa only [Pi.smul_apply, smul_eq_mul] using! (h i).smul c

/-- Weak gradients commute with negation. -/
theorem neg {d : ℕ} {U : Set (Vec d)}
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (h : HasWeakGradientOn U u Du) :
    HasWeakGradientOn U (-u) (-Du) := by
  intro i
  simpa only [Pi.neg_apply] using! (h i).neg

/-- Weak gradients commute with subtraction under the local-integrability
hypotheses needed coordinatewise by the raw Bochner identities. -/
theorem sub {d : ℕ} {U : Set (Vec d)}
    {u v : Vec d → ℝ} {Du Dv : Vec d → Vec d}
    (hu : HasWeakGradientOn U u Du)
    (hv : HasWeakGradientOn U v Dv)
    (huLoc : MeasureTheory.LocallyIntegrable u (volumeOn U))
    (hvLoc : MeasureTheory.LocallyIntegrable v (volumeOn U))
    (hDuLoc : ∀ i, MeasureTheory.LocallyIntegrable
      (fun x => Du x i) (volumeOn U))
    (hDvLoc : ∀ i, MeasureTheory.LocallyIntegrable
      (fun x => Dv x i) (volumeOn U)) :
    HasWeakGradientOn U (u - v) (Du - Dv) := by
  intro i
  simpa only [Pi.sub_apply] using!
    (hu i).sub (hv i) huLoc hvLoc (hDuLoc i) (hDvLoc i)

end HasWeakGradientOn

end PDE

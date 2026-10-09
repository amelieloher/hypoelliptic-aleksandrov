module

public import HypoellipticAleksandrov.Parabolic.Geometry
public import PDEFoundation.Ambient.Basis
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Support

/-!
# Raw spatial difference quotients

This module records the algebra, smoothness, and support transport of forward
translations in one native velocity coordinate. It deliberately makes no
domain, equation, or nonzero-increment assumption.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

/-- Translation by `h` in the `k`th native velocity coordinate, fixing time. -/
def spatialShift {d : ℕ} (k : Fin d) (h : ℝ) :
    TimeVelocity d → TimeVelocity d :=
  fun z => z + (0, h • PDE.basisVec k)

/-- Precomposition by the forward spatial translation. -/
def spatialTranslate {d : ℕ} {α : Type*} (k : Fin d) (h : ℝ)
    (f : TimeVelocity d → α) : TimeVelocity d → α :=
  fun z => f (spatialShift k h z)

/-- The forward spatial difference quotient, totalized at zero increment. -/
noncomputable def spatialDifferenceQuotient {d : ℕ} (k : Fin d) (h : ℝ)
    (f : TimeVelocity d → ℝ) : TimeVelocity d → ℝ :=
  fun z => (spatialTranslate k h f z - f z) / h

/-- A spatial shift changes only the selected native velocity coordinate. -/
@[simp] theorem spatialShift_apply
    {d : ℕ} (k : Fin d) (h r : ℝ) (y : PDE.Vec d) :
    spatialShift k h (r, y) = (r, y + h • PDE.basisVec k) := by
  simp [spatialShift]

/-- A spatial translate evaluates at the corresponding shifted point. -/
@[simp] theorem spatialTranslate_apply
    {d : ℕ} {α : Type*} (k : Fin d) (h : ℝ)
    (f : TimeVelocity d → α) (z : TimeVelocity d) :
    spatialTranslate k h f z = f (spatialShift k h z) :=
  rfl

/-- A spatial difference quotient has its literal pointwise value. -/
@[simp] theorem spatialDifferenceQuotient_apply
    {d : ℕ} (k : Fin d) (h : ℝ) (f : TimeVelocity d → ℝ)
    (z : TimeVelocity d) :
    spatialDifferenceQuotient k h f z =
      (spatialTranslate k h f z - f z) / h :=
  rfl

/-- A zero spatial shift is the identity. -/
@[simp] theorem spatialShift_zero {d : ℕ} (k : Fin d) :
    spatialShift k 0 = id := by
  funext z
  rcases z with ⟨r, y⟩
  simp [spatialShift]

/-- Successive shifts in one coordinate add their increments. -/
theorem spatialShift_comp {d : ℕ} (k : Fin d) (h₁ h₂ : ℝ) :
    spatialShift k h₂ ∘ spatialShift k h₁ =
      spatialShift k (h₁ + h₂) := by
  funext z
  rcases z with ⟨r, y⟩
  simp [spatialShift, add_smul, add_assoc]

/-- Translation by zero fixes every function. -/
@[simp] theorem spatialTranslate_zero
    {d : ℕ} {α : Type*} (k : Fin d) (f : TimeVelocity d → α) :
    spatialTranslate k 0 f = f := by
  funext z
  simp [spatialTranslate]

/-- Successive translations in one coordinate add their increments. -/
theorem spatialTranslate_comp
    {d : ℕ} {α : Type*} (k : Fin d) (h₁ h₂ : ℝ)
    (f : TimeVelocity d → α) :
    spatialTranslate k h₂ (spatialTranslate k h₁ f) =
      spatialTranslate k (h₁ + h₂) f := by
  funext z
  rcases z with ⟨r, y⟩
  simp only [spatialTranslate, spatialShift, Prod.mk_add_mk, add_zero]
  congr 1
  congr 1
  rw [add_assoc, add_comm h₁ h₂, add_smul]

/-- Spatial translation preserves pointwise addition. -/
theorem spatialTranslate_add
    {d : ℕ} {α : Type*} [Add α] (k : Fin d) (h : ℝ)
    (f g : TimeVelocity d → α) :
    spatialTranslate k h (f + g) =
      spatialTranslate k h f + spatialTranslate k h g :=
  rfl

/-- Spatial translation preserves pointwise negation. -/
theorem spatialTranslate_neg
    {d : ℕ} {α : Type*} [Neg α] (k : Fin d) (h : ℝ)
    (f : TimeVelocity d → α) :
    spatialTranslate k h (-f) = -spatialTranslate k h f :=
  rfl

/-- Spatial translation commutes with constant scalar multiplication. -/
theorem spatialTranslate_smul
    {d : ℕ} {R α : Type*} [SMul R α] (c : R)
    (k : Fin d) (h : ℝ) (f : TimeVelocity d → α) :
    spatialTranslate k h (c • f) = c • spatialTranslate k h f :=
  rfl

/-- Spatial difference quotients preserve addition. -/
theorem spatialDifferenceQuotient_add
    {d : ℕ} (k : Fin d) (h : ℝ) (f g : TimeVelocity d → ℝ) :
    spatialDifferenceQuotient k h (f + g) =
      spatialDifferenceQuotient k h f + spatialDifferenceQuotient k h g := by
  funext z
  simp only [spatialDifferenceQuotient_apply, spatialTranslate_apply, Pi.add_apply]
  ring

/-- Spatial difference quotients preserve negation. -/
theorem spatialDifferenceQuotient_neg
    {d : ℕ} (k : Fin d) (h : ℝ) (f : TimeVelocity d → ℝ) :
    spatialDifferenceQuotient k h (-f) =
      -spatialDifferenceQuotient k h f := by
  funext z
  simp only [spatialDifferenceQuotient_apply, spatialTranslate_apply, Pi.neg_apply]
  ring

/-- Spatial difference quotients commute with constant scalar multiplication. -/
theorem spatialDifferenceQuotient_smul
    {d : ℕ} (c : ℝ) (k : Fin d) (h : ℝ)
    (f : TimeVelocity d → ℝ) :
    spatialDifferenceQuotient k h (c • f) =
      c • spatialDifferenceQuotient k h f := by
  funext z
  simp only [spatialDifferenceQuotient_apply, spatialTranslate_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Exact forward-translation product rule. -/
theorem spatialDifferenceQuotient_mul
    {d : ℕ} (k : Fin d) (h : ℝ)
    (f g : TimeVelocity d → ℝ) :
    spatialDifferenceQuotient k h (f * g) =
      spatialTranslate k h f * spatialDifferenceQuotient k h g +
        spatialDifferenceQuotient k h f * g := by
  funext z
  simp only [spatialDifferenceQuotient_apply, spatialTranslate_apply, Pi.add_apply, Pi.mul_apply]
  ring

/-- Global continuous differentiability is preserved by spatial translation. -/
theorem ContDiff.spatialTranslate
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ∞} {k : Fin d} {h : ℝ} {f : TimeVelocity d → E}
    (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (spatialTranslate k h f) := by
  change ContDiff ℝ n (f ∘ fun z : TimeVelocity d => z + (0, h • PDE.basisVec k))
  exact hf.comp (contDiff_id.add contDiff_const)

/-- Global continuous differentiability is preserved by spatial difference quotients. -/
theorem ContDiff.spatialDifferenceQuotient
    {d : ℕ} {n : ℕ∞} {k : Fin d} {h : ℝ}
    {f : TimeVelocity d → ℝ} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (spatialDifferenceQuotient k h f) := by
  change ContDiff ℝ n
    (fun z => (HypoellipticAleksandrov.Parabolic.spatialTranslate k h f z - f z) / h)
  exact (ContDiff.spatialTranslate hf |>.sub hf).div_const h

/-- Spatial translation pulls topological support back exactly by the shift. -/
theorem tsupport_spatialTranslate
    {d : ℕ} {α : Type*} [Zero α] (k : Fin d) (h : ℝ)
    (f : TimeVelocity d → α) :
    tsupport (spatialTranslate k h f) =
      (spatialShift k h) ⁻¹' tsupport f := by
  change tsupport (fun z => f (z + (0, h • PDE.basisVec k))) =
    (fun z => z + (0, h • PDE.basisVec k)) ⁻¹' tsupport f
  simpa only [Function.comp_def, Homeomorph.coe_addRight] using
    tsupport_comp_eq_preimage f
      (Homeomorph.addRight ((0, h • PDE.basisVec k) : TimeVelocity d))

/-- Translated-support membership is support membership after shifting. -/
theorem mem_tsupport_spatialTranslate_iff
    {d : ℕ} {α : Type*} [Zero α] (k : Fin d) (h : ℝ)
    (f : TimeVelocity d → α) (z : TimeVelocity d) :
    z ∈ tsupport (spatialTranslate k h f) ↔
      spatialShift k h z ∈ tsupport f := by
  rw [tsupport_spatialTranslate]
  rfl

end HypoellipticAleksandrov.Parabolic

module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.OriginalTimeSeparatedDistribution

/-!
# Original-time separated spacetime tests

This module packages literal products of scalar original-time tests and
spatial weak tests as Mathlib test functions on scalar parabolic cylinders.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The open-set carrier of the scalar original-time product cylinder. -/
def originalTimeOpenCylinderOpens
    {d : ℕ} (r₀ r₁ : ℝ) (Ω : Set (PDE.Vec d)) (hΩ : IsOpen Ω) :
    TopologicalSpace.Opens (TimeVelocity d) :=
  ⟨scalarParabolicOpenCylinder r₀ r₁ Ω, isOpen_Ioo.prod hΩ⟩

/-- The literal product of an original-time scalar test and a spatial weak test. -/
noncomputable def originalTimeSeparatedProduct
    {d : ℕ} {Ω : Set (PDE.Vec d)} {r₀ r₁ : ℝ}
    (φ : OriginalTimeScalarTest r₀ r₁) (ψ : PDE.WeakTestFunction Ω) :
    TimeVelocity d → ℝ :=
  fun z => φ z.1 * ψ z.2

/-- The raw separated product has its literal pointwise value. -/
@[simp] theorem originalTimeSeparatedProduct_apply
    {d : ℕ} {Ω : Set (PDE.Vec d)} {r₀ r₁ : ℝ}
    (φ : OriginalTimeScalarTest r₀ r₁) (ψ : PDE.WeakTestFunction Ω)
    (z : TimeVelocity d) :
    originalTimeSeparatedProduct φ ψ z = φ z.1 * ψ z.2 :=
  rfl

/-- The canonical compact carrier of a separated original-time product. -/
noncomputable def originalTimeSeparatedProductCompact
    {d : ℕ} {Ω : Set (PDE.Vec d)} {r₀ r₁ : ℝ}
    (φ : OriginalTimeScalarTest r₀ r₁) (ψ : PDE.WeakTestFunction Ω) :
    TopologicalSpace.Compacts (TimeVelocity d) :=
  ⟨tsupport (φ : ℝ → ℝ) ×ˢ tsupport (ψ : PDE.Vec d → ℝ),
    (hasCompactSupport_def.mp φ.hasCompactSupport).prod
      (hasCompactSupport_def.mp ψ.hasCompactSupport)⟩

/-- The canonical compact carrier lies in the scalar product cylinder. -/
theorem originalTimeSeparatedProductCompact_subset_cylinder
    {d : ℕ} {Ω : Set (PDE.Vec d)} {r₀ r₁ : ℝ}
    (φ : OriginalTimeScalarTest r₀ r₁) (ψ : PDE.WeakTestFunction Ω) :
    (originalTimeSeparatedProductCompact φ ψ : Set (TimeVelocity d)) ⊆
      scalarParabolicOpenCylinder r₀ r₁ Ω := by
  intro z hz
  exact ⟨φ.tsupport_subset hz.1, ψ.tsupport_subset hz.2⟩

/-- The product as a smooth map vanishing outside its canonical compact. -/
noncomputable def originalTimeSeparatedProductSupportedIn
    {d : ℕ} {Ω : Set (PDE.Vec d)} {r₀ r₁ : ℝ}
    (φ : OriginalTimeScalarTest r₀ r₁) (ψ : PDE.WeakTestFunction Ω) :
    ContDiffMapSupportedIn (TimeVelocity d) ℝ (⊤ : ℕ∞)
      (originalTimeSeparatedProductCompact φ ψ) where
  toFun := originalTimeSeparatedProduct φ ψ
  contDiff' := by
    simpa only [originalTimeSeparatedProduct, Function.comp_def, Pi.mul_def] using!
      (φ.contDiff.comp contDiff_fst).mul (ψ.contDiff.comp contDiff_snd)
  zero_on_compl' := by
    intro z hz
    simp only [mem_compl_iff] at hz
    rcases not_and_or.mp hz with hφ | hψ
    · simp [image_eq_zero_of_notMem_tsupport hφ]
    · simp [image_eq_zero_of_notMem_tsupport hψ]

/-- The fixed-compact separated product has its literal pointwise value. -/
@[simp] theorem originalTimeSeparatedProductSupportedIn_apply
    {d : ℕ} {Ω : Set (PDE.Vec d)} {r₀ r₁ : ℝ}
    (φ : OriginalTimeScalarTest r₀ r₁) (ψ : PDE.WeakTestFunction Ω)
    (z : TimeVelocity d) :
    originalTimeSeparatedProductSupportedIn φ ψ z = φ z.1 * ψ z.2 :=
  rfl

/-- The separated product as a Mathlib test on the open scalar cylinder. -/
noncomputable def originalTimeSeparatedProductTestFunction
    {d : ℕ} {Ω : Set (PDE.Vec d)} {r₀ r₁ : ℝ}
    (hΩ : IsOpen Ω) (φ : OriginalTimeScalarTest r₀ r₁)
    (ψ : PDE.WeakTestFunction Ω) :
    TestFunction (originalTimeOpenCylinderOpens r₀ r₁ Ω hΩ) ℝ (⊤ : ℕ∞) :=
  TestFunction.ofSupportedIn
    (originalTimeSeparatedProductCompact_subset_cylinder φ ψ)
    (originalTimeSeparatedProductSupportedIn φ ψ)

/-- The cylinder test has its literal pointwise value. -/
@[simp] theorem originalTimeSeparatedProductTestFunction_apply
    {d : ℕ} {Ω : Set (PDE.Vec d)} {r₀ r₁ : ℝ}
    (hΩ : IsOpen Ω) (φ : OriginalTimeScalarTest r₀ r₁)
    (ψ : PDE.WeakTestFunction Ω) (z : TimeVelocity d) :
    originalTimeSeparatedProductTestFunction hΩ φ ψ z = φ z.1 * ψ z.2 :=
  rfl

/-- The product test has exactly the product of the factor supports. -/
theorem tsupport_originalTimeSeparatedProductTestFunction
    {d : ℕ} {Ω : Set (PDE.Vec d)} {r₀ r₁ : ℝ}
    (hΩ : IsOpen Ω) (φ : OriginalTimeScalarTest r₀ r₁)
    (ψ : PDE.WeakTestFunction Ω) :
    tsupport
        (originalTimeSeparatedProductTestFunction hΩ φ ψ :
          TimeVelocity d → ℝ) =
      tsupport (φ : ℝ → ℝ) ×ˢ tsupport (ψ : PDE.Vec d → ℝ) := by
  have hsupport : Function.support (fun z : TimeVelocity d => φ z.1 * ψ z.2) =
      Function.support (φ : ℝ → ℝ) ×ˢ Function.support (ψ : PDE.Vec d → ℝ) := by
    ext z
    simp [Function.mem_support]
  change closure (Function.support (fun z : TimeVelocity d => φ z.1 * ψ z.2)) = _
  rw [hsupport, closure_prod_eq]
  rfl

/-- Its scalar time derivative differentiates only the time factor. -/
@[simp] theorem scalarTimeDerivative_originalTimeSeparatedProductTestFunction
    {d : ℕ} {Ω : Set (PDE.Vec d)} {r₀ r₁ : ℝ}
    (hΩ : IsOpen Ω) (φ : OriginalTimeScalarTest r₀ r₁)
    (ψ : PDE.WeakTestFunction Ω) (z : TimeVelocity d) :
    scalarTimeDerivative
        (originalTimeSeparatedProductTestFunction hΩ φ ψ) z =
      φ.deriv z.1 * ψ z.2 := by
  change deriv (fun r : ℝ => φ r * ψ z.2) z.1 = φ.deriv z.1 * ψ z.2
  rw [OriginalTimeScalarTest.deriv_apply]
  simpa only [Pi.mul_def, mul_zero, add_zero] using!
    ((φ.contDiff.differentiable (by simp)).differentiableAt.hasDerivAt.mul
      (hasDerivAt_const z.1 (ψ z.2))).deriv

/-- Each spatial coordinate derivative differentiates only the spatial factor. -/
@[simp] theorem scalarSpatialGradient_originalTimeSeparatedProductTestFunction_apply
    {d : ℕ} {Ω : Set (PDE.Vec d)} {r₀ r₁ : ℝ}
    (hΩ : IsOpen Ω) (φ : OriginalTimeScalarTest r₀ r₁)
    (ψ : PDE.WeakTestFunction Ω) (z : TimeVelocity d) (i : Fin d) :
    scalarSpatialGradient
        (originalTimeSeparatedProductTestFunction hΩ φ ψ) z i =
      φ z.1 * ψ.partialDeriv i z.2 := by
  change (fderiv ℝ (fun y : PDE.Vec d => φ z.1 * ψ y) z.2) (PDE.basisVec i) = _
  change (fderiv ℝ ((fun _ : PDE.Vec d => φ z.1) * (ψ : PDE.Vec d → ℝ)) z.2)
      (PDE.basisVec i) = _
  rw [fderiv_mul]
  · simp [PDE.WeakTestFunction.partialDeriv, smul_eq_mul]
  · exact differentiableAt_const _
  · exact (ψ.contDiff.differentiable (by simp)).differentiableAt

end HypoellipticAleksandrov.Parabolic.Dirichlet

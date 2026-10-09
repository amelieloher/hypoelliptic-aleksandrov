module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.SeparatedSpacetimeCompactSupport
public import HypoellipticAleksandrov.Parabolic.Derivatives

/-!
# Sampled time factors

This module packages a fixed spatial sample of a spacetime test as a scalar time test.
-/

@[expose] public section

open Set Topology
open scoped Topology

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

private theorem isClosedEmbedding_fixedSpatial {d : ℕ} (y : PDE.Vec d) :
    IsClosedEmbedding (fun τ : ℝ => ((τ, y) : TimeVelocity d)) := by
  refine IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_id.prodMk continuous_const) (fun x z h => by
      simpa using congrArg Prod.fst h) ?_
  intro s hs
  have himage : (fun τ : ℝ => ((τ, y) : TimeVelocity d)) '' s =
      s ×ˢ ({y} : Set (PDE.Vec d)) := by
    ext z
    simp only [mem_image, mem_prod, mem_singleton_iff]
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      exact ⟨hτ, rfl⟩
    · rintro ⟨hτ, hy⟩
      exact ⟨z.1, hτ, Prod.ext rfl hy.symm⟩
  rw [himage]
  exact hs.prod isClosed_singleton

private theorem hasCompactSupport_fixedSpatial
    {d : ℕ} (y : PDE.Vec d) (f : TimeVelocity d → ℝ) (hf : HasCompactSupport f) :
    HasCompactSupport (fun τ : ℝ => f (τ, y)) := by
  refine HasCompactSupport.of_support_subset_isCompact
    ((isClosedEmbedding_fixedSpatial y).isCompact_preimage hf) ?_
  intro τ hτ
  exact subset_tsupport f hτ

/-- A sampled time slice is an original-time scalar test, with its expected derivative and
support in the compact time projection. -/
theorem exists_sampledTimeFactor
    {d : ℕ} {τ₁ τ₂ : ℝ} {O : Set (PDE.Vec d)} {hO : IsOpen O}
    (φ : TestFunction (originalTimeOpenCylinderOpens τ₁ τ₂ O hO) ℝ (⊤ : ℕ∞))
    (y : PDE.Vec d) :
    ∃ η : OriginalTimeScalarTest τ₁ τ₂,
      (∀ τ, η τ = φ (τ, y)) ∧
      (∀ τ, η.deriv τ = timeDerivative φ (τ, y)) ∧
      tsupport (η : ℝ → ℝ) ⊆
        (spacetimeTestTimeSupportCompact φ : Set ℝ) := by
  let η : OriginalTimeScalarTest τ₁ τ₂ :=
    { toFun := fun τ => φ (τ, y)
      contDiff' := φ.contDiff.comp (contDiff_id.prodMk contDiff_const)
      hasCompactSupport' := hasCompactSupport_fixedSpatial y φ φ.hasCompactSupport
      tsupport_subset' := by
        intro τ hτ
        have hclosed : IsClosed
            ((fun r : ℝ => ((r, y) : TimeVelocity d)) ⁻¹'
              tsupport (φ : TimeVelocity d → ℝ)) :=
          (isClosed_tsupport φ).preimage (continuous_id.prodMk continuous_const)
        have hsupp : Function.support (fun r : ℝ => φ (r, y)) ⊆
            (fun r : ℝ => ((r, y) : TimeVelocity d)) ⁻¹' tsupport φ := by
          intro r hr
          exact subset_tsupport φ hr
        have hz : (τ, y) ∈ tsupport (φ : TimeVelocity d → ℝ) :=
          closure_minimal hsupp hclosed hτ
        exact (φ.tsupport_subset hz).1 }
  refine ⟨η, fun _ => rfl, ?_, ?_⟩
  · intro τ
    rw [OriginalTimeScalarTest.deriv_apply]
    change deriv (fun r : ℝ => φ (r, y)) τ =
      fderiv ℝ (φ : TimeVelocity d → ℝ) (τ, y) (1, 0)
    have hcomp := (φ.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt.comp τ
      (hasFDerivAt_id τ |>.prodMk (hasFDerivAt_const (x := τ) y))
    rw [_root_.deriv]
    have hfderiv : fderiv ℝ (fun r : ℝ => φ (r, y)) τ =
        (fderiv ℝ (φ : TimeVelocity d → ℝ) (τ, y)).comp
          ((ContinuousLinearMap.id ℝ ℝ).prod 0) := by
      simpa only [Function.comp_def, id_eq] using hcomp.fderiv
    rw [hfderiv]
    rfl
  · intro τ hτ
    change τ ∈ Prod.fst '' tsupport (φ : TimeVelocity d → ℝ)
    have hclosed : IsClosed
        ((fun r : ℝ => ((r, y) : TimeVelocity d)) ⁻¹'
          tsupport (φ : TimeVelocity d → ℝ)) :=
      (isClosed_tsupport φ).preimage (continuous_id.prodMk continuous_const)
    have hsupp : Function.support (fun r : ℝ => φ (r, y)) ⊆
        (fun r : ℝ => ((r, y) : TimeVelocity d)) ⁻¹' tsupport φ := by
      intro r hr
      exact subset_tsupport φ hr
    exact ⟨(τ, y), closure_minimal hsupp hclosed hτ, rfl⟩

end HypoellipticAleksandrov.Parabolic.Dirichlet

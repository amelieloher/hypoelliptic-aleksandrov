module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeVariationalAffineUpper
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeVariationalNegation

/-! # Sharp affine envelope for reverse-time variational solutions -/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace Matrix.Norms.Elementwise MatrixOrder

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

local instance instReverseTimeL2VStarModuleEnvelope
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) :
    Module ℝ (ReverseTimeL2VStar hΩ T) :=
  MeasureTheory.Lp.instModule

/-- A reverse-time variational energy solution is bounded in absolute value by
the sharp affine envelope determined by its initial and source bounds. -/
theorem IsReverseTimeVariationalEnergySolution.abs_reverseTimeHilbertRepresentative_le_affine
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hLower : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω →
        lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
    (hcNonpos : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0)
    (Minit MF : ℝ) (hMinit : 0 ≤ Minit) (hMF : 0 ≤ MF)
    (hFbound : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → |F z.1 z.2| ≤ MF)
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (hinitial : ∀ᵐ y ∂PDE.volumeOn Ω, |initial y| ≤ Minit)
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (g : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
      (sub_pos.mpr h₀₁) u g)
    (hu : IsReverseTimeVariationalEnergySolution r₀ r₁ h₀₁ hΩ hΩbounded
      a b c F hFSmooth initial u g hdu) :
    ∀ τ : ℝ, ∀ hτ : τ ∈ Set.Icc 0 (r₁ - r₀),
      ∀ᵐ y ∂PDE.volumeOn Ω,
        |reverseTimeHilbertRepresentative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
            u g hdu ⟨τ, hτ⟩ y| ≤ Minit + τ * MF := by
  have hinitialUpper : ∀ᵐ y ∂PDE.volumeOn Ω, initial y ≤ Minit := by
    filter_upwards [hinitial] with y hy
    exact (le_abs_self (initial y)).trans hy
  have hupper := hu.reverseTimeHilbertRepresentative_le_affine
    r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F haSmooth hbSmooth hcSmooth hFSmooth
      hLower hcNonpos Minit MF hMinit hMF hFbound initial hinitialUpper u g hdu
  let Fneg : ℝ → PDE.Vec d → ℝ := fun r y => -F r y
  let initialNeg : PDE.ScalarLp Ω (2 : ℝ≥0∞) := -initial
  let uneg : ReverseTimeL2V hΩ (r₁ - r₀) := (-1 : ℝ) • u
  let gneg : ReverseTimeL2VStar hΩ (r₁ - r₀) := (-1 : ℝ) • g
  let hduneg : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀)
      (sub_pos.mpr h₀₁) uneg gneg := hdu.smul (-1)
  have hFnegSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => Fneg z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω) :=
    IsSmoothOnNeighborhood.neg hFSmooth
  have hFnegBound : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → |Fneg z.1 z.2| ≤ MF := by
    intro z hz
    simpa only [Fneg, abs_neg] using hFbound z hz
  have hinitialNeg : ∀ᵐ y ∂PDE.volumeOn Ω, initialNeg y ≤ Minit := by
    filter_upwards [hinitial, Lp.coeFn_neg initial] with y hy hneg
    rw [hneg]
    exact (neg_le_abs (initial y)).trans hy
  have huneg : IsReverseTimeVariationalEnergySolution r₀ r₁ h₀₁ hΩ hΩbounded
      a b c Fneg hFnegSmooth initialNeg uneg gneg hduneg := by
    exact hu.neg r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth initial u g hdu
  have hnegUpper := huneg.reverseTimeHilbertRepresentative_le_affine
    r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c Fneg haSmooth hbSmooth hcSmooth
      hFnegSmooth hLower hcNonpos Minit MF hMinit hMF hFnegBound initialNeg hinitialNeg
        uneg gneg hduneg
  intro τ hτ
  have hrep := reverseTimeHilbertRepresentative_neg_eq hΩ (r₁ - r₀)
    (sub_pos.mpr h₀₁) u g hdu
  have hrepτ := congrArg
    (fun Q : C(Set.Icc 0 (r₁ - r₀), PDE.ScalarLp Ω (2 : ℝ≥0∞)) => Q ⟨τ, hτ⟩) hrep
  have hrepτ' :
      reverseTimeHilbertRepresentative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
          uneg gneg hduneg ⟨τ, hτ⟩ =
        -reverseTimeHilbertRepresentative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
          u g hdu ⟨τ, hτ⟩ := by
    simpa only [uneg, gneg, hduneg, ContinuousMap.neg_apply] using hrepτ
  filter_upwards [hupper τ hτ, hnegUpper τ hτ, Lp.ext_iff.mp hrepτ',
    Lp.coeFn_neg
      (reverseTimeHilbertRepresentative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
        u g hdu ⟨τ, hτ⟩)] with y hyUpper hyNeg hrepY hcoeNeg
  have hyLower : -(Minit + τ * MF) ≤
      reverseTimeHilbertRepresentative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
        u g hdu ⟨τ, hτ⟩ y := by
    have hrepScalar :
        reverseTimeHilbertRepresentative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
            uneg gneg hduneg ⟨τ, hτ⟩ y =
          -reverseTimeHilbertRepresentative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
            u g hdu ⟨τ, hτ⟩ y := by
      calc
        _ = (-reverseTimeHilbertRepresentative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
              u g hdu ⟨τ, hτ⟩) y := hrepY
        _ = _ := by simp only [hcoeNeg, Pi.neg_apply]
    rw [hrepScalar] at hyNeg
    exact neg_le.mp hyNeg
  exact abs_le.mpr ⟨hyLower, hyUpper⟩

end HypoellipticAleksandrov.Parabolic.Dirichlet

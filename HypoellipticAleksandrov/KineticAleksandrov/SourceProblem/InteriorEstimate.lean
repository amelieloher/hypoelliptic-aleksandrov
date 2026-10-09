module

public import HypoellipticAleksandrov.KineticAleksandrov.SourceProblem.InteriorReduction
public import HypoellipticAleksandrov.Parabolic.ABP

/-! # The scalar parabolic Aleksandrov estimate on the Krylov cylinders -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LsuFree
open Parabolic
open MeasureTheory Set
open scoped MatrixOrder Matrix.Norms.Elementwise

/-- Krylov's scalar parabolic Aleksandrov estimate, uniformly over location and height. -/
theorem parabolic_aleksandrov_direct
    (N : ℕ) (hN : 1 ≤ N) (lam Lam : ℝ) (hlam : 0 < lam) (_hLam : lam ≤ Lam) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (t₀ : ℝ) (v₀ : PDE.Vec N) (h : ℝ), 0 < h → h ≤ 1 →
      ∀ (a : TimeVelocity N → PDE.Mat N) (f u : TimeVelocity N → ℝ),
        ContinuousOn a (krylovClosedCylinder t₀ h v₀) →
        (∀ z ∈ krylovClosedCylinder t₀ h v₀, (a z).IsSymm) →
        (∀ z ∈ krylovClosedCylinder t₀ h v₀,
          lam • (1 : PDE.Mat N) ≤ a z ∧ a z ≤ Lam • (1 : PDE.Mat N)) →
        MemLp f (parabolicExponent N) (volume.restrict (krylovCylinder t₀ h v₀)) →
        IsScalarC12On u (krylovCylinder t₀ h v₀) →
        ContinuousOn u (krylovClosedCylinder t₀ h v₀) →
        (∀ᵐ z ∂volume.restrict (krylovCylinder t₀ h v₀),
          scalarTimeDerivative u z - matrixContraction (a z) (scalarSpatialHessian u z)
            ≤ f z) →
        (∀ z ∈ krylovParabolicBoundary t₀ h v₀, u z ≤ 0) →
        ∀ z ∈ krylovCylinder t₀ h v₀,
          u z ≤ C * parabolicLpNormOn N f (krylovCylinder t₀ h v₀) := by
  obtain ⟨C, hC, hABP⟩ := parabolic_abp_unit_of_lower_ellipticity N hN lam hlam
  refine ⟨C, hC.le, ?_⟩
  intro t₀ v₀ h hh hh1 a f u ha _hsym hell hf hu huc hsub hb z hz
  let Z : TimeVelocity N := (z.1 - (t₀ - h), z.2 - v₀)
  have hZ : Z ∈ closedParabolicCylinder h (0 : PDE.Vec N) := by
    refine ⟨⟨by dsimp [Z]; linarith [hz.1.1],
      by dsimp [Z]; linarith [hz.1.2]⟩, ?_⟩
    change PDE.euclideanSqDist (z.2 - v₀) 0 ≤ 1 ^ 2
    have hv : PDE.euclideanSqDist z.2 v₀ ≤ 1 ^ 2 :=
      (show PDE.euclideanSqDist z.2 v₀ < 1 ^ 2 from hz.2).le
    simpa only [PDE.euclideanSqDist, Pi.sub_apply, sub_zero] using hv
  have hmap : KrylovEstimate.innerMap t₀ h v₀ 1 Z = z := by
    apply Prod.ext
    · simp only [KrylovEstimate.innerMap, parabolicAffine, Z, one_pow,
        sub_self, zero_mul, zero_div, add_zero, one_mul]
      ring
    · simp only [KrylovEstimate.innerMap, parabolicAffine, Z, one_smul]
      exact add_sub_cancel _ _
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε / (C + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  obtain ⟨A, F, w, hA, hF, hw, hlo, hsw, hbw, hclose, hnorm⟩ :=
    exists_smooth_subsolution_close_direct N hN lam hlam t₀ h v₀ hh a f u
      ha (fun y hy => (hell y hy).1) hf hu huc hsub hb hδ
  have hestimate := hABP hh hh1 0 A F w hA hF hw hlo hsw hbw Z hZ
  have hvalue := hclose Z hZ
  rw [hmap] at hvalue
  have hupper := (neg_le_abs (w Z - u z)).trans hvalue
  have hsource := mul_le_mul_of_nonneg_left hnorm hC.le
  have herror : δ * (C + 1) = ε := div_mul_cancel₀ ε (by linarith)
  nlinarith

end HypoellipticAleksandrov.KineticAleksandrov.LsuFree

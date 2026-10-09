module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2CoordinatesTransport
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2CutoffScaling

/-! # Exact velocity-Hessian prefactor in homogeneous coordinates -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- The homogeneous cutoff ansatz has the literal source velocity-Hessian scaling. -/
theorem homogeneousAnsatz_velocity_hessian {d : ℕ} (alpha C₀ sigma R : ℝ)
    (hsigma : 0 < sigma) (hR : 0 < R) (x v w u : PDE.Vec d) (hx : x ≠ 0) :
    fderiv ℝ (fun z => fderiv ℝ
      (fun a => homogeneousAnsatz alpha (cutoffProfile alpha C₀ sigma R) x a) z w) v u =
      Real.rpow (PDE.vecEuclideanNorm x) ((alpha - 2) / 3) *
        fderiv ℝ (fun z => fderiv ℝ
          (fun a => cutoffProfile alpha C₀ sigma R a (positionDirection x)) z w)
          (normalizedVelocity x v) u := by
  have hr := PDE.vecEuclideanNorm_pos_iff.mpr hx
  have hF : ContDiff ℝ (⊤ : ℕ∞)
      (fun a => cutoffProfile alpha C₀ sigma R a (positionDirection x)) :=
    (contDiff_cutoffProfile alpha C₀ sigma R hsigma hR).comp
      (contDiff_id.prodMk contDiff_const)
  have heq : (fun a => homogeneousAnsatz alpha (cutoffProfile alpha C₀ sigma R) x a) =
      (fun a => Real.rpow (PDE.vecEuclideanNorm x) (alpha / 3) *
        cutoffProfile alpha C₀ sigma R
          (Real.rpow (PDE.vecEuclideanNorm x) (-(1 / 3 : ℝ)) • a) (positionDirection x)) := by
    funext a
    rfl
  have hp : Real.rpow (PDE.vecEuclideanNorm x) (alpha / 3) *
      Real.rpow (PDE.vecEuclideanNorm x) (-(1 / 3 : ℝ)) ^ 2 =
      Real.rpow (PDE.vecEuclideanNorm x) ((alpha - 2) / 3) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_mul_natCast hr.le, ← Real.rpow_add hr]
    congr 1
    norm_num
    ring
  rw [heq]
  have hh := hessian_scaledFunction _ hF
    (Real.rpow (PDE.vecEuclideanNorm x) (alpha / 3))
    (Real.rpow (PDE.vecEuclideanNorm x) (-(1 / 3 : ℝ))) v w u
  rw [hp] at hh
  exact hh

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

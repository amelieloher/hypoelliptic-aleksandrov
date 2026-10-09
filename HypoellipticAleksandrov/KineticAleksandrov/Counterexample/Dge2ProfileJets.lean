module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2CoordinatesHessian
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2ProfileGradient
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # Local full-product and slice jet identities away from the profile origin -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- The native full-product velocity derivative agrees with its literal slice derivative. -/
theorem fderiv_velocity_slice {d : ℕ} (H : XV d → ℝ) (x v w : PDE.Vec d)
    (hH : DifferentiableAt ℝ H (x, v)) :
    fderiv ℝ (fun z => H (x, z)) v w = fderiv ℝ H (x, v) (0, w) := by
  have hi : HasFDerivAt (fun z : PDE.Vec d => (x, z))
      ((0 : PDE.Vec d →L[ℝ] PDE.Vec d).prod (ContinuousLinearMap.id ℝ (PDE.Vec d))) v := by
    convert (hasFDerivAt_const (𝕜 := ℝ) x v).prodMk (hasFDerivAt_id (𝕜 := ℝ) v) using 1
    funext z
    rfl
  have hh := hH.hasFDerivAt.comp v hi
  have hh' : HasFDerivAt (fun z => H (x, z))
      ((fderiv ℝ H (x, v)).comp
        ((0 : PDE.Vec d →L[ℝ] PDE.Vec d).prod (ContinuousLinearMap.id ℝ (PDE.Vec d)))) v := by
    convert hh using 1
    funext z
    rfl
  rw [hh'.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    zero_apply, ContinuousLinearMap.id_apply]

/-- Scalar evaluation of the full first derivative gives its literal second derivative. -/
theorem full_secondDirectional_eq {d : ℕ} (H : XV d → ℝ) (q u w : XV d)
    (hH : ContDiffAt ℝ (⊤ : ℕ∞) H q) :
    fderiv ℝ (fun z => fderiv ℝ H z w) q u = fderiv ℝ (fderiv ℝ H) q u w := by
  have hd := (hH.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiableAt (by simp)
  rw [fderiv_clm_apply hd (differentiableAt_const w)]
  simp

/-- A smooth full-product velocity Hessian agrees with the literal velocity slice Hessian. -/
theorem full_velocity_hessian_eq_slice {d : ℕ} (H : XV d → ℝ) (x v w u : PDE.Vec d)
    (hH : ContDiffAt ℝ (⊤ : ℕ∞) H (x, v)) :
    fderiv ℝ (fun z => fderiv ℝ H z (0, w)) (x, v) (0, u) =
      fderiv ℝ (fun z => fderiv ℝ (fun a => H (x, a)) z w) v u := by
  have hi : HasFDerivAt (fun z : PDE.Vec d => (x, z))
      ((0 : PDE.Vec d →L[ℝ] PDE.Vec d).prod (ContinuousLinearMap.id ℝ (PDE.Vec d))) v := by
    convert (hasFDerivAt_const (𝕜 := ℝ) x v).prodMk (hasFDerivAt_id (𝕜 := ℝ) v) using 1
    funext z
    rfl
  have hd := ((hH.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply
    (contDiffAt_const (c := ((0, w) : XV d)))).differentiableAt (by simp)
  have hh := hd.hasFDerivAt.comp v hi
  have hevent : (fun z => fderiv ℝ (fun a => H (x, a)) z w) =ᶠ[nhds v]
      (fun z => fderiv ℝ H (x, z) (0, w)) := by
    have hc : Continuous (fun z : PDE.Vec d => (x, z)) := by fun_prop
    have hreg := hc.continuousAt.eventually ((hH.of_le (show (1 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by
      simp)).eventually (by simp))
    filter_upwards [hreg] with z hz
    exact fderiv_velocity_slice H x z w (hz.differentiableAt (by norm_num))
  rw [hevent.fderiv_eq (𝕜 := ℝ)]
  have hh' : HasFDerivAt (fun z => fderiv ℝ H (x, z) (0, w))
      ((fderiv ℝ (fun z => fderiv ℝ H z (0, w)) (x, v)).comp
        ((0 : PDE.Vec d →L[ℝ] PDE.Vec d).prod (ContinuousLinearMap.id ℝ (PDE.Vec d)))) v := by
    convert hh using 1
    funext z
    rfl
  rw [hh'.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    zero_apply, ContinuousLinearMap.id_apply]

/-- The full-product position derivative agrees with its literal position slice. -/
theorem fderiv_position_slice {d : ℕ} (H : XV d → ℝ) (x v w : PDE.Vec d)
    (hH : DifferentiableAt ℝ H (x, v)) :
    fderiv ℝ (fun z => H (z, v)) x w = fderiv ℝ H (x, v) (w, 0) := by
  have hi : HasFDerivAt (fun z : PDE.Vec d => (z, v))
      ((ContinuousLinearMap.id ℝ (PDE.Vec d)).prod (0 : PDE.Vec d →L[ℝ] PDE.Vec d)) x := by
    convert (hasFDerivAt_id (𝕜 := ℝ) x).prodMk (hasFDerivAt_const (𝕜 := ℝ) v x) using 1
    funext z
    rfl
  have hh := hH.hasFDerivAt.comp x hi
  have hh' : HasFDerivAt (fun z => H (z, v))
      ((fderiv ℝ H (x, v)).comp
        ((ContinuousLinearMap.id ℝ (PDE.Vec d)).prod
          (0 : PDE.Vec d →L[ℝ] PDE.Vec d))) x := by
    convert hh using 1
    funext z
    rfl
  rw [hh'.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    zero_apply, ContinuousLinearMap.id_apply]

/-- Native position selectors conditions to the full directional transport derivative. -/
theorem transport_eq_direction {d : ℕ} (H : XV d → ℝ) (q : XV d) :
    PDE.vecDot q.2 (dx H q) = fderiv ℝ H q (q.2, 0) := by
  have heq : (q.2, (0 : PDE.Vec d)) =
      ∑ i : Fin d, q.2 i • ((Pi.single i 1, 0) : XV d) := by
    apply Prod.ext
    · ext k
      simp [Prod.fst_sum, Pi.single_apply]
    · simp [Prod.snd_sum]
  rw [heq, map_sum]
  simp only [map_smul, smul_eq_mul, dx, PDE.vecDot]

/-- The local full-product Hessian matrix is Hermitian at every smooth point. -/
theorem dvv_isHermitian {d : ℕ} (H : XV d → ℝ) (q : XV d)
    (hH : ContDiffAt ℝ (⊤ : ℕ∞) H q) : (dvv H q).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  ext i k
  change fderiv ℝ (fun z => fderiv ℝ H z (0, Pi.single i 1)) q (0, Pi.single k 1) =
    fderiv ℝ (fun z => fderiv ℝ H z (0, Pi.single k 1)) q (0, Pi.single i 1)
  rw [full_secondDirectional_eq H q _ _ hH, full_secondDirectional_eq H q _ _ hH]
  exact (hH.isSymmSndFDerivAt (by simp)).eq _ _

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2SignsCutoff
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2SpectralSigns
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # The actual cutoff Hessian matrix and transport scalar -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- Scalar evaluation commutes with the second derivative of a smooth function. -/
theorem secondDirectional_eq {d : ℕ} (F : PDE.Vec d → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (y w u : PDE.Vec d) :
    fderiv ℝ (fun z => fderiv ℝ F z w) y u = fderiv ℝ (fderiv ℝ F) y u w := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) y :=
    (hF.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp) y
  rw [fderiv_clm_apply hd (differentiableAt_const w)]
  simp

/-- The literal symmetric matrix representing the cutoff velocity Hessian. -/
def cutoffMatrix {d : ℕ} (alpha C₀ sigma R : ℝ) (y e : PDE.Vec d) : PDE.Mat d :=
  fun i k => fderiv ℝ (fderiv ℝ (fun z => cutoffProfile alpha C₀ sigma R z e)) y
    (Pi.single i 1) (Pi.single k 1)

/-- A bilinear continuous derivative is the quadratic form of its native coordinate matrix. -/
theorem dotProduct_matrix_of_bilinear {d : ℕ}
    (B : PDE.Vec d →L[ℝ] PDE.Vec d →L[ℝ] ℝ) (w : PDE.Vec d) :
    dotProduct w (Matrix.mulVec (fun i k => B (Pi.single i 1) (Pi.single k 1)) w) = B w w := by
  have heq : w = ∑ i : Fin d, w i • Pi.single i (1 : ℝ) := by
    ext k
    simp [Pi.single_apply]
  conv_rhs => rw [heq]
  simp only [map_sum, map_smul, smul_eq_mul]
  simp only [dotProduct, Matrix.mulVec, sum_apply, smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The cutoff matrix has exactly the previously differentiated quadratic form. -/
theorem cutoffMatrix_quadratic {d : ℕ} (alpha C₀ sigma R : ℝ)
    (hsigma : 0 < sigma) (hR : 0 < R) (y e w : PDE.Vec d) :
    dotProduct w ((cutoffMatrix alpha C₀ sigma R y e).mulVec w) =
      cutoffHessian alpha C₀ sigma R y e w := by
  have hF : ContDiff ℝ (⊤ : ℕ∞) (fun a => cutoffProfile alpha C₀ sigma R a e) :=
    (contDiff_cutoffProfile alpha C₀ sigma R hsigma hR).comp
    (contDiff_id.prodMk (contDiff_const (c := e)))
  rw [cutoffHessian, secondDirectional_eq _ hF]
  exact dotProduct_matrix_of_bilinear _ w

/-- The actual cutoff matrix is Hermitian by symmetry of the second derivative. -/
theorem cutoffMatrix_isHermitian {d : ℕ} (alpha C₀ sigma R : ℝ)
    (hsigma : 0 < sigma) (hR : 0 < R) (y e : PDE.Vec d) :
    (cutoffMatrix alpha C₀ sigma R y e).IsHermitian := by
  have hF : ContDiff ℝ (⊤ : ℕ∞) (fun a => cutoffProfile alpha C₀ sigma R a e) :=
    (contDiff_cutoffProfile alpha C₀ sigma R hsigma hR).comp
    (contDiff_id.prodMk (contDiff_const (c := e)))
  rw [Matrix.isHermitian_iff_isSymm]
  ext i k
  exact (hF.contDiffAt.isSymmSndFDerivAt (by simp)).eq _ _

/-- The actual cutoff Hessian matrix is continuous jointly in both vector variables. -/
theorem continuous_cutoffMatrix {d : ℕ} (alpha C₀ sigma R : ℝ)
    (hsigma : 0 < sigma) (hR : 0 < R) :
    Continuous (fun q : PDE.Vec d × PDE.Vec d => cutoffMatrix alpha C₀ sigma R q.1 q.2) := by
  have hF := contDiff_cutoffProfile (d := d) alpha C₀ sigma R hsigma hR
  have hf : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : PDE.Vec d × PDE.Vec d =>
        fderiv ℝ (fun z => cutoffProfile alpha C₀ sigma R z q.2) q.1) := by
    have hc : ContDiff ℝ (⊤ : ℕ∞)
        (fun q : (PDE.Vec d × PDE.Vec d) × PDE.Vec d => (q.2, q.1.2)) := by fun_prop
    exact (hF.comp hc).fderiv contDiff_fst (by simp)
  have hh : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : PDE.Vec d × PDE.Vec d =>
        fderiv ℝ (fderiv ℝ (fun z => cutoffProfile alpha C₀ sigma R z q.2)) q.1) := by
    have hc : ContDiff ℝ (⊤ : ℕ∞)
        (fun q : (PDE.Vec d × PDE.Vec d) × PDE.Vec d => (q.2, q.1.2)) := by fun_prop
    exact (hf.comp hc).fderiv contDiff_fst (by simp)
  apply continuous_pi
  intro i
  apply continuous_pi
  intro k
  exact ((hh.clm_apply contDiff_const).clm_apply contDiff_const).continuous

/-- The actual cutoff transport scalar is continuous jointly. -/
theorem continuous_cutoffTransport {d : ℕ} (alpha C₀ sigma R : ℝ)
    (hsigma : 0 < sigma) (hR : 0 < R) :
    Continuous (fun q : PDE.Vec d × PDE.Vec d =>
      ansatzTransport alpha (cutoffProfile alpha C₀ sigma R) q.1 q.2) := by
  have hF := contDiff_cutoffProfile (d := d) alpha C₀ sigma R hsigma hR
  have hv : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : PDE.Vec d × PDE.Vec d =>
        fderiv ℝ (fun z => cutoffProfile alpha C₀ sigma R z q.2) q.1) := by
    have hc : ContDiff ℝ (⊤ : ℕ∞)
        (fun q : (PDE.Vec d × PDE.Vec d) × PDE.Vec d => (q.2, q.1.2)) := by fun_prop
    exact (hF.comp hc).fderiv contDiff_fst (by simp)
  have he : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : PDE.Vec d × PDE.Vec d =>
        fderiv ℝ (fun z => cutoffProfile alpha C₀ sigma R q.1 z) q.2) := by
    have hc : ContDiff ℝ (⊤ : ℕ∞)
        (fun q : (PDE.Vec d × PDE.Vec d) × PDE.Vec d => (q.1.1, q.2)) := by fun_prop
    exact (hF.comp hc).fderiv contDiff_snd (by simp)
  have ht : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : PDE.Vec d × PDE.Vec d => q.1 - PDE.vecDot q.1 q.2 • q.2) := by
    unfold PDE.vecDot
    fun_prop
  have hvapp := (hv.clm_apply contDiff_fst).continuous
  have heapp := (he.clm_apply ht).continuous
  have hdot : Continuous (fun q : PDE.Vec d × PDE.Vec d => PDE.vecDot q.1 q.2) := by
    unfold PDE.vecDot
    fun_prop
  exact (hdot.mul ((continuous_const.mul hF.continuous).sub
    (continuous_const.mul hvapp))).add heapp

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

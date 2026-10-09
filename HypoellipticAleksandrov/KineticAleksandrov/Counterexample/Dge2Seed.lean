module

public import PDEFoundation.Ambient.EuclideanNorm
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity

/-!
# The regularized translated radial seed in Appendix C

All squared lengths in this module are Euclidean squared lengths on the native carrier.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open scoped BigOperators

/-- The positive quantity inside the seed's real power. -/
def seedBase {d : ℕ} (sigma : ℝ) (y e : PDE.Vec d) : ℝ :=
  sigma ^ 2 + PDE.vecNormSq (y - e)

/-- The literal seed of Appendix C. -/
def seed {d : ℕ} (alpha C₀ sigma : ℝ) (y e : PDE.Vec d) : ℝ :=
  C₀ + Real.rpow (seedBase sigma y e) (alpha / 2)

/-- The seed base is strictly positive when the regularization parameter is positive. -/
theorem seedBase_pos {d : ℕ} (sigma : ℝ) (hsigma : 0 < sigma)
    (y e : PDE.Vec d) : 0 < seedBase sigma y e := by
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos hsigma) (PDE.vecNormSq_nonneg _)

/-- The literal seed is positive for a nonnegative additive constant. -/
theorem seed_pos {d : ℕ} (alpha C₀ sigma : ℝ) (hC₀ : 0 ≤ C₀)
    (hsigma : 0 < sigma) (y e : PDE.Vec d) : 0 < seed alpha C₀ sigma y e := by
  exact add_pos_of_nonneg_of_pos hC₀ (Real.rpow_pos_of_pos
    (seedBase_pos sigma hsigma y e) _)

/-- The regularized seed is smooth jointly in its two native vector variables. -/
theorem contDiff_seed {d : ℕ} (alpha C₀ sigma : ℝ) (hsigma : 0 < sigma) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun q : PDE.Vec d × PDE.Vec d => seed alpha C₀ sigma q.1 q.2) := by
  have hb : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : PDE.Vec d × PDE.Vec d => seedBase sigma q.1 q.2) := by
    unfold seedBase PDE.vecNormSq PDE.vecDot
    fun_prop
  exact contDiff_const.add (hb.rpow_const_of_ne fun q =>
    (seedBase_pos sigma hsigma q.1 q.2).ne')

/-- The tangential Hessian eigenvalue of the seed. -/
def seedTangentialEigenvalue {d : ℕ} (alpha sigma : ℝ) (y e : PDE.Vec d) : ℝ :=
  alpha * Real.rpow (seedBase sigma y e) (alpha / 2 - 1)

/-- The radial Hessian eigenvalue of the seed. -/
def seedRadialEigenvalue {d : ℕ} (alpha sigma : ℝ) (y e : PDE.Vec d) : ℝ :=
  alpha * Real.rpow (seedBase sigma y e) (alpha / 2 - 2) *
    (sigma ^ 2 - (1 - alpha) * PDE.vecNormSq (y - e))

/-- The tangential seed eigenvalue is strictly positive. -/
theorem seedTangentialEigenvalue_pos {d : ℕ} (alpha sigma : ℝ)
    (ha : 0 < alpha) (hsigma : 0 < sigma) (y e : PDE.Vec d) :
    0 < seedTangentialEigenvalue alpha sigma y e := by
  exact mul_pos ha (Real.rpow_pos_of_pos (seedBase_pos sigma hsigma y e) _)

/-- The radial seed eigenvalue is negative precisely past the source threshold. -/
theorem seedRadialEigenvalue_neg_iff {d : ℕ} (alpha sigma : ℝ)
    (ha : 0 < alpha) (hsigma : 0 < sigma) (y e : PDE.Vec d) :
    seedRadialEigenvalue alpha sigma y e < 0 ↔
      sigma ^ 2 < (1 - alpha) * PDE.vecNormSq (y - e) := by
  unfold seedRadialEigenvalue
  have hp := mul_pos ha
    (Real.rpow_pos_of_pos (seedBase_pos sigma hsigma y e) (alpha / 2 - 2))
  simp only [Real.rpow_eq_pow]
  rw [mul_neg_iff]
  simp only [hp, hp.not_gt, true_and, false_and, or_false, sub_neg]

/-- The Euclidean dot product with a fixed vector as a continuous linear map. -/
def seedDotLinear {d : ℕ} (z : PDE.Vec d) : PDE.Vec d →L[ℝ] ℝ :=
  ∑ i : Fin d, z i • ContinuousLinearMap.proj i

/-- Evaluation of the dot-product continuous linear map. -/
theorem seedDotLinear_apply {d : ℕ} (z w : PDE.Vec d) :
    seedDotLinear z w = PDE.vecDot z w := by
  simp [seedDotLinear, PDE.vecDot]

/-- The exact Frechet derivative of the seed base. -/
theorem hasFDerivAt_seedBase {d : ℕ} (sigma : ℝ) (y e : PDE.Vec d) :
    HasFDerivAt (fun z => seedBase sigma z e) (2 • seedDotLinear (y - e)) y := by
  have hi (i : Fin d) : HasFDerivAt (fun z : PDE.Vec d => (z i - e i) ^ 2)
      ((2 * (y i - e i)) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i) y := by
    convert ((hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin d => ℝ) i y).sub_const
      (e i)).pow 2 using 1
    simp
  have hh := (HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i)).const_add
    (sigma ^ 2)
  convert hh using 1
  · simp [seedBase, PDE.vecNormSq_eq_sum_sq]
  · ext w
    simp [seedDotLinear, Finset.mul_sum, mul_assoc]

/-- The exact first derivative of the seed with respect to its velocity variable. -/
theorem hasFDerivAt_seed {d : ℕ} (alpha C₀ sigma : ℝ) (hsigma : 0 < sigma)
    (y e : PDE.Vec d) :
    HasFDerivAt (fun z => seed alpha C₀ sigma z e)
      ((alpha * Real.rpow (seedBase sigma y e) (alpha / 2 - 1)) •
        seedDotLinear (y - e)) y := by
  have hh := ((hasFDerivAt_seedBase sigma y e).rpow_const
    (p := alpha / 2) (Or.inl (seedBase_pos sigma hsigma y e).ne')).const_add C₀
  convert hh using 1
  · rfl
  · ext w
    simp only [smul_apply, smul_eq_mul, Real.rpow_eq_pow]
    ring

/-- The first seed derivative applied to a native vector. -/
theorem fderiv_seed_apply {d : ℕ} (alpha C₀ sigma : ℝ) (hsigma : 0 < sigma)
    (y e w : PDE.Vec d) :
    fderiv ℝ (fun z => seed alpha C₀ sigma z e) y w =
      alpha * Real.rpow (seedBase sigma y e) (alpha / 2 - 1) *
        PDE.vecDot (y - e) w := by
  rw [(hasFDerivAt_seed alpha C₀ sigma hsigma y e).fderiv]
  simp only [smul_apply, smul_eq_mul, seedDotLinear_apply]

/-- The rank-one expression for the seed's velocity Hessian. -/
def seedHessianForm {d : ℕ} (alpha sigma : ℝ) (y e w u : PDE.Vec d) : ℝ :=
  alpha * Real.rpow (seedBase sigma y e) (alpha / 2 - 1) * PDE.vecDot w u +
    alpha * (alpha - 2) * Real.rpow (seedBase sigma y e) (alpha / 2 - 2) *
      PDE.vecDot (y - e) w * PDE.vecDot (y - e) u

/-- The differentiated seed first derivative, with an explicit linear-map value. -/
theorem hasFDerivAt_seed_first {d : ℕ} (alpha C₀ sigma : ℝ) (hsigma : 0 < sigma)
    (y e w : PDE.Vec d) :
    HasFDerivAt (fun z => fderiv ℝ (fun a => seed alpha C₀ sigma a e) z w)
      ((PDE.vecDot (y - e) w *
          (alpha * (alpha - 2) * Real.rpow (seedBase sigma y e) (alpha / 2 - 2))) •
        seedDotLinear (y - e) +
        (alpha * Real.rpow (seedBase sigma y e) (alpha / 2 - 1)) • seedDotLinear w)
      y := by
  have hp := ((hasFDerivAt_seedBase sigma y e).rpow_const (p := alpha / 2 - 1)
    (Or.inl (seedBase_pos sigma hsigma y e).ne')).const_mul alpha
  have hd : HasFDerivAt (fun z => PDE.vecDot (z - e) w) (seedDotLinear w) y := by
    have hh := ((seedDotLinear w).hasFDerivAt (x := y)).sub_const (PDE.vecDot w e)
    convert hh using 1
    ext z
    simp only [seedDotLinear_apply, PDE.vecDot, Pi.sub_apply, mul_sub,
      Finset.sum_sub_distrib, mul_comm]
  have hh := hp.mul hd
  have hexp : alpha / 2 - 1 - 1 = alpha / 2 - 2 := by ring
  convert hh using 1
  · ext z
    exact fderiv_seed_apply alpha C₀ sigma hsigma z e w
  · ext u
    simp only [smul_apply, smul_eq_mul, add_apply,
      Real.rpow_eq_pow, hexp]
    ring

/-- The exact seed Hessian, evaluated on two arbitrary native directions. -/
theorem seed_hessian {d : ℕ} (alpha C₀ sigma : ℝ) (hsigma : 0 < sigma)
    (y e w u : PDE.Vec d) :
    fderiv ℝ (fun z => fderiv ℝ (fun a => seed alpha C₀ sigma a e) z w) y u =
      seedHessianForm alpha sigma y e w u := by
  rw [(hasFDerivAt_seed_first alpha C₀ sigma hsigma y e w).fderiv]
  simp only [seedHessianForm, smul_apply, smul_eq_mul, add_apply,
    seedDotLinear_apply]
  ring

/-- The seed Hessian has its stated tangential eigenvalue on orthogonal directions. -/
theorem seed_hessian_tangent {d : ℕ} (alpha C₀ sigma : ℝ) (hsigma : 0 < sigma)
    (y e w u : PDE.Vec d) (hw : PDE.vecDot (y - e) w = 0) :
    fderiv ℝ (fun z => fderiv ℝ (fun a => seed alpha C₀ sigma a e) z w) y u =
      seedTangentialEigenvalue alpha sigma y e * PDE.vecDot w u := by
  rw [seed_hessian alpha C₀ sigma hsigma]
  simp [seedHessianForm, seedTangentialEigenvalue, hw]

/-- The seed Hessian has its stated radial eigenvalue on the translated radial vector. -/
theorem seed_hessian_radial {d : ℕ} (alpha C₀ sigma : ℝ) (hsigma : 0 < sigma)
    (y e u : PDE.Vec d) :
    fderiv ℝ (fun z => fderiv ℝ (fun a => seed alpha C₀ sigma a e) z (y - e)) y u =
      seedRadialEigenvalue alpha sigma y e * PDE.vecDot (y - e) u := by
  rw [seed_hessian alpha C₀ sigma hsigma]
  have hpower : Real.rpow (seedBase sigma y e) (alpha / 2 - 1) =
      Real.rpow (seedBase sigma y e) (alpha / 2 - 2) * seedBase sigma y e := by
    simp only [Real.rpow_eq_pow]
    calc
      seedBase sigma y e ^ (alpha / 2 - 1) =
          seedBase sigma y e ^ ((alpha / 2 - 2) + 1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add (seedBase_pos sigma hsigma y e), Real.rpow_one]
  simp only [seedHessianForm, seedRadialEigenvalue, hpower, PDE.vecNormSq]
  unfold seedBase PDE.vecNormSq
  ring

/-- The ambient sphere-direction derivative of the seed is the negative velocity jet. -/
theorem fderiv_seed_sphere_apply {d : ℕ} (alpha C₀ sigma : ℝ) (hsigma : 0 < sigma)
    (y e w : PDE.Vec d) :
    fderiv ℝ (fun a => seed alpha C₀ sigma y a) e w =
      -(alpha * Real.rpow (seedBase sigma y e) (alpha / 2 - 1) *
        PDE.vecDot (y - e) w) := by
  have hsym (a b : PDE.Vec d) : seed alpha C₀ sigma a b = seed alpha C₀ sigma b a := by
    unfold seed seedBase
    rw [show a - b = -(b - a) by abel, PDE.vecNormSq_neg]
  have hf : (fun a => seed alpha C₀ sigma y a) =
      (fun a => seed alpha C₀ sigma a y) := by
    funext a
    exact hsym y a
  rw [hf, fderiv_seed_apply alpha C₀ sigma hsigma]
  have hdot : PDE.vecDot (e - y) w = -PDE.vecDot (y - e) w := by
    simp only [PDE.vecDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [hdot]
  have hbase : seedBase sigma e y = seedBase sigma y e := by
    unfold seedBase
    rw [show e - y = -(y - e) by abel, PDE.vecNormSq_neg]
  rw [hbase]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

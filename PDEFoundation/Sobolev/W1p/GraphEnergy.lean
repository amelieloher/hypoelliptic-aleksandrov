module

public import PDEFoundation.Sobolev.H1.Graph
public import PDEFoundation.Sobolev.W1p.RepresentativeGraph
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Domain energies controlled by the `H¹` graph distance

The scalar value error and the Euclidean magnitude of the gradient error each
have squared integral at most the squared distance in the complete `H¹`
graph.  Both component comparisons have constant one.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory

noncomputable section

/-- The squared integral of a representative of a scalar `L²` class is its
squared `L²` norm. -/
theorem integral_sq_eq_sq_norm_of_ae_eq
    {d : ℕ} {U : Set (Vec d)} (F : ScalarLp U (2 : ℝ≥0∞))
    (f : Vec d → ℝ)
    (hF : ⇑F =ᵐ[volumeOn U] f) :
    (∫ x, f x ^ 2 ∂(volumeOn U)) = ‖F‖ ^ 2 := by
  calc
    (∫ x, f x ^ 2 ∂(volumeOn U)) =
        ∫ x, F x ^ 2 ∂(volumeOn U) := by
      apply integral_congr_ae
      filter_upwards [hF] with x hx
      rw [hx]
    _ = RCLike.re (inner ℝ F F) := by
      rw [L2.inner_def, ← integral_re (L2.integrable_inner F F)]
      apply integral_congr_ae
      filter_upwards with x
      simp
    _ = ‖F‖ ^ 2 := inner_self_eq_norm_sq F

/-- The squared integral of the norm of a representative of a Hilbert-vector
`L²` class is its squared `L²` norm. -/
theorem integral_norm_sq_eq_sq_norm_of_ae_eq_hilbert
    {d : ℕ} {U : Set (Vec d)}
    (F : HilbertVectorLp U (2 : ℝ≥0∞))
    (f : Vec d → ℝ)
    (hF : (fun x => ‖F x‖) =ᵐ[volumeOn U] f) :
    (∫ x, f x ^ 2 ∂(volumeOn U)) = ‖F‖ ^ 2 := by
  calc
    (∫ x, f x ^ 2 ∂(volumeOn U)) =
        ∫ x, ‖F x‖ ^ 2 ∂(volumeOn U) := by
      apply integral_congr_ae
      filter_upwards [hF] with x hx
      rw [hx]
    _ = RCLike.re (inner ℝ F F) := by
      rw [L2.inner_def, ← integral_re (L2.integrable_inner F F)]
      apply integral_congr_ae
      filter_upwards with x
      simp
    _ = ‖F‖ ^ 2 := inner_self_eq_norm_sq F

/-- The domain `L²` value error is bounded by the squared `H¹` graph distance,
with constant one. -/
theorem integral_sq_sub_toFun_le_dist_sq
    {d : ℕ} {U : Set (Vec d)}
    (v w : W1pFunction U (2 : ℝ≥0∞)) :
    (∫ x, (v.toFun x - w.toFun x) ^ 2 ∂(volumeOn U)) ≤
      dist v.toW1pGraph w.toW1pGraph ^ 2 := by
  let F : ScalarLp U (2 : ℝ≥0∞) :=
    (v.toW1pGraph - w.toW1pGraph).1.1
  have hF : ⇑F =ᵐ[volumeOn U]
      fun x => v.toFun x - w.toFun x := by
    dsimp only [F]
    change ⇑(v.toW1pGraph.1.1 - w.toW1pGraph.1.1) =ᵐ[volumeOn U]
      fun x => v.toFun x - w.toFun x
    filter_upwards [Lp.coeFn_sub v.toW1pGraph.1.1 w.toW1pGraph.1.1,
      v.coeFn_toW1pGraph_fst, w.coeFn_toW1pGraph_fst] with x hsub hv hw
    rw [hsub]
    simp only [Pi.sub_apply, hv, hw]
  have hnorm : ‖F‖ ≤ ‖v.toW1pGraph - w.toW1pGraph‖ := by
    rw [H1Graph.norm_eq_max]
    exact le_max_left _ _
  calc
    (∫ x, (v.toFun x - w.toFun x) ^ 2 ∂(volumeOn U)) =
        ‖F‖ ^ 2 :=
      integral_sq_eq_sq_norm_of_ae_eq F
        (fun x => v.toFun x - w.toFun x) hF
    _ ≤ ‖v.toW1pGraph - w.toW1pGraph‖ ^ 2 := by
      gcongr
    _ = dist v.toW1pGraph w.toW1pGraph ^ 2 := by
      rw [dist_eq_norm]

/-- The domain `L²` Euclidean-gradient error is bounded by the squared `H¹`
graph distance, with constant one. -/
theorem integral_sq_grad_sub_le_dist_sq
    {d : ℕ} {U : Set (Vec d)}
    (v w : W1pFunction U (2 : ℝ≥0∞)) :
    (∫ x, vecEuclideanNorm (v.grad x - w.grad x) ^ 2
        ∂(volumeOn U)) ≤
      dist v.toW1pGraph w.toW1pGraph ^ 2 := by
  let F : HilbertVectorLp U (2 : ℝ≥0∞) :=
    (v.toW1pGraph - w.toW1pGraph).1.2
  have hF : (fun x => ‖F x‖) =ᵐ[volumeOn U]
      fun x => vecEuclideanNorm (v.grad x - w.grad x) := by
    dsimp only [F]
    change (fun x =>
      ‖(v.toW1pGraph.1.2 - w.toW1pGraph.1.2) x‖) =ᵐ[volumeOn U]
        fun x => vecEuclideanNorm (v.grad x - w.grad x)
    filter_upwards [Lp.coeFn_sub v.toW1pGraph.1.2 w.toW1pGraph.1.2,
      v.coeFn_toW1pGraph_snd, w.coeFn_toW1pGraph_snd] with x hsub hv hw
    rw [hsub, Pi.sub_apply, hv, hw]
    change ‖(toHilbertVecField v.grad - toHilbertVecField w.grad) x‖ = _
    rw [congrFun (toHilbertVecField_sub v.grad w.grad) x]
    exact norm_toHilbertVecField_apply (fun x => v.grad x - w.grad x) x
  have hnorm : ‖F‖ ≤ ‖v.toW1pGraph - w.toW1pGraph‖ := by
    rw [H1Graph.norm_eq_max]
    exact le_max_right _ _
  calc
    (∫ x, vecEuclideanNorm (v.grad x - w.grad x) ^ 2
        ∂(volumeOn U)) = ‖F‖ ^ 2 :=
      integral_norm_sq_eq_sq_norm_of_ae_eq_hilbert F
        (fun x => vecEuclideanNorm (v.grad x - w.grad x)) hF
    _ ≤ ‖v.toW1pGraph - w.toW1pGraph‖ ^ 2 := by
      gcongr
    _ = dist v.toW1pGraph w.toW1pGraph ^ 2 := by
      rw [dist_eq_norm]

/-- Restricting the scalar value-error energy to a subset of the Sobolev
domain preserves the constant-one graph-distance bound. -/
theorem integralOn_sq_sub_toFun_le_dist_sq
    {d : ℕ} {U V : Set (Vec d)}
    (v w : W1pFunction U (2 : ℝ≥0∞))
    (hVU : V ⊆ U) :
    (∫ x in V, (v.toFun x - w.toFun x) ^ 2) ≤
      dist v.toW1pGraph w.toW1pGraph ^ 2 := by
  have hint : Integrable
      (fun x => (v.toFun x - w.toFun x) ^ 2) (volumeOn U) :=
    (v.memLp.sub w.memLp).integrable_sq
  calc
    (∫ x in V, (v.toFun x - w.toFun x) ^ 2) ≤
        ∫ x, (v.toFun x - w.toFun x) ^ 2 ∂(volumeOn U) :=
      integral_mono_measure
        (Measure.restrict_mono hVU le_rfl)
        (Filter.Eventually.of_forall fun _ => sq_nonneg _) hint
    _ ≤ dist v.toW1pGraph w.toW1pGraph ^ 2 :=
      integral_sq_sub_toFun_le_dist_sq v w

/-- Restricting the Euclidean-gradient error energy to a subset of the
Sobolev domain preserves the constant-one graph-distance bound. -/
theorem integralOn_sq_grad_sub_le_dist_sq
    {d : ℕ} {U V : Set (Vec d)}
    (v w : W1pFunction U (2 : ℝ≥0∞))
    (hVU : V ⊆ U) :
    (∫ x in V, vecEuclideanNorm (v.grad x - w.grad x) ^ 2) ≤
      dist v.toW1pGraph w.toW1pGraph ^ 2 := by
  have hmem : MemLp
      (fun x => vecEuclideanNorm (v.grad x - w.grad x))
      2 (volumeOn U) := by
    apply GradMemLpOn.memLp_vecEuclideanNorm
    intro i
    exact (v.gradMemLp i).sub (w.gradMemLp i)
  have hint : Integrable
      (fun x => vecEuclideanNorm (v.grad x - w.grad x) ^ 2)
      (volumeOn U) :=
    hmem.integrable_sq
  calc
    (∫ x in V, vecEuclideanNorm (v.grad x - w.grad x) ^ 2) ≤
        ∫ x, vecEuclideanNorm (v.grad x - w.grad x) ^ 2
          ∂(volumeOn U) :=
      integral_mono_measure
        (Measure.restrict_mono hVU le_rfl)
        (Filter.Eventually.of_forall fun _ => sq_nonneg _) hint
    _ ≤ dist v.toW1pGraph w.toW1pGraph ^ 2 :=
      integral_sq_grad_sub_le_dist_sq v w

/-- Nonnegative weighted graph-error summability transfers to the domain
scalar value-error energies. -/
theorem summable_weighted_integral_sq_sub_toFun
    {d : ℕ} {U : Set (Vec d)}
    (ψ : ℕ → W1pFunction U (2 : ℝ≥0∞))
    (u : W1pFunction U (2 : ℝ≥0∞)) (w : ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n)
    (hsum : Summable fun n =>
      w n * dist (ψ n).toW1pGraph u.toW1pGraph ^ 2) :
    Summable fun n => w n *
      ∫ x, ((ψ n).toFun x - u.toFun x) ^ 2 ∂(volumeOn U) := by
  refine Summable.of_nonneg_of_le ?_ ?_ hsum
  · intro n
    exact mul_nonneg (hw n) (integral_nonneg fun _ => sq_nonneg _)
  · intro n
    exact mul_le_mul_of_nonneg_left
      (integral_sq_sub_toFun_le_dist_sq (ψ n) u) (hw n)

/-- Nonnegative weighted graph-error summability transfers to the domain
Euclidean-gradient error energies. -/
theorem summable_weighted_integral_sq_grad_sub
    {d : ℕ} {U : Set (Vec d)}
    (ψ : ℕ → W1pFunction U (2 : ℝ≥0∞))
    (u : W1pFunction U (2 : ℝ≥0∞)) (w : ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n)
    (hsum : Summable fun n =>
      w n * dist (ψ n).toW1pGraph u.toW1pGraph ^ 2) :
    Summable fun n => w n *
      ∫ x, vecEuclideanNorm ((ψ n).grad x - u.grad x) ^ 2
        ∂(volumeOn U) := by
  refine Summable.of_nonneg_of_le ?_ ?_ hsum
  · intro n
    exact mul_nonneg (hw n) (integral_nonneg fun _ => sq_nonneg _)
  · intro n
    exact mul_le_mul_of_nonneg_left
      (integral_sq_grad_sub_le_dist_sq (ψ n) u) (hw n)

/-- Nonnegative weighted graph-error summability transfers to scalar
value-error energies on any subset of the Sobolev domain. -/
theorem summable_weighted_integralOn_sq_sub_toFun
    {d : ℕ} {U V : Set (Vec d)}
    (ψ : ℕ → W1pFunction U (2 : ℝ≥0∞))
    (u : W1pFunction U (2 : ℝ≥0∞)) (w : ℕ → ℝ)
    (hVU : V ⊆ U) (hw : ∀ n, 0 ≤ w n)
    (hsum : Summable fun n =>
      w n * dist (ψ n).toW1pGraph u.toW1pGraph ^ 2) :
    Summable fun n => w n *
      ∫ x in V, ((ψ n).toFun x - u.toFun x) ^ 2 := by
  refine Summable.of_nonneg_of_le ?_ ?_ hsum
  · intro n
    exact mul_nonneg (hw n) (integral_nonneg fun _ => sq_nonneg _)
  · intro n
    exact mul_le_mul_of_nonneg_left
      (integralOn_sq_sub_toFun_le_dist_sq (ψ n) u hVU) (hw n)

/-- Nonnegative weighted graph-error summability transfers to Euclidean
gradient-error energies on any subset of the Sobolev domain. -/
theorem summable_weighted_integralOn_sq_grad_sub
    {d : ℕ} {U V : Set (Vec d)}
    (ψ : ℕ → W1pFunction U (2 : ℝ≥0∞))
    (u : W1pFunction U (2 : ℝ≥0∞)) (w : ℕ → ℝ)
    (hVU : V ⊆ U) (hw : ∀ n, 0 ≤ w n)
    (hsum : Summable fun n =>
      w n * dist (ψ n).toW1pGraph u.toW1pGraph ^ 2) :
    Summable fun n => w n *
      ∫ x in V, vecEuclideanNorm ((ψ n).grad x - u.grad x) ^ 2 := by
  refine Summable.of_nonneg_of_le ?_ ?_ hsum
  · intro n
    exact mul_nonneg (hw n) (integral_nonneg fun _ => sq_nonneg _)
  · intro n
    exact mul_le_mul_of_nonneg_left
      (integralOn_sq_grad_sub_le_dist_sq (ψ n) u hVU) (hw n)

namespace H1Function

/-- Dyadically weighted graph errors control the full-domain scalar value
errors of approximants to an `H¹` representative. -/
theorem summable_dyadic_integral_sq_sub_toW1pFunction
    {d : ℕ} {U : Set (Vec d)}
    (ψ : ℕ → W1pFunction U (2 : ℝ≥0∞))
    (u : H1Function U)
    (hsum : Summable fun n =>
      (2 : ℝ) ^ n *
        dist (ψ n).toW1pGraph u.toW1pFunction.toW1pGraph ^ 2) :
    Summable fun n => (2 : ℝ) ^ n *
      ∫ x, ((ψ n).toFun x - u.toFun x) ^ 2 ∂(volumeOn U) := by
  exact summable_weighted_integral_sq_sub_toFun ψ u.toW1pFunction
    (fun n => (2 : ℝ) ^ n) (fun n => pow_nonneg (by norm_num) n) hsum

/-- Dyadically weighted graph errors control the full-domain Euclidean
gradient errors of approximants to an `H¹` representative. -/
theorem summable_dyadic_integral_sq_grad_sub_toW1pFunction
    {d : ℕ} {U : Set (Vec d)}
    (ψ : ℕ → W1pFunction U (2 : ℝ≥0∞))
    (u : H1Function U)
    (hsum : Summable fun n =>
      (2 : ℝ) ^ n *
        dist (ψ n).toW1pGraph u.toW1pFunction.toW1pGraph ^ 2) :
    Summable fun n => (2 : ℝ) ^ n *
      ∫ x, vecEuclideanNorm ((ψ n).grad x - u.grad x) ^ 2
        ∂(volumeOn U) := by
  exact summable_weighted_integral_sq_grad_sub ψ u.toW1pFunction
    (fun n => (2 : ℝ) ^ n) (fun n => pow_nonneg (by norm_num) n) hsum

/-- Dyadically weighted graph errors control scalar value-error energies on
any subset of the Sobolev domain. -/
theorem summable_dyadic_integralOn_sq_sub_toW1pFunction
    {d : ℕ} {U V : Set (Vec d)}
    (ψ : ℕ → W1pFunction U (2 : ℝ≥0∞))
    (u : H1Function U) (hVU : V ⊆ U)
    (hsum : Summable fun n =>
      (2 : ℝ) ^ n *
        dist (ψ n).toW1pGraph u.toW1pFunction.toW1pGraph ^ 2) :
    Summable fun n => (2 : ℝ) ^ n *
      ∫ x in V, ((ψ n).toFun x - u.toFun x) ^ 2 := by
  exact summable_weighted_integralOn_sq_sub_toFun ψ u.toW1pFunction
    (fun n => (2 : ℝ) ^ n) hVU
    (fun n => pow_nonneg (by norm_num) n) hsum

/-- Dyadically weighted graph errors control Euclidean-gradient error
energies on any subset of the Sobolev domain. -/
theorem summable_dyadic_integralOn_sq_grad_sub_toW1pFunction
    {d : ℕ} {U V : Set (Vec d)}
    (ψ : ℕ → W1pFunction U (2 : ℝ≥0∞))
    (u : H1Function U) (hVU : V ⊆ U)
    (hsum : Summable fun n =>
      (2 : ℝ) ^ n *
        dist (ψ n).toW1pGraph u.toW1pFunction.toW1pGraph ^ 2) :
    Summable fun n => (2 : ℝ) ^ n *
      ∫ x in V, vecEuclideanNorm ((ψ n).grad x - u.grad x) ^ 2 := by
  exact summable_weighted_integralOn_sq_grad_sub ψ u.toW1pFunction
    (fun n => (2 : ℝ) ^ n) hVU
    (fun n => pow_nonneg (by norm_num) n) hsum

end H1Function

end

end PDE

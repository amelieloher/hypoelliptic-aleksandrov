module

public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.Parabolic.Operator

/-!
# Pointwise parabolic minimum principle

This module proves the one-sided pointwise calculus statement behind the classical
forward parabolic minimum principle. At a local minimum relative to all earlier times,
the time derivative is nonpositive and the velocity Hessian is positive semidefinite.
Consequently, a positive semidefinite coefficient matrix gives the expected sign for
the forward parabolic operator.

The regularity assumption is pointwise `ContDiffAt ℝ 2 u z`. The second-derivative
argument is localized along affine lines through `z`; no global smoothness assumption
or comparison principle is used.

## Main results

* `velocityHessian_posSemidef_of_past_localMin`: positivity of the velocity Hessian.
* `timeDerivative_nonpos_of_past_localMin`: the one-sided time-derivative sign.
* `parabolicOperator_nonpos_of_past_localMin`: the pointwise operator sign.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter Set Matrix
open scoped MatrixOrder Topology

private theorem deriv_deriv_nonneg_of_isLocalMin
    {f : ℝ → ℝ} {a c : ℝ}
    (hmin : IsLocalMin f a)
    (hsecond : HasDerivAt (deriv f) c a)
    (hcont : ContinuousAt f a) :
    0 ≤ c := by
  by_contra hc
  have hcneg : c < 0 := lt_of_not_ge hc
  have hmax : IsLocalMax f a :=
    isLocalMax_of_deriv_deriv_neg
      (by simpa only [hsecond.deriv] using hcneg)
      hmin.deriv_eq_zero hcont
  have heq : f =ᶠ[𝓝 a] fun _ => f a := by
    filter_upwards [hmin, hmax] with y hymin hymax
    exact le_antisymm hymax hymin
  have hderivEq : deriv f =ᶠ[𝓝 a] fun _ => 0 := by
    filter_upwards [heq.deriv] with y hy
    rw [hy]
    exact deriv_const y (f a)
  have : c = 0 := by
    calc
      c = deriv (deriv f) a := hsecond.deriv.symm
      _ = deriv (fun _ => 0) a := hderivEq.deriv_eq
      _ = 0 := deriv_const _ _
  exact (ne_of_lt hcneg) this

private theorem hasDerivAt_affine_line
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x q : E) (s : ℝ) :
    HasDerivAt (fun r : ℝ => x + r • q) q s := by
  simpa only [one_smul] using
    ((hasDerivAt_id' (𝕜 := ℝ) s).smul_const q).const_add x

private theorem hasDerivAt_fderiv_restrict_affine_line
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} {x q : E}
    {H : E →L[ℝ] E →L[ℝ] ℝ}
    (hsecond : HasFDerivAt (fderiv ℝ g) H x) :
    HasDerivAt
      (fun r : ℝ => fderiv ℝ g (x + r • q) q)
      (H q q) 0 := by
  have hline : HasDerivAt (fun r : ℝ => x + r • q) q 0 :=
    hasDerivAt_affine_line x q 0
  have hsecond' : HasFDerivAt (fderiv ℝ g) H (x + (0 : ℝ) • q) := by
    simpa only [zero_smul, add_zero] using hsecond
  have hgrad : HasDerivAt (fun r : ℝ => fderiv ℝ g (x + r • q)) (H q) 0 :=
    hsecond'.comp_hasDerivAt 0 hline
  simpa only [zero_smul, add_zero, map_zero] using
    hgrad.clm_apply (hasDerivAt_const (x := 0) (c := q))

private theorem hasDerivAt_deriv_restrict_affine_line_of_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} {x q : E}
    (hg : ContDiffAt ℝ 2 g x) :
    HasDerivAt (deriv (fun r : ℝ => g (x + r • q)))
      (fderiv ℝ (fderiv ℝ g) x q q) 0 := by
  have hgGradDiffAt : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hEvalLine : HasDerivAt
      (fun r : ℝ => fderiv ℝ g (x + r • q) q)
      (fderiv ℝ (fderiv ℝ g) x q q) 0 :=
    hasDerivAt_fderiv_restrict_affine_line hgGradDiffAt.hasFDerivAt
  have hgEventually : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 g y :=
    hg.eventually (by norm_num)
  have hgEventuallyAtLineZero :
      ∀ᶠ y in 𝓝 (x + (0 : ℝ) • q), ContDiffAt ℝ 2 g y := by
    simpa only [zero_smul, add_zero] using hgEventually
  apply hEvalLine.congr_of_eventuallyEq
  filter_upwards [
    (hasDerivAt_affine_line x q 0).continuousAt hgEventuallyAtLineZero] with r hr
  change ContDiffAt ℝ 2 g (x + r • q) at hr
  exact (hr.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt
    r (hasDerivAt_affine_line x q r) |>.deriv

private theorem fderiv_fderiv_apply_nonneg_of_isLocalMin_affineLine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} {x q : E}
    (hg : ContDiffAt ℝ 2 g x)
    (hmin : IsLocalMin (fun r : ℝ => g (x + r • q)) 0) :
    0 ≤ fderiv ℝ (fderiv ℝ g) x q q := by
  have hlineCont : ContinuousAt (fun r : ℝ => x + r • q) 0 :=
    (hasDerivAt_affine_line x q 0).continuousAt
  have hgAtLineZero : ContinuousAt g (x + (0 : ℝ) • q) := by
    simpa only [zero_smul, add_zero] using hg.continuousAt
  have hcompCont : ContinuousAt (fun r : ℝ => g (x + r • q)) 0 :=
    hgAtLineZero.comp' (f := fun r : ℝ => x + r • q) hlineCont
  exact deriv_deriv_nonneg_of_isLocalMin hmin
    (hasDerivAt_deriv_restrict_affine_line_of_contDiffAt hg) hcompCont

private theorem time_slice_hasDerivAt
    {d : ℕ} {u : TimeVelocity d → ℝ} {z : TimeVelocity d}
    (hu : ContDiffAt ℝ 2 u z) :
    HasDerivAt (fun t : ℝ => u (t, z.2)) (timeDerivative u z) z.1 := by
  have huDiff : DifferentiableAt ℝ u z := hu.differentiableAt (by norm_num)
  have hline : HasDerivAt (fun t : ℝ => (t, z.2)) ((1, 0) : TimeVelocity d) z.1 := by
    exact
      ((hasDerivAt_id' (𝕜 := ℝ) z.1).prodMk
        (hasDerivAt_const (x := z.1) (c := z.2)))
  simpa only [timeDerivative, Function.comp_def] using huDiff.hasFDerivAt.comp_hasDerivAt z.1 hline

private theorem velocityHessian_isSymm_of_contDiffAt
    {d : ℕ} {u : TimeVelocity d → ℝ} {z : TimeVelocity d}
    (hu : ContDiffAt ℝ 2 u z) :
    (velocityHessian u z).IsSymm := by
  refine Matrix.IsSymm.ext ?_
  intro i j
  simpa [velocityHessian] using
    (hu.isSymmSndFDerivAt (by norm_num)).eq
      ((0 : ℝ), Pi.single j 1) ((0 : ℝ), Pi.single i 1)

/-- A past-relative local minimum is a local minimum on the velocity slice. -/
theorem spatial_localMin_of_past_localMin
    {d : ℕ} {u : TimeVelocity d → ℝ} {z : TimeVelocity d}
    (hmin : IsLocalMinOn u (Set.Iic z.1 ×ˢ Set.univ) z) :
    IsLocalMin (fun v : PDE.Vec d => u (z.1, v)) z.2 := by
  apply isLocalMinOn_univ_iff.mp
  simpa only [Function.comp_def, id_eq] using hmin.comp_continuousOn
    (s := Set.univ)
    (by intro v _; simp)
    (continuous_const.prodMk continuous_id).continuousOn (Set.mem_univ z.2)

/-- At a past-relative local minimum of a pointwise `C²` function, the velocity Hessian
is positive semidefinite. -/
theorem velocityHessian_posSemidef_of_past_localMin
    {d : ℕ} {u : TimeVelocity d → ℝ} {z : TimeVelocity d}
    (hu : ContDiffAt ℝ 2 u z)
    (hmin : IsLocalMinOn u (Set.Iic z.1 ×ˢ Set.univ) z) :
    (velocityHessian u z).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    simpa only [star_trivial] using
      (velocityHessian_isSymm_of_contDiffAt hu).apply i j
  · intro q
    have hspatial : IsLocalMin (fun v : PDE.Vec d => u (z.1, v)) z.2 :=
      spatial_localMin_of_past_localMin hmin
    have hspatialAtLineZero : IsLocalMin (fun v : PDE.Vec d => u (z.1, v))
        (z.2 + (0 : ℝ) • q) := by
      simpa only [zero_smul, add_zero] using hspatial
    have hlineMinSpatial : IsLocalMin
        (fun r : ℝ => u (z.1, z.2 + r • q)) 0 := by
      simpa only [Function.comp_def, id_eq] using
        hspatialAtLineZero.comp_continuous
          (g := fun r : ℝ => z.2 + r • q)
          (hasDerivAt_affine_line z.2 q 0).continuousAt
    let direction : TimeVelocity d := (0, q)
    have hlineEq :
        (fun r : ℝ => u (z + r • direction)) =
          fun r : ℝ => u (z.1, z.2 + r • q) := by
      funext r
      congr 1
      apply Prod.ext <;> simp [direction]
    have hlineMin : IsLocalMin (fun r : ℝ => u (z + r • direction)) 0 := by
      rw [hlineEq]
      exact hlineMinSpatial
    simp only [star_trivial]
    rw [velocityHessian_quadratic_eq]
    simpa only [direction] using
      fderiv_fderiv_apply_nonneg_of_isLocalMin_affineLine hu hlineMin

/-- At a past-relative local minimum of a pointwise `C²` function, the time derivative
is nonpositive. -/
theorem timeDerivative_nonpos_of_past_localMin
    {d : ℕ} {u : TimeVelocity d → ℝ} {z : TimeVelocity d}
    (hu : ContDiffAt ℝ 2 u z)
    (hmin : IsLocalMinOn u (Set.Iic z.1 ×ˢ Set.univ) z) :
    timeDerivative u z ≤ 0 := by
  have htimeMin : IsLocalMinOn (fun t : ℝ => u (t, z.2)) (Set.Iic z.1) z.1 := by
    simpa only [Function.comp_def, id_eq] using hmin.comp_continuousOn
      (s := Set.Iic z.1)
      (by rintro t ht; exact ⟨ht, Set.mem_univ t⟩)
      (continuous_id.prodMk continuous_const).continuousOn (by simp)
  have htimeDeriv : HasDerivAt (fun t : ℝ => u (t, z.2))
      (timeDerivative u z) z.1 :=
    time_slice_hasDerivAt hu
  have hminusOne : (-1 : ℝ) ∈ posTangentConeAt (Set.Iic z.1) z.1 := by
    have hsegment : segment ℝ z.1 (z.1 - 1) ⊆ Set.Iic z.1 := by
      intro s hs
      rw [segment_symm] at hs
      exact (segment_subset_Icc (sub_le_self _ (by norm_num : (0 : ℝ) ≤ 1)) hs).2
    simpa using sub_mem_posTangentConeAt_of_segment_subset hsegment
  have htimeFDeriv := HasDerivAt.hasFDerivAt htimeDeriv
  have hnonneg := htimeMin.hasFDerivWithinAt_nonneg
    htimeFDeriv.hasFDerivWithinAt hminusOne
  have hneg : 0 ≤ -timeDerivative u z := by
    simpa using hnonneg
  linarith

/-- The trace of the product of two real positive semidefinite matrices is nonnegative. -/
theorem trace_mul_nonneg_of_posSemidef
    {d : ℕ} {A H : PDE.Mat d}
    (hA : A.PosSemidef) (hH : H.PosSemidef) :
    0 ≤ (A * H).trace := by
  classical
  let S : PDE.Mat d := CFC.sqrt H
  have hS : S.PosSemidef := by
    dsimp [S]
    exact CFC.sqrt_nonneg H |>.posSemidef
  have hconj : (S * A * Sᴴ).PosSemidef := hA.mul_mul_conjTranspose_same S
  calc
    0 ≤ (S * A * Sᴴ).trace := hconj.trace_nonneg
    _ = (S * A * S).trace := by rw [hS.isHermitian.eq]
    _ = (A * S * S).trace := (Matrix.trace_mul_cycle A S S).symm
    _ = (A * (S * S)).trace := by rw [Matrix.mul_assoc]
    _ = (A * H).trace := by rw [show S * S = H by
      dsimp [S]
      exact CFC.sqrt_mul_sqrt_self H hH.nonneg]

/-- At a past-relative local minimum of a pointwise `C²` function, the forward
parabolic operator is nonpositive for a positive semidefinite coefficient matrix. -/
theorem parabolicOperator_nonpos_of_past_localMin
    {d : ℕ} {A : CoefficientField d} {u : TimeVelocity d → ℝ} {z : TimeVelocity d}
    (hu : ContDiffAt ℝ 2 u z)
    (hmin : IsLocalMinOn u (Set.Iic z.1 ×ˢ Set.univ) z)
    (hA : (coefficientAt A z).PosSemidef) :
    parabolicOperator A u z ≤ 0 := by
  have htime : timeDerivative u z ≤ 0 :=
    timeDerivative_nonpos_of_past_localMin hu hmin
  have hHessian : (velocityHessian u z).PosSemidef :=
    velocityHessian_posSemidef_of_past_localMin hu hmin
  have htrace : 0 ≤ (coefficientAt A z * velocityHessian u z).trace :=
    trace_mul_nonneg_of_posSemidef hA hHessian
  rw [parabolicOperator_apply,
    HypoellipticAleksandrov.matrixContraction_eq_trace_mul_of_isSymm _ _
      (velocityHessian_isSymm_of_contDiffAt hu)]
  linarith

end HypoellipticAleksandrov.Parabolic

module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Flow.Commutator

/-!
# The heat identity for the Gaussian flow

The Gaussian flow estimates: `∂_h Φ_h = M^h : D² Φ_h` with
`M^h : D² = (λ/2)(2 h² Δ_z - 2 h ∇_z · ∇_v + Δ_v)`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open Real

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

theorem hasDerivAt_flowConst {lam h : ℝ} (hl : 0 < lam) (hh : 0 < h) :
    HasDerivAt (flowConst lam) (-2 * flowConst lam h / h) h := by
  have h2 : (2 * π * lam * h ^ 2) ≠ 0 := by positivity
  have := (hasDerivAt_const h (√(12 / 5 : ℝ))).div
    ((hasDerivAt_pow 2 h).const_mul (2 * π * lam)) h2
  unfold flowConst
  refine this.congr_deriv ?_
  field_simp
  simp
  ring

theorem hasDerivAt_flowA {lam h : ℝ} (hl : 0 < lam) (hh : 0 < h) :
    HasDerivAt (flowA lam) (-3 * flowA lam h / h) h := by
  have h2 : (5 * lam * h ^ 3) ≠ 0 := by positivity
  have := (hasDerivAt_const h (6 : ℝ)).div ((hasDerivAt_pow 3 h).const_mul (5 * lam)) h2
  unfold flowA
  refine this.congr_deriv ?_
  field_simp
  simp
  ring

theorem hasDerivAt_flowB {lam h : ℝ} (hl : 0 < lam) (hh : 0 < h) :
    HasDerivAt (flowB lam) (-2 * flowB lam h / h) h := by
  have h2 : (5 * lam * h ^ 2) ≠ 0 := by positivity
  have := (hasDerivAt_const h (6 : ℝ)).div ((hasDerivAt_pow 2 h).const_mul (5 * lam)) h2
  unfold flowB
  refine this.congr_deriv ?_
  field_simp
  simp
  ring

theorem hasDerivAt_flowC {lam h : ℝ} (hl : 0 < lam) (hh : 0 < h) :
    HasDerivAt (flowC lam) (-flowC lam h / h) h := by
  have h2 : (5 * lam * h) ≠ 0 := by positivity
  have := (hasDerivAt_const h (4 : ℝ)).div ((hasDerivAt_id h).const_mul (5 * lam)) h2
  unfold flowC
  refine this.congr_deriv ?_
  simp
  field_simp

/-- The `h`-derivative of the flow kernel at a fixed phase-space point. -/
theorem hasDerivAt_flowKernel_param {lam h : ℝ} (hl : 0 < lam) (hh : 0 < h)
    (y : EvolutionAmbientState d) :
    HasDerivAt (fun h' => flowKernel lam h' y)
      (flowKernel lam h y * ∑ i, (-2 / h + (3 * flowA lam h * y.2 i ^ 2 +
        2 * flowB lam h * y.2 i * y.1 i + flowC lam h * y.1 i ^ 2) / h)) h := by
  have hev : (fun h' => flowKernel lam h' y) =ᶠ[nhds h] fun h' =>
      flowConst lam h' ^ d * rexp (-(∑ i, (flowA lam h' * y.2 i ^ 2 +
        flowB lam h' * y.2 i * y.1 i + flowC lam h' * y.1 i ^ 2))) := by
    filter_upwards [Ioi_mem_nhds hh] with h' hh'
    exact flowKernel_eq hl hh' y
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  have hK := (hasDerivAt_flowConst hl hh).pow d
  have hA := hasDerivAt_flowA hl hh
  have hB := hasDerivAt_flowB hl hh
  have hC := hasDerivAt_flowC hl hh
  have hQ : HasDerivAt (fun h' => ∑ i, (flowA lam h' * y.2 i ^ 2 +
        flowB lam h' * y.2 i * y.1 i + flowC lam h' * y.1 i ^ 2))
      (∑ i, ((-3 * flowA lam h / h) * y.2 i ^ 2 + (-2 * flowB lam h / h) * y.2 i * y.1 i +
        (-flowC lam h / h) * y.1 i ^ 2)) h := by
    refine HasDerivAt.fun_sum fun i _ => ?_
    exact (((hA.mul_const _).add ((hB.mul_const _).mul_const _)).add (hC.mul_const _))
  have hE := (hQ.neg).exp
  have := hK.mul hE
  refine this.congr_deriv ?_
  have hpos := flowConst_pos hl hh
  have hk : flowConst lam h ^ d * rexp (-(∑ i, (flowA lam h * y.2 i ^ 2 +
        flowB lam h * y.2 i * y.1 i + flowC lam h * y.1 i ^ 2))) = flowKernel lam h y :=
    (flowKernel_eq hl hh y).symm
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
    set X : Fin (n + 1) → ℝ := fun i => 3 * flowA lam h * y.2 i ^ 2 +
      2 * flowB lam h * y.2 i * y.1 i + flowC lam h * y.1 i ^ 2 with hX
    have e1 : ∑ i, (-2 / h + (3 * flowA lam h * y.2 i ^ 2 +
        2 * flowB lam h * y.2 i * y.1 i + flowC lam h * y.1 i ^ 2) / h) =
        -2 * ((n : ℝ) + 1) / h + (∑ i, X i) / h := by
      rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.sum_div]
      simp
      ring
    have e2 : -∑ i, ((-3 * flowA lam h / h) * y.2 i ^ 2 +
        (-2 * flowB lam h / h) * y.2 i * y.1 i + (-flowC lam h / h) * y.1 i ^ 2) =
        (∑ i, X i) / h := by
      rw [← Finset.sum_neg_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hX]
      ring
    rw [e1, ← hk]
    simp only [Pi.neg_apply, Pi.pow_apply, e2]
    push_cast
    rw [pow_succ]
    ring

theorem velocityPartial_velocityPartial_flowKernel {lam h : ℝ} (hl : 0 < lam) (hh : 0 < h)
    (i : Fin d) (y : EvolutionAmbientState d) :
    velocityPartial i (velocityPartial i (flowKernel lam h)) y =
      flowConst lam h ^ d * ((flowB lam h * y.2 i + 2 * flowC lam h * y.1 i) ^ 2
        - 2 * flowC lam h) * gaussExp (flowA lam h) (flowB lam h) (flowC lam h) y := by
  change dirPartial (Sum.inl i) (dirPartial (Sum.inl i) (flowKernel lam h)) y = _
  rw [flowKernel_funext hl hh, dirPartial_dirPartial_gaussExp]
  simp only [gen, genCoeff, ↓reduceIte]
  ring

/-- The Gaussian flow estimates, the heat identity `∂_h Φ_h = M^h : D² Φ_h`. -/
theorem hasDerivAt_flowKernel {lam h : ℝ} (hl : 0 < lam) (hh : 0 < h)
    (y : EvolutionAmbientState d) :
    HasDerivAt (fun h' => flowKernel lam h' y)
      ((lam / 2) * (2 * h ^ 2 * positionLaplacian (flowKernel lam h) y -
        2 * h * mixedDivergence (flowKernel lam h) y +
        velocityLaplacian (flowKernel lam h) y)) h := by
  refine (hasDerivAt_flowKernel_param hl hh y).congr_deriv ?_
  unfold positionLaplacian mixedDivergence velocityLaplacian
  simp_rw [positionPartial_positionPartial_flowKernel hl hh,
    positionPartial_velocityPartial_flowKernel hl hh,
    velocityPartial_velocityPartial_flowKernel hl hh, flowKernel_eq hl hh y]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum]
  have key : ∑ i : Fin d, (-2 / h + (3 * flowA lam h * y.2 i ^ 2 +
      2 * flowB lam h * y.2 i * y.1 i + flowC lam h * y.1 i ^ 2) / h) =
      (lam / 2) * (2 * h ^ 2 * ∑ i : Fin d, ((2 * flowA lam h * y.2 i + flowB lam h * y.1 i) ^ 2
          - 2 * flowA lam h) -
        2 * h * ∑ i : Fin d, ((flowB lam h * y.2 i + 2 * flowC lam h * y.1 i) *
          (2 * flowA lam h * y.2 i + flowB lam h * y.1 i) - flowB lam h) +
        ∑ i : Fin d, ((flowB lam h * y.2 i + 2 * flowC lam h * y.1 i) ^ 2 -
          2 * flowC lam h)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold flowA flowB flowC
    field_simp
    ring
  rw [key]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

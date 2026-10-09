module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.W21Density

/-!
# `r^q |β|²` is a smooth `W^{2,1}` function

The smoothing estimates: writing `J = βr = (Fm)_h`, one has
`r^q |β|² = ∑ᵢⱼ r^{q-2} Jᵢⱼ²`, and the first and second derivatives of each summand are dominated by
`r^{q-1}|Dr|`, `r^{q-1}|DJ|`, `r^{q-1}|D²r|`, `r^{q-1}|D²J|`, `r^{q-2}|Dr|²`, `r^{q-2}|DJ|²`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ} {lam Lam : ℝ} {Φ : SmoothingKernelFamily d lam} {h q : ℝ}
  {F : EvolutionAmbientState d → PDE.Mat d} {m : Measure (EvolutionAmbientState d)}

theorem rpow_sub_two_mul_self {u : ℝ} (hu : 0 < u) (q : ℝ) :
    u ^ (q - 2) * u = u ^ (q - 1) := by
  rw [← Real.rpow_add_one hu.ne']; ring_nf

theorem rpow_sub_one_mul_self {u : ℝ} (hu : 0 < u) (q : ℝ) :
    u ^ (q - 1) * u = u ^ q := by
  rw [← Real.rpow_add_one hu.ne']; ring_nf

theorem smoothW21_entry [IsFiniteMeasure m] (hlam : 0 < lam) (hLam' : lam ≤ Lam)
    (hF : IsAdmissibleCoefficient lam Lam F) (hh : 0 < h) (hm : m ≠ 0) (i j : Fin d)
    (hI0 : Integrable (integrandPow Φ h m q)) (hIg : Integrable (integrandGrad Φ h m q))
    (hIh : Integrable (integrandHess Φ h m q)) (hIf : Integrable (integrandFisher Φ h m q))
    (hJg : Integrable (integrandFluxGrad Φ h F m q))
    (hJh : Integrable (integrandFluxHess Φ h F m q))
    (hJf : Integrable (integrandFluxFisher Φ h F m q)) :
    SmoothW21 (fun y => smoothDensity Φ h m y ^ (q - 2) * smoothFlux Φ h F m y i j ^ 2) := by
  have hLam : 0 ≤ Lam := (hlam.trans_le hLam').le
  set u := smoothDensity Φ h m with hudef
  set J : EvolutionAmbientState d → ℝ := fun y => smoothFlux Φ h F m y i j with hJdef
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := contDiff_smoothDensity Φ m hh
  have hpos : ∀ y, 0 < u y := smoothDensity_pos Φ m hh hm
  have hJc : ContDiff ℝ (⊤ : ℕ∞) J := contDiff_smoothFluxEntry Φ m hlam hF hh i j
  have hw : ContDiff ℝ (⊤ : ℕ∞) (fun y => J y ^ 2) := hJc.pow 2
  have hJb : ∀ y, |J y| ≤ Lam * u y := fun y => by
    have e : J y = u y * smoothCoefficient Φ h F m y i j :=
      smoothFluxEntry_eq_mul Φ m hh hm i j y
    rw [e, abs_mul, abs_of_pos (hpos y), mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_smoothCoefficient_le Φ m hlam hF hh y i j)
      (hpos y).le
  set s : ℝ := q - 2 with hs
  have hG : ContDiff ℝ (⊤ : ℕ∞) (fun y => u y ^ s * J y ^ 2) := contDiff_rpow_mul hu hw hpos s
  have hd : ∀ {f : EvolutionAmbientState d → ℝ} {y : EvolutionAmbientState d},
      ContDiff ℝ (⊤ : ℕ∞) f → DifferentiableAt ℝ f y := fun hf => (hf.differentiable (by simp)) _
  -- partials of w = J²
  have hw1 : ∀ c, coordPartial c (fun y => J y ^ 2) = fun y => 2 * J y * coordPartial c J y :=
    fun c => funext fun y => coordPartial_sq c (hd hJc)
  have hw2 : ∀ c c' y, coordPartial c' (coordPartial c (fun y => J y ^ 2)) y =
      2 * (coordPartial c' J y * coordPartial c J y +
        J y * coordPartial c' (coordPartial c J) y) := by
    intro c c' y
    rw [hw1 c]
    have hJ1 : ContDiff ℝ (⊤ : ℕ∞) (coordPartial c J) := contDiff_coordPartial hJc c
    have e1 : (fun y => 2 * J y * coordPartial c J y) =
        fun y => 2 * (J y * coordPartial c J y) := by funext y; ring
    rw [e1, coordPartial_const_mul' c' 2 (hd (hJc.mul hJ1)), coordPartial_mul c' (hd hJc) (hd hJ1)]
    ring
  have hQ : ∀ y, u y ^ s = u y * u y ^ (s - 1) := fun y => by
    rw [mul_comm, ← Real.rpow_add_one (hpos y).ne']; ring_nf
  have hQ1 : ∀ y, u y ^ (s - 1) = u y * u y ^ (s - 2) := fun y => by
    rw [mul_comm, ← Real.rpow_add_one (hpos y).ne']; ring_nf
  refine ⟨hG, ?_, fun c => ?_, fun c c' => ?_⟩
  · refine (hI0.const_mul (Lam ^ 2)).mono' hG.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (hpos y).le _) (sq_nonneg _))]
    have h1 : J y ^ 2 ≤ (Lam * u y) ^ 2 := by
      rw [← sq_abs (J y)]; exact pow_le_pow_left₀ (abs_nonneg _) (hJb y) 2
    have h2 : u y ^ s * u y ^ 2 = u y ^ q := by
      have := rpow_sub_one_mul_self (hpos y) q
      rw [← rpow_sub_two_mul_self (hpos y) q] at this
      rw [hs]; nlinarith [this, Real.rpow_nonneg (hpos y).le (q - 2)]
    calc u y ^ s * J y ^ 2 ≤ u y ^ s * (Lam * u y) ^ 2 :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (hpos y).le _)
      _ = Lam ^ 2 * integrandPow Φ h m q y := by
          unfold integrandPow; rw [← h2]; ring
  · -- first derivatives
    have hc := coordPartial_rpow_mul hu hw hpos s c
    rw [hc]
    refine ((hIg.const_mul (|s| * Lam ^ 2)).add (hJg.const_mul (2 * Lam))).mono'
      ?_ (Filter.Eventually.of_forall fun y => ?_)
    · rw [← hc]; exact (continuous_coordPartial hG c).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      have h1 := first_bound_G (s := s) (Q := u y ^ s) (Q1 := u y ^ (s - 1)) (U := u y)
        (J := J y) (a := coordPartial c u y) (b := coordPartial c J y) (Lam := Lam)
        (HA := gradNorm u y) (HB := coefficientGradNorm (smoothFlux Φ h F m) y) (hpos y)
        (Real.rpow_nonneg (hpos y).le _) (Real.rpow_nonneg (hpos y).le _) (hQ y) (hJb y) hLam
        (abs_coordPartial_le_gradNorm u y c)
        (abs_coordPartial_entry_le (smoothFlux Φ h F m) y i j c)
      have hQU : u y ^ s * u y = u y ^ (q - 1) := rpow_sub_two_mul_self (hpos y) q
      simp only [hw1 c] at h1 ⊢
      refine h1.trans (le_of_eq ?_)
      simp only [integrandGrad, integrandFluxGrad, Pi.add_apply, ← hudef]
      rw [← hQU]
      try ring
  · -- second derivatives
    have hform : ∀ y, coordPartial c' (coordPartial c (fun y => u y ^ s * J y ^ 2)) y =
        s * (s - 1) * u y ^ (s - 2) * coordPartial c' u y * coordPartial c u y * J y ^ 2 +
        s * u y ^ (s - 1) * coordPartial c' (coordPartial c u) y * J y ^ 2 +
        s * u y ^ (s - 1) * coordPartial c u y * (2 * J y * coordPartial c' J y) +
        s * u y ^ (s - 1) * coordPartial c' u y * (2 * J y * coordPartial c J y) +
        u y ^ s * (2 * coordPartial c' J y * coordPartial c J y +
          2 * J y * coordPartial c' (coordPartial c J) y) := by
      intro y
      rw [coordPartial₂_rpow_mul hu hw hpos s c c' y, hw2 c c' y, hw1 c', hw1 c]
      beta_reduce
      ring
    have hfun : coordPartial c' (coordPartial c (fun y => u y ^ s * J y ^ 2)) = fun y => _ :=
      funext hform
    rw [hfun]
    set A1 : ℝ := |s * (s - 1)| * Lam ^ 2 + 2 * |s| * Lam
    refine (((hIf.const_mul A1).add (hIh.const_mul (|s| * Lam ^ 2))).add
      ((hJf.const_mul (2 * |s| * Lam + 2)).add (hJh.const_mul (2 * Lam)))).mono' ?_
      (Filter.Eventually.of_forall fun y => ?_)
    · rw [← hfun]
      exact (continuous_coordPartial (contDiff_coordPartial hG c) c').aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      have h1 := second_bound_G (s := s) (Q := u y ^ s) (Q1 := u y ^ (s - 1))
        (Q2 := u y ^ (s - 2)) (U := u y) (J := J y)
        (a := coordPartial c u y) (a' := coordPartial c' u y)
        (a'' := coordPartial c' (coordPartial c u) y) (b := coordPartial c J y)
        (b' := coordPartial c' J y) (b'' := coordPartial c' (coordPartial c J) y) (Lam := Lam)
        (GS := gradNormSq u y) (FG := coefficientGradNormSq (smoothFlux Φ h F m) y)
        (HS := hessNorm u y) (HG := coefficientHessNorm (smoothFlux Φ h F m) y) (hpos y)
        (Real.rpow_nonneg (hpos y).le _) (hQ1 y) (hQ y) (hJb y) hLam
        (sq_coordPartial_le_gradNormSq u y c) (sq_coordPartial_le_gradNormSq u y c')
        (sq_coordPartial_entry_le (smoothFlux Φ h F m) y i j c)
        (sq_coordPartial_entry_le (smoothFlux Φ h F m) y i j c')
        (abs_coordPartial₂_le_hessNorm u y c' c)
        (abs_coordPartial₂_entry_le (smoothFlux Φ h F m) y i j c' c)
      have hQU : u y ^ s * u y = u y ^ (q - 1) := rpow_sub_two_mul_self (hpos y) q
      refine h1.trans (le_of_eq ?_)
      simp only [integrandFisher, integrandHess, integrandFluxFisher, integrandFluxHess,
        Pi.add_apply, ← hudef]
      rw [← hQU]
      try ring

theorem smoothW21_zero : SmoothW21 (fun _ : EvolutionAmbientState d => (0 : ℝ)) := by
  have z : ∀ c : Fin d ⊕ Fin d, coordPartial c (fun _ : EvolutionAmbientState d => (0 : ℝ)) =
      fun _ => 0 := fun c => coordPartial_const c 0
  refine ⟨contDiff_const, integrable_zero _ _ _, fun c => ?_, fun c c' => ?_⟩
  · rw [z c]; exact integrable_zero _ _ _
  · rw [z c, z c']; exact integrable_zero _ _ _

/-- The smoothing estimates: `r^q` and `r^q |β|²` are smooth `W^{2,1}` functions. -/
theorem smoothW21_of_packageIntegrable [IsFiniteMeasure m] {C : ℝ} (hlam : 0 < lam)
    (hLam' : lam ≤ Lam) (hq : 1 < q) (hF : IsAdmissibleCoefficient lam Lam F) (hh : 0 < h)
    (hP : PackageIntegrable Φ h F m q C) :
    SmoothW21 (integrandPow Φ h m q) ∧ SmoothW21 (integrandPowBeta Φ h F m q) := by
  by_cases hm : m = 0
  · subst hm
    have hq0 : q ≠ 0 := by linarith
    have e1 : integrandPow Φ h (0 : Measure (EvolutionAmbientState d)) q = fun _ => 0 := by
      funext y; simp [integrandPow, smoothDensity_zero, Real.zero_rpow hq0]
    have e2 : integrandPowBeta Φ h F (0 : Measure (EvolutionAmbientState d)) q = fun _ => 0 := by
      funext y; simp [integrandPowBeta, smoothDensity_zero, Real.zero_rpow hq0]
    rw [e1, e2]
    exact ⟨smoothW21_zero, smoothW21_zero⟩
  · refine ⟨smoothW21_rpow_density hh hm hP.pow.1 hP.grad.1 hP.hess.1 hP.fisher.1, ?_⟩
    have hpos : ∀ y, 0 < smoothDensity Φ h m y := smoothDensity_pos Φ m hh hm
    have e : integrandPowBeta Φ h F m q = fun y => ∑ i, ∑ j,
        smoothDensity Φ h m y ^ (q - 2) * smoothFlux Φ h F m y i j ^ 2 := by
      funext y
      unfold integrandPowBeta frobeniusSq
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hJ : smoothFlux Φ h F m y i j =
          smoothDensity Φ h m y * smoothCoefficient Φ h F m y i j :=
        smoothFluxEntry_eq_mul Φ m hh hm i j y
      have h2 : smoothDensity Φ h m y ^ (q - 2) * smoothDensity Φ h m y ^ 2 =
          smoothDensity Φ h m y ^ q := by
        have e := rpow_sub_one_mul_self (hpos y) q
        rw [← rpow_sub_two_mul_self (hpos y) q] at e
        rw [← e]; ring
      rw [hJ, mul_pow, ← mul_assoc, h2]
    rw [e]
    exact SmoothW21.sum _ fun i _ => SmoothW21.sum _ fun j _ =>
      smoothW21_entry hlam hLam' hF hh hm i j hP.pow.1 hP.grad.1 hP.hess.1 hP.fisher.1
        hP.fluxGrad.1 hP.fluxHess.1 hP.fluxFisher.1

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

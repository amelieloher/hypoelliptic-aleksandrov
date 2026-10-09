module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.NormBounds

/-!
# Pointwise bounds for the integrands of the integrability list

For `m ≠ 0` (so `r = m_h > 0`), each integrand of the integrability list of the smoothing
estimates is bounded pointwise by a constant times `R^{q-1}` times `smoothWeight2`, where `R` is
an upper bound of `r`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory Real

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ} {lam Lam : ℝ} {Φ : SmoothingKernelFamily d lam} {h : ℝ}
  {F : EvolutionAmbientState d → PDE.Mat d}
  (m : Measure (EvolutionAmbientState d)) [IsFiniteMeasure m]

theorem rpow_density_aux {r R q : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hq : 1 < q) :
    r ^ (q - 1) ≤ R ^ (q - 1) ∧ 0 ≤ r ^ (q - 1) ∧ r ^ q = r ^ (q - 1) * r ∧
      r ^ (q - 2) * r = r ^ (q - 1) := by
  refine ⟨Real.rpow_le_rpow hr.le hrR (by linarith), (Real.rpow_pos_of_pos hr _).le, ?_, ?_⟩
  · rw [← Real.rpow_add_one hr.ne']; ring_nf
  · rw [← Real.rpow_add_one hr.ne']; ring_nf

section Pointwise

variable {C1 C2 Cfi R q : ℝ} (hlam : 0 < lam) (hLam' : lam ≤ Lam)
  (hF : IsAdmissibleCoefficient lam Lam F) (hh : 0 < h) (hm : m ≠ 0)
  (hk : KernelConsts Φ h C1 C2 Cfi) (hq : 1 < q)
  (hR : ∀ y, smoothDensity Φ h m y ≤ R) (hCfi : 0 ≤ Cfi)

include hh hm hq hR in
theorem target_rpow_le (y : EvolutionAmbientState d) :
    smoothDensity Φ h m y ^ q ≤ R ^ (q - 1) * smoothWeight2 Φ h m y := by
  have hr := smoothDensity_pos Φ m hh hm y
  obtain ⟨h1, h2, h3, -⟩ := rpow_density_aux hr (hR y) hq
  rw [h3]
  exact mul_le_mul h1 (smoothDensity_le_smoothWeight2 (Φ := Φ) m hh y) hr.le
    ((Real.rpow_nonneg hr.le _).trans h1)

include hh hm hq hR hlam hLam' hF in
theorem target_rpow_frobenius_le (y : EvolutionAmbientState d) :
    smoothDensity Φ h m y ^ q * frobeniusSq (smoothCoefficient Φ h F m y) ≤
      d * Lam ^ 2 * (R ^ (q - 1) * smoothWeight2 Φ h m y) := by
  have h1 := target_rpow_le m hh hm hq hR y
  have h2 := frobeniusSq_smoothCoefficient_le Φ m hlam hLam' hF hh y
  have hr := smoothDensity_pos Φ m hh hm y
  calc _ ≤ smoothDensity Φ h m y ^ q * (d * Lam ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hr.le _)
    _ ≤ (R ^ (q - 1) * smoothWeight2 Φ h m y) * (d * Lam ^ 2) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = _ := by ring

include hh hm hq hR hk in
theorem target_gradNorm_le (y : EvolutionAmbientState d) :
    smoothDensity Φ h m y ^ (q - 1) * gradNorm (smoothDensity Φ h m) y ≤
      R ^ (q - 1) * ((2 * d + 1) * (|C1| * smoothWeight2 Φ h m y)) := by
  have hr := smoothDensity_pos Φ m hh hm y
  obtain ⟨h1, h2, -, -⟩ := rpow_density_aux hr (hR y) hq
  have h3 := gradNorm_smoothWeighted_le m (f := fun _ => 1) (Cf := 1) hh measurable_const
    (fun _ => by simp) hk y
  rw [← smoothDensity_eq] at h3
  simp only [one_mul] at h3
  exact mul_le_mul h1 h3 (Real.sqrt_nonneg _) ((Real.rpow_nonneg hr.le _).trans h1)

include hh hm hq hR hk in
theorem target_hessNorm_le (y : EvolutionAmbientState d) :
    smoothDensity Φ h m y ^ (q - 1) * hessNorm (smoothDensity Φ h m) y ≤
      R ^ (q - 1) * (((2 * d) ^ 2 + 1) * (|C2| * smoothWeight2 Φ h m y)) := by
  have hr := smoothDensity_pos Φ m hh hm y
  obtain ⟨h1, h2, -, -⟩ := rpow_density_aux hr (hR y) hq
  have h3 := hessNorm_smoothWeighted_le m (f := fun _ => 1) (Cf := 1) hh measurable_const
    (fun _ => by simp) hk y
  rw [← smoothDensity_eq] at h3
  simp only [one_mul] at h3
  exact mul_le_mul h1 h3 (Real.sqrt_nonneg _) ((Real.rpow_nonneg hr.le _).trans h1)

include hh hm hq hR hk in
theorem target_fisher_le (y : EvolutionAmbientState d) :
    smoothDensity Φ h m y ^ (q - 2) * gradNormSq (smoothDensity Φ h m) y ≤
      R ^ (q - 1) * (Cfi * smoothWeight2 Φ h m y) := by
  have hr := smoothDensity_pos Φ m hh hm y
  obtain ⟨h1, h2, -, h4⟩ := rpow_density_aux hr (hR y) hq
  have hD := gradNormSq_smoothWeighted_le (Φ := Φ) (h := h) m hh (f := fun _ => 1)
    measurable_const (Cf := 1) (fun _ => by simp) y
  rw [← smoothDensity_eq] at hD
  have hFi := fisherSmooth_le m hh hk y
  have hFi0 := fisherSmooth_nonneg (Φ := Φ) (h := h) m hh y
  calc _ ≤ smoothDensity Φ h m y ^ (q - 2) * (smoothDensity Φ h m y * fisherSmooth Φ h m y) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hr.le _)
        nlinarith
    _ = smoothDensity Φ h m y ^ (q - 1) * fisherSmooth Φ h m y := by rw [← h4]; ring
    _ ≤ R ^ (q - 1) * (Cfi * smoothWeight2 Φ h m y) :=
        mul_le_mul h1 hFi hFi0 ((Real.rpow_nonneg hr.le _).trans h1)

include hh hm hq hR hk hlam hF in
theorem target_coefficientGradNorm_le (y : EvolutionAmbientState d) :
    smoothDensity Φ h m y ^ q * coefficientGradNorm (smoothCoefficient Φ h F m) y ≤
      R ^ (q - 1) * ((1 + 4 * d ^ 2 * Lam ^ 2 * Cfi) / 2 * smoothWeight2 Φ h m y) := by
  have hr := smoothDensity_pos Φ m hh hm y
  obtain ⟨h1, h2, h3, -⟩ := rpow_density_aux hr (hR y) hq
  set r := smoothDensity Φ h m y with hrdef
  set G := coefficientGradNormSq (smoothCoefficient Φ h F m) y with hG
  have hG0 : 0 ≤ G := coefficientGradNormSq_nonneg _ _
  have hrG := density_mul_coefficientGradNormSq_le Φ m hlam hF hh hm y
  rw [← hrdef, ← hG] at hrG
  have hFi := fisherSmooth_le m hh hk y
  have hFi0 := fisherSmooth_nonneg (Φ := Φ) (h := h) m hh y
  set c : ℝ := 4 * d ^ 2 * Lam ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have hsq : r * √G ≤ (r + c * fisherSmooth Φ h m y) / 2 := by
    refine (sq_le_sq₀ (by positivity) (by positivity)).1 ?_
    have : (r * √G) ^ 2 = r * (r * G) := by
      rw [mul_pow, Real.sq_sqrt hG0]; ring
    rw [this]
    nlinarith [sq_nonneg (r - c * fisherSmooth Φ h m y), mul_le_mul_of_nonneg_left hrG hr.le]
  have hsw := smoothDensity_le_smoothWeight2 (Φ := Φ) m hh y
  have hS := smoothWeight2_nonneg (Φ := Φ) m hh y
  calc r ^ q * coefficientGradNorm (smoothCoefficient Φ h F m) y = r ^ (q - 1) * (r * √G) := by
        rw [h3]; unfold coefficientGradNorm; rw [← hG]; ring
    _ ≤ R ^ (q - 1) * ((r + c * fisherSmooth Φ h m y) / 2) :=
        mul_le_mul h1 hsq (by positivity) ((Real.rpow_nonneg hr.le _).trans h1)
    _ ≤ R ^ (q - 1) * ((1 + 4 * d ^ 2 * Lam ^ 2 * Cfi) / 2 * smoothWeight2 Φ h m y) := by
        refine mul_le_mul_of_nonneg_left ?_ ((Real.rpow_nonneg hr.le _).trans h1)
        have : c * fisherSmooth Φ h m y ≤ c * (Cfi * smoothWeight2 Φ h m y) :=
          mul_le_mul_of_nonneg_left hFi hc0
        nlinarith

include hh hm hq hR hk hlam hLam' hF in
theorem target_fluxGradNorm_le (y : EvolutionAmbientState d) :
    smoothDensity Φ h m y ^ (q - 1) * coefficientGradNorm (smoothFlux Φ h F m) y ≤
      R ^ (q - 1) * ((d ^ 2 * (2 * d) + 1) * (Lam * |C1| * smoothWeight2 Φ h m y)) := by
  have hr := smoothDensity_pos Φ m hh hm y
  obtain ⟨h1, h2, -, -⟩ := rpow_density_aux hr (hR y) hq
  exact mul_le_mul h1 (coefficientGradNorm_smoothFlux_le m hlam hLam' hF hh hk y)
    (Real.sqrt_nonneg _) ((Real.rpow_nonneg hr.le _).trans h1)

include hh hm hq hR hk hlam hLam' hF in
theorem target_fluxHessNorm_le (y : EvolutionAmbientState d) :
    smoothDensity Φ h m y ^ (q - 1) * coefficientHessNorm (smoothFlux Φ h F m) y ≤
      R ^ (q - 1) * ((d ^ 2 * (2 * d) ^ 2 + 1) * (Lam * |C2| * smoothWeight2 Φ h m y)) := by
  have hr := smoothDensity_pos Φ m hh hm y
  obtain ⟨h1, h2, -, -⟩ := rpow_density_aux hr (hR y) hq
  exact mul_le_mul h1 (coefficientHessNorm_smoothFlux_le m hlam hLam' hF hh hk y)
    (Real.sqrt_nonneg _) ((Real.rpow_nonneg hr.le _).trans h1)

theorem coefficientGradNormSq_smoothFlux_le (hlam : 0 < lam)
    (hF : IsAdmissibleCoefficient lam Lam F)
    (hh : 0 < h) (y : EvolutionAmbientState d) :
    coefficientGradNormSq (smoothFlux Φ h F m) y ≤
      d ^ 2 * Lam ^ 2 * (smoothDensity Φ h m y * fisherSmooth Φ h m y) := by
  unfold coefficientGradNormSq
  calc ∑ i, ∑ j, gradNormSq (fun y => smoothFlux Φ h F m y i j) y
      ≤ ∑ _i : Fin d, ∑ _j : Fin d, Lam ^ 2 * (smoothDensity Φ h m y * fisherSmooth Φ h m y) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        have : (fun y => smoothFlux Φ h F m y i j) = smoothWeighted Φ h (fun a => F a i j) m := by
          rw [← smoothFluxEntry_eq]; rfl
        rw [this]
        have := gradNormSq_smoothWeighted_le (Φ := Φ) (h := h) m hh (hF.measurable i j)
          (fun a => hF.abs_apply_le hlam a i j) y
        calc _ ≤ _ := this
          _ = _ := by ring
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

include hh hm hq hR hk hlam hF in
theorem target_fluxFisher_le (y : EvolutionAmbientState d) :
    smoothDensity Φ h m y ^ (q - 2) * coefficientGradNormSq (smoothFlux Φ h F m) y ≤
      R ^ (q - 1) * (d ^ 2 * Lam ^ 2 * Cfi * smoothWeight2 Φ h m y) := by
  have hr := smoothDensity_pos Φ m hh hm y
  obtain ⟨h1, h2, -, h4⟩ := rpow_density_aux hr (hR y) hq
  have h5 := coefficientGradNormSq_smoothFlux_le (Φ := Φ) m hlam hF hh y
  have hFi := fisherSmooth_le m hh hk y
  have hFi0 := fisherSmooth_nonneg (Φ := Φ) (h := h) m hh y
  calc _ ≤ smoothDensity Φ h m y ^ (q - 2) *
        (d ^ 2 * Lam ^ 2 * (smoothDensity Φ h m y * fisherSmooth Φ h m y)) :=
        mul_le_mul_of_nonneg_left h5 (Real.rpow_nonneg hr.le _)
    _ = d ^ 2 * Lam ^ 2 * (smoothDensity Φ h m y ^ (q - 1) * fisherSmooth Φ h m y) := by
        rw [← h4]; ring
    _ ≤ d ^ 2 * Lam ^ 2 * (R ^ (q - 1) * (Cfi * smoothWeight2 Φ h m y)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul h1 hFi hFi0
          ((Real.rpow_nonneg hr.le _).trans h1)) (by positivity)
    _ = _ := by ring

include hh hm hq hR hk hlam hLam' hF in
theorem target_mixed_le (y : EvolutionAmbientState d) :
    smoothDensity Φ h m y ^ (q - 1) * gradNorm (smoothDensity Φ h m) y *
        coefficientGradNorm (smoothCoefficient Φ h F m) y ≤
      R ^ (q - 1) * (2 * d * Lam * Cfi * smoothWeight2 Φ h m y) := by
  have hr := smoothDensity_pos Φ m hh hm y
  obtain ⟨h1, h2, -, -⟩ := rpow_density_aux hr (hR y) hq
  set r := smoothDensity Φ h m y with hrdef
  have hLam : 0 ≤ Lam := (hlam.trans_le hLam').le
  have hrG := density_mul_coefficientGradNormSq_le Φ m hlam hF hh hm y
  have hD := gradNormSq_smoothDensity_div_le Φ m hh hm y
  have hD' : gradNormSq (smoothDensity Φ h m) y ≤ r * fisherSmooth Φ h m y := by
    rwa [div_le_iff₀ hr, mul_comm] at hD
  have hFi := fisherSmooth_le m hh hk y
  have hFi0 := fisherSmooth_nonneg (Φ := Φ) (h := h) m hh y
  have hG0 := coefficientGradNormSq_nonneg (smoothCoefficient Φ h F m) y
  have hD0 := gradNormSq_nonneg (smoothDensity Φ h m) y
  set G := coefficientGradNormSq (smoothCoefficient Φ h F m) y
  set D := gradNormSq (smoothDensity Φ h m) y
  have hprod : gradNorm (smoothDensity Φ h m) y * coefficientGradNorm (smoothCoefficient Φ h F m) y
      ≤ 2 * d * Lam * fisherSmooth Φ h m y := by
    have : gradNorm (smoothDensity Φ h m) y * coefficientGradNorm (smoothCoefficient Φ h F m) y =
        √(D * G) := by
      unfold gradNorm coefficientGradNorm; rw [← Real.sqrt_mul hD0]
    rw [this, Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have e1 : D * G ≤ (r * fisherSmooth Φ h m y) * G := mul_le_mul_of_nonneg_right hD' hG0
    have e2 : (r * fisherSmooth Φ h m y) * G = fisherSmooth Φ h m y * (r * G) := by ring
    have e3 : fisherSmooth Φ h m y * (r * G) ≤ fisherSmooth Φ h m y *
        (4 * d ^ 2 * Lam ^ 2 * fisherSmooth Φ h m y) := mul_le_mul_of_nonneg_left hrG hFi0
    nlinarith
  calc r ^ (q - 1) * gradNorm (smoothDensity Φ h m) y *
        coefficientGradNorm (smoothCoefficient Φ h F m) y
      = r ^ (q - 1) * (gradNorm (smoothDensity Φ h m) y *
        coefficientGradNorm (smoothCoefficient Φ h F m) y) := by ring
    _ ≤ R ^ (q - 1) * (2 * d * Lam * fisherSmooth Φ h m y) :=
        mul_le_mul h1 hprod (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
          ((Real.rpow_nonneg hr.le _).trans h1)
    _ ≤ R ^ (q - 1) * (2 * d * Lam * (Cfi * smoothWeight2 Φ h m y)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hFi (by positivity))
          ((Real.rpow_nonneg hr.le _).trans h1)
    _ = _ := by ring

end Pointwise

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

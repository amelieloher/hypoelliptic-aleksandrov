module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Norms

/-!
# Gradient and Hessian norms of smoothed measures bounded by `smoothWeight2`

Combines `DerivBounds` with the sum-of-squares estimates of `Norms`: the norms `|D (fm)_h|`,
`|D² (fm)_h|`, and the matrix norms of the smoothed flux, are bounded by explicit constants times
`smoothWeight2`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ} {lam Lam : ℝ} {Φ : SmoothingKernelFamily d lam} {h : ℝ}
  {f : EvolutionAmbientState d → ℝ} {Cf : ℝ}
  {F : EvolutionAmbientState d → PDE.Mat d}
  (m : Measure (EvolutionAmbientState d)) [IsFiniteMeasure m]

/-- The kernel constants of the Gaussian flow estimates at one parameter `h`, as used in the
smoothing estimates. -/
structure KernelConsts (Φ : SmoothingKernelFamily d lam) (h C1 C2 Cfi : ℝ) : Prop where
  c1 : ∀ z, ‖iteratedFDeriv ℝ 1 (Φ.kernel h) z‖ ≤ C1 * (1 + ‖z‖) ^ 1 * Φ.kernel h z
  c2 : ∀ z, ‖iteratedFDeriv ℝ 2 (Φ.kernel h) z‖ ≤ C2 * (1 + ‖z‖) ^ 2 * Φ.kernel h z
  fisher : ∀ z, fisherKernel Φ h z ≤ Cfi * weight2 Φ h z

/-- The kernel constants can be chosen uniformly on a compact subset of `(0, ∞)`. -/
theorem exists_kernelConsts {K : Set ℝ} (hK : IsCompact K) (hsub : K ⊆ Set.Ioi 0) :
    ∃ C1 C2 Cfi : ℝ, 0 ≤ Cfi ∧ ∀ h ∈ K, KernelConsts Φ h C1 C2 Cfi := by
  obtain ⟨C1, hC1⟩ := Φ.deriv_bound 1 hK hsub
  obtain ⟨C2, hC2⟩ := Φ.deriv_bound 2 hK hsub
  obtain ⟨Cfi, hCfi0, hCfi⟩ := exists_fisherKernel_le (Φ := Φ) hK hsub
  exact ⟨C1, C2, Cfi, hCfi0, fun h hh => ⟨hC1 h hh, hC2 h hh, hCfi h hh⟩⟩

theorem gradNorm_smoothWeighted_le {C1 C2 Cfi : ℝ} (hh : 0 < h) (hf : Measurable f)
    (hfb : ∀ a, |f a| ≤ Cf) (hk : KernelConsts Φ h C1 C2 Cfi) (y : EvolutionAmbientState d) :
    gradNorm (smoothWeighted Φ h f m) y ≤ (2 * d + 1) * (Cf * |C1| * smoothWeight2 Φ h m y) := by
  have hCf : 0 ≤ Cf := (abs_nonneg _).trans (hfb 0)
  have hB : 0 ≤ Cf * |C1| * smoothWeight2 Φ h m y :=
    mul_nonneg (mul_nonneg hCf (abs_nonneg _)) (smoothWeight2_nonneg m hh y)
  exact sqrt_le_mul_succ (by positivity) hB
    (gradNormSq_le_of_forall fun c => abs_coordPartial_smoothWeighted_le m hh hf hfb hk.c1 c y)

theorem hessNorm_smoothWeighted_le {C1 C2 Cfi : ℝ} (hh : 0 < h) (hf : Measurable f)
    (hfb : ∀ a, |f a| ≤ Cf) (hk : KernelConsts Φ h C1 C2 Cfi) (y : EvolutionAmbientState d) :
    hessNorm (smoothWeighted Φ h f m) y ≤
      ((2 * d) ^ 2 + 1) * (Cf * |C2| * smoothWeight2 Φ h m y) := by
  have hCf : 0 ≤ Cf := (abs_nonneg _).trans (hfb 0)
  have hB : 0 ≤ Cf * |C2| * smoothWeight2 Φ h m y :=
    mul_nonneg (mul_nonneg hCf (abs_nonneg _)) (smoothWeight2_nonneg m hh y)
  exact sqrt_le_mul_succ (by positivity) hB
    (hessNormSq_le_of_forall fun c c' =>
      abs_coordPartial₂_smoothWeighted_le m hh hf hfb hk.c2 c c' y)

theorem coefficientGradNorm_smoothFlux_le {C1 C2 Cfi : ℝ} (hlam : 0 < lam) (hLam' : lam ≤ Lam)
    (hF : IsAdmissibleCoefficient lam Lam F) (hh : 0 < h) (hk : KernelConsts Φ h C1 C2 Cfi)
    (y : EvolutionAmbientState d) :
    coefficientGradNorm (smoothFlux Φ h F m) y ≤
      (d ^ 2 * (2 * d) + 1) * (Lam * |C1| * smoothWeight2 Φ h m y) := by
  have hLam : 0 ≤ Lam := (hlam.trans_le hLam').le
  have hB : 0 ≤ Lam * |C1| * smoothWeight2 Φ h m y :=
    mul_nonneg (mul_nonneg hLam (abs_nonneg _)) (smoothWeight2_nonneg m hh y)
  refine sqrt_le_mul_succ (by positivity) hB ?_
  unfold coefficientGradNormSq
  calc ∑ i, ∑ j, gradNormSq (fun y => smoothFlux Φ h F m y i j) y
      ≤ ∑ _i : Fin d, ∑ _j : Fin d, (2 * d) * (Lam * |C1| * smoothWeight2 Φ h m y) ^ 2 := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        have : (fun y => smoothFlux Φ h F m y i j) = smoothWeighted Φ h (fun a => F a i j) m := by
          rw [← smoothFluxEntry_eq]; rfl
        rw [this]
        exact gradNormSq_le_of_forall fun c => abs_coordPartial_smoothWeighted_le m hh
          (hF.measurable i j) (fun a => hF.abs_apply_le hlam a i j) hk.c1 c y
    _ = d ^ 2 * (2 * d) * (Lam * |C1| * smoothWeight2 Φ h m y) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem coefficientHessNorm_smoothFlux_le {C1 C2 Cfi : ℝ} (hlam : 0 < lam) (hLam' : lam ≤ Lam)
    (hF : IsAdmissibleCoefficient lam Lam F) (hh : 0 < h) (hk : KernelConsts Φ h C1 C2 Cfi)
    (y : EvolutionAmbientState d) :
    coefficientHessNorm (smoothFlux Φ h F m) y ≤
      (d ^ 2 * (2 * d) ^ 2 + 1) * (Lam * |C2| * smoothWeight2 Φ h m y) := by
  have hLam : 0 ≤ Lam := (hlam.trans_le hLam').le
  have hB : 0 ≤ Lam * |C2| * smoothWeight2 Φ h m y :=
    mul_nonneg (mul_nonneg hLam (abs_nonneg _)) (smoothWeight2_nonneg m hh y)
  refine sqrt_le_mul_succ (by positivity) hB ?_
  unfold coefficientHessNormSq
  calc ∑ i, ∑ j, hessNormSq (fun y => smoothFlux Φ h F m y i j) y
      ≤ ∑ _i : Fin d, ∑ _j : Fin d, (2 * d) ^ 2 * (Lam * |C2| * smoothWeight2 Φ h m y) ^ 2 := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        have : (fun y => smoothFlux Φ h F m y i j) = smoothWeighted Φ h (fun a => F a i j) m := by
          rw [← smoothFluxEntry_eq]; rfl
        rw [this]
        exact hessNormSq_le_of_forall fun c c' => abs_coordPartial₂_smoothWeighted_le m hh
          (hF.measurable i j) (fun a => hF.abs_apply_le hlam a i j) hk.c2 c c' y
    _ = d ^ 2 * (2 * d) ^ 2 * (Lam * |C2| * smoothWeight2 Φ h m y) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem fisherSmooth_le {C1 C2 Cfi : ℝ} (hh : 0 < h) (hk : KernelConsts Φ h C1 C2 Cfi)
    (y : EvolutionAmbientState d) :
    fisherSmooth Φ h m y ≤ Cfi * smoothWeight2 Φ h m y := by
  unfold fisherSmooth smoothWeight2
  rw [← integral_const_mul]
  exact integral_mono (integrable_fisherKernel_translate m hh y)
    ((integrable_weight2_translate m hh y).const_mul _) fun a => hk.fisher _

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

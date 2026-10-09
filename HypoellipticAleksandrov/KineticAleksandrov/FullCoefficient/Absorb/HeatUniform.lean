module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.HeatDominator

/-!
# A dominator for the heat operator, uniform in the measure

The time-integrated identities: for the integration in the slice time `τ`, the
bound of `exists_heat_dominator` has to be uniform over the family of slice measures. The proof is
the same; the dominating function is `y ↦ ∫ G (y - a) dm(a)` with a single `G`, and the sup bound is
`Cs * m.real univ`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ} {lam : ℝ} (Φ : SmoothingKernelFamily d lam)

theorem exists_heat_dominator_uniform {K : Set ℝ} (hK : IsCompact K) (hsub : K ⊆ Set.Ioi 0) :
    ∃ (G : EvolutionAmbientState d → ℝ) (A Cs : ℝ), Continuous G ∧ Integrable G ∧
      (∀ y, 0 ≤ G y) ∧ 0 ≤ A ∧ 0 ≤ Cs ∧
      ∀ (m : Measure (EvolutionAmbientState d)) [IsFiniteMeasure m], ∀ h ∈ K,
        (∀ y, smoothDensity Φ h m y ≤ Cs * m.real Set.univ) ∧
        ∀ (f : EvolutionAmbientState d → ℝ) (Cf : ℝ), Measurable f → (∀ a, |f a| ≤ Cf) →
          ∀ y, |heatOperator lam h (smoothWeighted Φ h f m) y| ≤
            Cf * A * ∫ a, G (y - a) ∂m := by
  obtain ⟨C1, C2, Cfi, hCfi, hk⟩ := exists_kernelConsts (Φ := Φ) hK hsub
  obtain ⟨Cs, hCs0, hCs⟩ := Φ.exists_sup_bound hK hsub
  obtain ⟨G, B, hGc, hGi, hGb, hGdom⟩ := Φ.weight_dom 2 hK hsub
  obtain ⟨b, hb⟩ := hK.bddAbove
  set b' : ℝ := max b 0 with hb'
  set Hc : ℝ := |lam| / 2 * (2 * b' ^ 2 * d + 2 * b' * d + d) with hHc
  have hHc0 : 0 ≤ Hc := by positivity
  set A : ℝ := Hc * |C2| with hA
  refine ⟨G, A, Cs, hGc, hGi, fun y => (hGb y).1, by positivity, hCs0, ?_⟩
  intro m _ h hhK
  have hGint : ∀ y : EvolutionAmbientState d, Integrable (fun a => G (y - a)) m := fun y =>
    Integrable.of_bound (C := B)
      ((hGc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun a => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hGb _).1]; exact (hGb _).2)
  have hh : 0 < h := hsub hhK
  have hhb : h ≤ b' := (hb hhK).trans (le_max_left _ _)
  refine ⟨fun y => (smoothDensity_le_of_kernel_le Φ hh (fun z => hCs h hhK z) m y), ?_⟩
  intro f Cf hf hfb y
  have hCf : 0 ≤ Cf := (abs_nonneg _).trans (hfb 0)
  have hH : heatOperator lam h (smoothWeighted Φ h f m) y =
      ∫ a, f a * heatOperator lam h (Φ.kernel h) (y - a) ∂m := by
    change heatOperator lam h (wconv (Φ.kernel h) f m) y = _
    rw [heatOperator_wconv (Φ.isBoundedSmooth hh) hf hfb]
    simp [wconv]
  rw [hH]
  have hpt : ∀ a, ‖f a * heatOperator lam h (Φ.kernel h) (y - a)‖ ≤ Cf * A * G (y - a) := by
    intro a
    have h1 := abs_heatOperator_le (lam := lam) (Φ.contDiff hh) h (y - a)
    have h2 : ‖iteratedFDeriv ℝ 2 (Φ.kernel h) (y - a)‖ ≤ |C2| * G (y - a) := by
      refine (hk h hhK).c2 (y - a) |>.trans ?_
      have hp := Φ.pos hh (y - a)
      calc C2 * (1 + ‖y - a‖) ^ 2 * Φ.kernel h (y - a)
          ≤ |C2| * ((1 + ‖y - a‖) ^ 2 * Φ.kernel h (y - a)) := by
            rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ ≤ |C2| * G (y - a) := mul_le_mul_of_nonneg_left (hGdom h hhK _) (abs_nonneg _)
    have hcoef : |lam| / 2 * (2 * h ^ 2 * d + 2 * |h| * d + d) ≤ Hc := by
      rw [hHc, abs_of_pos hh]
      have : h ^ 2 ≤ b' ^ 2 := pow_le_pow_left₀ hh.le hhb 2
      gcongr
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |f a| * |heatOperator lam h (Φ.kernel h) (y - a)|
        ≤ Cf * (Hc * (|C2| * G (y - a))) :=
          mul_le_mul (hfb a) (h1.trans (mul_le_mul hcoef h2 (norm_nonneg _) hHc0))
            (abs_nonneg _) hCf
      _ = Cf * A * G (y - a) := by rw [hA]; ring
  have := norm_integral_le_of_norm_le ((hGint y).const_mul (Cf * A))
    (Filter.Eventually.of_forall hpt)
  rw [integral_const_mul] at this
  simpa [Real.norm_eq_abs] using this

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

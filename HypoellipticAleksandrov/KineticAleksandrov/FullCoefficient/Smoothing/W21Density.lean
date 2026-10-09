module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.W21Basic

/-!
# `r^q` is a smooth `W^{2,1}` function

The smoothing estimates: for `m ≠ 0`, `D(r^q) = q r^{q-1} Dr` and
`D²(r^q) = q(q-1) r^{q-2} Dr ⊗ Dr + q r^{q-1} D²r`, so the integrability of
`r^q, r^{q-1}|Dr|, r^{q-1}|D²r|, r^{q-2}|Dr|²` gives `r^q ∈ W^{2,1}`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ} {lam : ℝ} {Φ : SmoothingKernelFamily d lam} {h q : ℝ}
  {m : Measure (EvolutionAmbientState d)}

theorem smoothW21_rpow_density [IsFiniteMeasure m] (hh : 0 < h) (hm : m ≠ 0)
    (hI0 : Integrable (integrandPow Φ h m q)) (hIg : Integrable (integrandGrad Φ h m q))
    (hIh : Integrable (integrandHess Φ h m q)) (hIf : Integrable (integrandFisher Φ h m q)) :
    SmoothW21 (fun y => smoothDensity Φ h m y ^ q) := by
  have hu : ContDiff ℝ (⊤ : ℕ∞) (smoothDensity Φ h m) := contDiff_smoothDensity Φ m hh
  have hpos : ∀ y, 0 < smoothDensity Φ h m y := smoothDensity_pos Φ m hh hm
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun y => smoothDensity Φ h m y ^ q) :=
    contDiff_rpow_of_pos hu hpos q
  have e1 : (fun y => smoothDensity Φ h m y ^ q) =
      fun y => smoothDensity Φ h m y ^ q * (fun _ : EvolutionAmbientState d => (1 : ℝ)) y := by
    funext y; simp
  have hw : ContDiff ℝ (⊤ : ℕ∞) (fun _ : EvolutionAmbientState d => (1 : ℝ)) := contDiff_const
  refine ⟨hg, hI0, fun c => ?_, fun c c' => ?_⟩
  · have hc := coordPartial_rpow_mul hu hw hpos q c
    rw [e1, hc]
    refine ((hIg.const_mul |q|)).mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
    · rw [← hc, ← e1]; exact (continuous_coordPartial hg c).aestronglyMeasurable
    · simp only [coordPartial_const_apply, mul_zero, add_zero, mul_one, Real.norm_eq_abs]
      have h1 := abs_coordPartial_le_gradNorm (smoothDensity Φ h m) y c
      have h2 : 0 ≤ smoothDensity Φ h m y ^ (q - 1) := Real.rpow_nonneg (hpos y).le _
      calc |q * smoothDensity Φ h m y ^ (q - 1) * coordPartial c (smoothDensity Φ h m) y|
          = |q| * (smoothDensity Φ h m y ^ (q - 1) * |coordPartial c (smoothDensity Φ h m) y|) := by
            simp only [abs_mul, abs_of_nonneg h2]; ring
        _ ≤ |q| * integrandGrad Φ h m q y := by
            unfold integrandGrad; gcongr
  · have hc2 : coordPartial c' (coordPartial c (fun y => smoothDensity Φ h m y ^ q)) =
        fun y => q * (q - 1) * smoothDensity Φ h m y ^ (q - 2) *
          coordPartial c' (smoothDensity Φ h m) y * coordPartial c (smoothDensity Φ h m) y +
          q * smoothDensity Φ h m y ^ (q - 1) *
            coordPartial c' (coordPartial c (smoothDensity Φ h m)) y := by
      funext y
      rw [e1, coordPartial₂_rpow_mul hu hw hpos q c c' y]
      have z1 : coordPartial c (fun _ : EvolutionAmbientState d => (1 : ℝ)) = fun _ => 0 :=
        coordPartial_const c 1
      simp only [z1, coordPartial_const_apply, mul_zero, add_zero, mul_one]
    rw [hc2]
    refine ((hIf.const_mul |q * (q - 1)|).add (hIh.const_mul |q|)).mono' ?_
      (Filter.Eventually.of_forall fun y => ?_)
    · rw [← hc2]
      exact (continuous_coordPartial (contDiff_coordPartial hg c) c').aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      have h1 := second_bound_rpow (s := q) (P1 := smoothDensity Φ h m y ^ (q - 1))
        (P2 := smoothDensity Φ h m y ^ (q - 2)) (Real.rpow_nonneg (hpos y).le _)
        (Real.rpow_nonneg (hpos y).le _)
        (sq_coordPartial_le_gradNormSq (smoothDensity Φ h m) y c)
        (sq_coordPartial_le_gradNormSq (smoothDensity Φ h m) y c')
        (abs_coordPartial₂_le_hessNorm (smoothDensity Φ h m) y c' c)
      refine h1.trans (le_of_eq ?_)
      simp only [integrandFisher, integrandHess, Pi.add_apply]

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

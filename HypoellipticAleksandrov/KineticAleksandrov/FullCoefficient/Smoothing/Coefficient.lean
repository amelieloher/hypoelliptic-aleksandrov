module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Bounds

/-!
# The smoothed coefficient `β_h`

The smoothing estimates, matrix part: `β = (Fm)_h / m_h` is symmetric,
`λ I ≤ β ≤ Λ I` and `|β|² ≤ d Λ²`, because `β(y)` is an average of values of `F`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory Matrix
open scoped MatrixOrder

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ} {lam Lam : ℝ} (Φ : SmoothingKernelFamily d lam) {h : ℝ}
  {F : EvolutionAmbientState d → PDE.Mat d}
  (m : Measure (EvolutionAmbientState d))

namespace IsAdmissibleCoefficient

theorem abs_apply_le (hlam : 0 < lam) (hF : IsAdmissibleCoefficient lam Lam F)
    (y : EvolutionAmbientState d) (i j : Fin d) : |F y i j| ≤ Lam :=
  HypoellipticAleksandrov.abs_apply_le_of_loewner hlam (hF.lower y) (hF.upper y) i j

end IsAdmissibleCoefficient

variable [IsFiniteMeasure m]

theorem integrable_flux_integrand (hlam : 0 < lam) (hF : IsAdmissibleCoefficient lam Lam F)
    (hh : 0 < h) (i j : Fin d) (y : EvolutionAmbientState d) :
    Integrable (fun a => Φ.kernel h (y - a) * F a i j) m := by
  obtain ⟨C, hC⟩ := (Φ.isBoundedSmooth hh).bound_zero
  have := integrable_weighted_translate (Φ.isBoundedSmooth hh).contDiff.continuous
    (hF.measurable i j) (fun a => hF.abs_apply_le hlam a i j) hC m y
  refine this.congr (Filter.Eventually.of_forall fun a => ?_)
  simp [mul_comm]

/-- The quadratic form of the smoothed flux is the smoothing of the quadratic form of `F`. -/
theorem dotProduct_smoothFlux_mulVec (hlam : 0 < lam) (hF : IsAdmissibleCoefficient lam Lam F)
    (hh : 0 < h) (y : EvolutionAmbientState d) (x : PDE.Vec d) :
    x ⬝ᵥ (smoothFlux Φ h F m y *ᵥ x) =
      ∫ a, Φ.kernel h (y - a) * (x ⬝ᵥ (F a *ᵥ x)) ∂m := by
  have hint : ∀ i j, Integrable (fun a => x i * x j * (Φ.kernel h (y - a) * F a i j)) m :=
    fun i j => (integrable_flux_integrand Φ m hlam hF hh i j y).const_mul _
  have hpt : ∀ a, Φ.kernel h (y - a) * (x ⬝ᵥ (F a *ᵥ x)) =
      ∑ i, ∑ j, x i * x j * (Φ.kernel h (y - a) * F a i j) := fun a => by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  simp only [hpt]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  simp only [dotProduct, Matrix.mulVec, smoothFlux, smoothFluxEntry, Matrix.of_apply,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]
  ring

omit [IsFiniteMeasure m] in
theorem isSymm_smoothFlux (hF : IsAdmissibleCoefficient lam Lam F) (y : EvolutionAmbientState d) :
    (smoothFlux Φ h F m y).IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  show ∫ a, Φ.kernel h (y - a) * F a j i ∂m = ∫ a, Φ.kernel h (y - a) * F a i j ∂m
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp only
  rw [(hF.symm a).apply i j]

theorem smoothFlux_quadratic_bounds (hlam : 0 < lam) (hF : IsAdmissibleCoefficient lam Lam F)
    (hh : 0 < h) (y : EvolutionAmbientState d) (x : PDE.Vec d) :
    lam * (x ⬝ᵥ x) * smoothDensity Φ h m y ≤ x ⬝ᵥ (smoothFlux Φ h F m y *ᵥ x) ∧
      x ⬝ᵥ (smoothFlux Φ h F m y *ᵥ x) ≤ Lam * (x ⬝ᵥ x) * smoothDensity Φ h m y := by
  rw [dotProduct_smoothFlux_mulVec Φ m hlam hF hh]
  have hr := integrable_kernel_translate Φ m hh y
  have hq : Integrable (fun a => Φ.kernel h (y - a) * (x ⬝ᵥ (F a *ᵥ x))) m := by
    have h1 : ∀ a, Φ.kernel h (y - a) * (x ⬝ᵥ (F a *ᵥ x)) =
        ∑ i, ∑ j, x i * x j * (Φ.kernel h (y - a) * F a i j) := fun a => by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    simp only [h1]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (integrable_flux_integrand Φ m hlam hF hh i j y).const_mul _
  constructor
  · calc lam * (x ⬝ᵥ x) * smoothDensity Φ h m y
        = ∫ a, lam * (x ⬝ᵥ x) * Φ.kernel h (y - a) ∂m := by
          rw [smoothDensity, integral_const_mul]
      _ ≤ _ := integral_mono (hr.const_mul _) hq fun a => by
          have := le_quadraticForm_of_smul_one_le (hF.lower a) x
          have hp := Φ.pos hh (y - a)
          nlinarith
  · calc ∫ a, Φ.kernel h (y - a) * (x ⬝ᵥ (F a *ᵥ x)) ∂m
        ≤ ∫ a, Lam * (x ⬝ᵥ x) * Φ.kernel h (y - a) ∂m :=
          integral_mono hq (hr.const_mul _) fun a => by
            have := quadraticForm_le_of_le_smul_one (hF.upper a) x
            have hp := Φ.pos hh (y - a)
            nlinarith
      _ = _ := by rw [smoothDensity, integral_const_mul]

omit [IsFiniteMeasure m] in
theorem smoothCoefficient_of_ne_zero (hm : m ≠ 0) (y : EvolutionAmbientState d) :
    smoothCoefficient Φ h F m y = (smoothDensity Φ h m y)⁻¹ • smoothFlux Φ h F m y := by
  simp [smoothCoefficient, hm]

omit [IsFiniteMeasure m] in
theorem smoothCoefficient_of_eq_zero (y : EvolutionAmbientState d) :
    smoothCoefficient Φ h F (0 : Measure (EvolutionAmbientState d)) y =
      lam • (1 : PDE.Mat d) := by
  simp [smoothCoefficient]

theorem isSymm_smoothCoefficient (hF : IsAdmissibleCoefficient lam Lam F)
    (y : EvolutionAmbientState d) : (smoothCoefficient Φ h F m y).IsSymm := by
  by_cases hm : m = 0
  · subst hm
    rw [smoothCoefficient_of_eq_zero]
    exact (Matrix.isSymm_one).smul _
  · rw [smoothCoefficient_of_ne_zero Φ m hm]
    exact (isSymm_smoothFlux Φ m hF y).smul _

/-- Two-sided Loewner bounds for `β`: `λ I ≤ β ≤ Λ I`. -/
theorem smoothCoefficient_loewner (hlam : 0 < lam) (hF : IsAdmissibleCoefficient lam Lam F)
    (hh : 0 < h) (y : EvolutionAmbientState d) :
    lam • (1 : PDE.Mat d) ≤ smoothCoefficient Φ h F m y ∧
      smoothCoefficient Φ h F m y ≤ Lam • (1 : PDE.Mat d) := by
  by_cases hm : m = 0
  · subst hm
    rw [smoothCoefficient_of_eq_zero]
    exact ⟨le_rfl, (hF.lower y).trans (hF.upper y)⟩
  · have hr := smoothDensity_pos Φ m hh hm y
    have hsymm := isSymm_smoothCoefficient Φ m hF (h := h) y
    rw [smoothCoefficient_of_ne_zero Φ m hm] at hsymm ⊢
    have hq : ∀ x : PDE.Vec d,
        x ⬝ᵥ (((smoothDensity Φ h m y)⁻¹ • smoothFlux Φ h F m y) *ᵥ x) =
          (smoothDensity Φ h m y)⁻¹ * (x ⬝ᵥ (smoothFlux Φ h F m y *ᵥ x)) := fun x => by
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    constructor
    · refine HypoellipticAleksandrov.loewner_lower_of_quadraticForm hsymm fun x => ?_
      have := (smoothFlux_quadratic_bounds Φ m hlam hF hh y x).1
      rw [PDE.vecNormSq, PDE.vecDot]
      change lam * (x ⬝ᵥ x) ≤ x ⬝ᵥ (((smoothDensity Φ h m y)⁻¹ • smoothFlux Φ h F m y) *ᵥ x)
      rw [hq, ← div_eq_inv_mul, le_div_iff₀ hr]
      linarith
    · refine le_smul_one_of_quadraticForm hsymm fun x => ?_
      have := (smoothFlux_quadratic_bounds Φ m hlam hF hh y x).2
      rw [hq, ← div_eq_inv_mul, div_le_iff₀ hr]
      linarith

theorem abs_smoothCoefficient_le (hlam : 0 < lam) (hF : IsAdmissibleCoefficient lam Lam F)
    (hh : 0 < h) (y : EvolutionAmbientState d) (i j : Fin d) :
    |smoothCoefficient Φ h F m y i j| ≤ Lam := by
  obtain ⟨h1, h2⟩ := smoothCoefficient_loewner Φ m hlam hF hh y
  exact HypoellipticAleksandrov.abs_apply_le_of_loewner hlam h1 h2 i j

/-- The bound `|β|² ≤ d Λ²` (squared Frobenius norm). -/
theorem frobeniusSq_smoothCoefficient_le (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hF : IsAdmissibleCoefficient lam Lam F) (hh : 0 < h) (y : EvolutionAmbientState d) :
    frobeniusSq (smoothCoefficient Φ h F m y) ≤ d * Lam ^ 2 := by
  obtain ⟨h1, h2⟩ := smoothCoefficient_loewner Φ m hlam hF hh y
  exact frobeniusSq_le (hlam.trans_le hLam)
    (HypoellipticAleksandrov.posDef_of_loewner_lower hlam h1).posSemidef h2

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

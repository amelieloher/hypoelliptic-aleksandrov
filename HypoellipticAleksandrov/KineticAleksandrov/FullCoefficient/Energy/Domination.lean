module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Energy.Pointwise
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Energy.IBP

/-!
# Domination lemmas for the integrations by parts of the energy inequality

Coordinate partials are bounded by the Euclidean gradient and Hessian norms, and the integrands
of the integrations by parts are dominated by the integrands of the smoothing estimates.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

theorem sq_gradNorm (F : EvolutionAmbientState d → ℝ) (y : EvolutionAmbientState d) :
    gradNorm F y ^ 2 = gradNormSq F y :=
  Real.sq_sqrt (gradNormSq_nonneg F y)

theorem sq_coefficientGradNorm (B : EvolutionAmbientState d → PDE.Mat d)
    (y : EvolutionAmbientState d) : coefficientGradNorm B y ^ 2 = coefficientGradNormSq B y :=
  Real.sq_sqrt (coefficientGradNormSq_nonneg B y)

theorem gradNorm_nonneg (F : EvolutionAmbientState d → ℝ) (y : EvolutionAmbientState d) :
    0 ≤ gradNorm F y := Real.sqrt_nonneg _

theorem hessNorm_nonneg (F : EvolutionAmbientState d → ℝ) (y : EvolutionAmbientState d) :
    0 ≤ hessNorm F y := Real.sqrt_nonneg _

theorem coefficientGradNorm_nonneg (B : EvolutionAmbientState d → PDE.Mat d)
    (y : EvolutionAmbientState d) : 0 ≤ coefficientGradNorm B y := Real.sqrt_nonneg _

theorem coefficientHessNorm_nonneg (B : EvolutionAmbientState d → PDE.Mat d)
    (y : EvolutionAmbientState d) : 0 ≤ coefficientHessNorm B y := Real.sqrt_nonneg _

theorem energy_abs_coordPartial_le_gradNorm (c : Fin d ⊕ Fin d) (F : EvolutionAmbientState d → ℝ)
    (y : EvolutionAmbientState d) : |coordPartial c F y| ≤ gradNorm F y :=
  Real.abs_le_sqrt (Finset.single_le_sum (f := fun c => coordPartial c F y ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ c))

theorem energy_abs_coordPartial₂_le_hessNorm (c c' : Fin d ⊕ Fin d)
    (F : EvolutionAmbientState d → ℝ)
    (y : EvolutionAmbientState d) : |coordPartial c (coordPartial c' F) y| ≤ hessNorm F y := by
  refine Real.abs_le_sqrt ?_
  unfold hessNormSq
  refine le_trans ?_ (Finset.single_le_sum (f := fun c => ∑ c', coordPartial c
    (coordPartial c' F) y ^ 2) (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (Finset.mem_univ c))
  exact Finset.single_le_sum (f := fun c' => coordPartial c (coordPartial c' F) y ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ c')

theorem abs_coordPartial_coeff_le (c : Fin d ⊕ Fin d) (B : EvolutionAmbientState d → PDE.Mat d)
    (i j : Fin d) (y : EvolutionAmbientState d) :
    |coordPartial c (fun y => B y i j) y| ≤ coefficientGradNorm B y := by
  refine (energy_abs_coordPartial_le_gradNorm c _ y).trans ?_
  unfold gradNorm coefficientGradNorm
  refine Real.sqrt_le_sqrt ?_
  unfold coefficientGradNormSq
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, gradNormSq (fun y => B y i j) y)
    (fun _ _ => Finset.sum_nonneg fun _ _ => gradNormSq_nonneg _ _) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j => gradNormSq (fun y => B y i j) y)
    (fun _ _ => gradNormSq_nonneg _ _) (Finset.mem_univ j)

theorem abs_coordPartial₂_coeff_le (c c' : Fin d ⊕ Fin d) (B : EvolutionAmbientState d → PDE.Mat d)
    (i j : Fin d) (y : EvolutionAmbientState d) :
    |coordPartial c (coordPartial c' (fun y => B y i j)) y| ≤ coefficientHessNorm B y := by
  refine (energy_abs_coordPartial₂_le_hessNorm c c' _ y).trans ?_
  unfold hessNorm coefficientHessNorm
  refine Real.sqrt_le_sqrt ?_
  unfold coefficientHessNormSq
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, hessNormSq (fun y => B y i j) y)
    (fun _ _ => Finset.sum_nonneg fun _ _ => hessNormSq_nonneg _ _) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j => hessNormSq (fun y => B y i j) y)
    (fun _ _ => hessNormSq_nonneg _ _) (Finset.mem_univ j)

theorem integrable_of_abs_le {f g : EvolutionAmbientState d → ℝ} {K : ℝ}
    (hf : AEStronglyMeasurable f volume) (hg : Integrable g) (h : ∀ y, |f y| ≤ K * g y) :
    Integrable f :=
  (hg.const_mul K).mono' hf (Filter.Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs]; exact h y)

theorem integrable_cutoff_mul {ζ f : EvolutionAmbientState d → ℝ} {A : ℝ} (hζ : Continuous ζ)
    (hA : ∀ y, |ζ y| ≤ A) (hf : Integrable f) : Integrable fun y => ζ y * f y :=
  (hf.norm.const_mul A).mono' (hζ.aestronglyMeasurable.mul hf.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun y => by
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hA y) (norm_nonneg _))

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

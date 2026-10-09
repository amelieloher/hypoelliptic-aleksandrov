module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.PackageProof
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.RpowCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.W21Algebra

/-!
# Smooth functions with integrable derivatives up to order two

`SmoothW21 g` records that `g` is smooth and that `g`, its coordinate partials and its second
coordinate partials are all integrable. For a smooth function this implies membership in the
Sobolev space `W^{2,1}(ℝ^{2d})` with the classical derivatives as weak derivatives. This is the
form in which the integrability list of the smoothing estimates is used. The module also
proves closure under finite sums and the comparison of the coordinate partials with the Euclidean
gradient and Hessian norms.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

/-- A smooth function on phase space whose value, coordinate partials and second coordinate
partials are integrable (the classical form of membership in `W^{2,1}`). -/
def SmoothW21 (g : EvolutionAmbientState d → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) g ∧ Integrable g ∧ (∀ c, Integrable (coordPartial c g)) ∧
    ∀ c c', Integrable (coordPartial c' (coordPartial c g))

theorem coordPartial_finsetSum {ι : Type*} (s : Finset ι) {f : ι → EvolutionAmbientState d → ℝ}
    (hf : ∀ i ∈ s, ContDiff ℝ (⊤ : ℕ∞) (f i)) (c : Fin d ⊕ Fin d) :
    coordPartial c (fun y => ∑ i ∈ s, f i y) = fun y => ∑ i ∈ s, coordPartial c (f i) y := by
  funext y
  unfold coordPartial
  have hd : ∀ i ∈ s, DifferentiableAt ℝ (f i) y := fun i hi => (hf i hi).differentiable (by simp) y
  have e : (fun y => ∑ i ∈ s, f i y) = ∑ i ∈ s, f i := by
    funext y; simp
  rw [e, fderiv_sum hd]
  simp

theorem SmoothW21.sum {ι : Type*} (s : Finset ι) {f : ι → EvolutionAmbientState d → ℝ}
    (hf : ∀ i ∈ s, SmoothW21 (f i)) : SmoothW21 (fun y => ∑ i ∈ s, f i y) := by
  have hs : ∀ i ∈ s, ContDiff ℝ (⊤ : ℕ∞) (f i) := fun i hi => (hf i hi).1
  have hc1 : ∀ c, ∀ i ∈ s, ContDiff ℝ (⊤ : ℕ∞) (coordPartial c (f i)) :=
    fun c i hi => contDiff_coordPartial (hs i hi) c
  refine ⟨ContDiff.sum hs, integrable_finsetSum _ fun i hi => (hf i hi).2.1, fun c => ?_,
    fun c c' => ?_⟩
  · rw [coordPartial_finsetSum s hs c]
    exact integrable_finsetSum _ fun i hi => (hf i hi).2.2.1 c
  · rw [coordPartial_finsetSum s hs c, coordPartial_finsetSum s (hc1 c) c']
    exact integrable_finsetSum _ fun i hi => (hf i hi).2.2.2 c c'

theorem sq_coordPartial_le_gradNormSq (F : EvolutionAmbientState d → ℝ)
    (y : EvolutionAmbientState d) (c : Fin d ⊕ Fin d) :
    coordPartial c F y ^ 2 ≤ gradNormSq F y :=
  Finset.single_le_sum (f := fun c => coordPartial c F y ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ c)

theorem sq_coordPartial₂_le_hessNormSq (F : EvolutionAmbientState d → ℝ)
    (y : EvolutionAmbientState d) (c c' : Fin d ⊕ Fin d) :
    coordPartial c (coordPartial c' F) y ^ 2 ≤ hessNormSq F y := by
  unfold hessNormSq
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun c => ∑ c', coordPartial c (coordPartial c' F) y ^ 2)
    (fun c _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ c))
  exact Finset.single_le_sum (f := fun c' => coordPartial c (coordPartial c' F) y ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ c')

theorem abs_coordPartial_le_gradNorm (F : EvolutionAmbientState d → ℝ)
    (y : EvolutionAmbientState d) (c : Fin d ⊕ Fin d) :
    |coordPartial c F y| ≤ gradNorm F y :=
  Real.abs_le_sqrt (sq_coordPartial_le_gradNormSq F y c)

theorem abs_coordPartial₂_le_hessNorm (F : EvolutionAmbientState d → ℝ)
    (y : EvolutionAmbientState d) (c c' : Fin d ⊕ Fin d) :
    |coordPartial c (coordPartial c' F) y| ≤ hessNorm F y :=
  Real.abs_le_sqrt (sq_coordPartial₂_le_hessNormSq F y c c')

theorem sq_coordPartial_entry_le (B : EvolutionAmbientState d → PDE.Mat d)
    (y : EvolutionAmbientState d) (i j : Fin d) (c : Fin d ⊕ Fin d) :
    coordPartial c (fun y => B y i j) y ^ 2 ≤ coefficientGradNormSq B y := by
  unfold coefficientGradNormSq
  refine le_trans (sq_coordPartial_le_gradNormSq (fun y => B y i j) y c) ?_
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, gradNormSq (fun y => B y i j) y)
    (fun _ _ => Finset.sum_nonneg fun _ _ => gradNormSq_nonneg _ _) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j => gradNormSq (fun y => B y i j) y)
    (fun _ _ => gradNormSq_nonneg _ _) (Finset.mem_univ j)

theorem abs_coordPartial₂_entry_le (B : EvolutionAmbientState d → PDE.Mat d)
    (y : EvolutionAmbientState d) (i j : Fin d) (c c' : Fin d ⊕ Fin d) :
    |coordPartial c (coordPartial c' (fun y => B y i j)) y| ≤ coefficientHessNorm B y := by
  refine Real.abs_le_sqrt ?_
  unfold coefficientHessNormSq
  refine le_trans (sq_coordPartial₂_le_hessNormSq (fun y => B y i j) y c c') ?_
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, hessNormSq (fun y => B y i j) y)
    (fun _ _ => Finset.sum_nonneg fun _ _ => hessNormSq_nonneg _ _) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j => hessNormSq (fun y => B y i j) y)
    (fun _ _ => hessNormSq_nonneg _ _) (Finset.mem_univ j)

theorem abs_coordPartial_entry_le (B : EvolutionAmbientState d → PDE.Mat d)
    (y : EvolutionAmbientState d) (i j : Fin d) (c : Fin d ⊕ Fin d) :
    |coordPartial c (fun y => B y i j) y| ≤ coefficientGradNorm B y :=
  Real.abs_le_sqrt (sq_coordPartial_entry_le B y i j c)

theorem coordPartial_const_apply (c : Fin d ⊕ Fin d) (a : ℝ) (y : EvolutionAmbientState d) :
    coordPartial c (fun _ : EvolutionAmbientState d => a) y = 0 := by
  simp [coordPartial]

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

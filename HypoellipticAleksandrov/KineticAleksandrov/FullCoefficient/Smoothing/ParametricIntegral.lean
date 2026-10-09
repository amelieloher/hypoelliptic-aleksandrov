module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Smooth dependence of weighted convolutions with finite measures

For a finite measure `m` on a normed space `E`, a bounded measurable weight `f : E → ℝ` and a
function `G : E → F` all of whose derivatives are bounded, the weighted convolution
`y ↦ ∫ f a • G (y - a) ∂m` is smooth and its Fréchet derivative is the weighted convolution of
`fderiv G`. This is the analytic content of the smoothness of the smoothed
functions: differentiation under the integral sign in the space variable.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

universe u

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `G` is smooth with every derivative bounded. -/
structure IsBoundedSmooth {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] (G : E → F) :
    Prop where
  contDiff : ContDiff ℝ (⊤ : ℕ∞) G
  bounded : ∀ k : ℕ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ k G x‖ ≤ C

variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem IsBoundedSmooth.fderiv {G : E → F} (hG : IsBoundedSmooth G) :
    IsBoundedSmooth (_root_.fderiv ℝ G) := by
  refine ⟨?_, fun k => ?_⟩
  · exact hG.contDiff.fderiv_right (by simp)
  · obtain ⟨C, hC⟩ := hG.bounded (k + 1)
    exact ⟨C, fun x => by rw [norm_iteratedFDeriv_fderiv]; exact hC x⟩

theorem IsBoundedSmooth.bound_zero {G : E → F} (hG : IsBoundedSmooth G) :
    ∃ C : ℝ, ∀ x, ‖G x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hG.bounded 0
  exact ⟨C, fun x => by simpa using hC x⟩

theorem IsBoundedSmooth.bound_one {G : E → F} (hG : IsBoundedSmooth G) :
    ∃ C : ℝ, ∀ x, ‖_root_.fderiv ℝ G x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hG.bounded 1
  exact ⟨C, fun x => by simpa using hC x⟩

theorem IsBoundedSmooth.apply_const {F' : Type} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {G : E → (E →L[ℝ] F')} (hG : IsBoundedSmooth G) (e : E) :
    IsBoundedSmooth (fun x => G x e) := by
  let L : (E →L[ℝ] F') →L[ℝ] F' := ContinuousLinearMap.apply ℝ F' e
  refine ⟨L.contDiff.comp hG.contDiff, fun k => ?_⟩
  obtain ⟨C, hC⟩ := hG.bounded k
  refine ⟨‖L‖ * C, fun x => ?_⟩
  have := L.norm_iteratedFDeriv_comp_left (f := G) (x := x) (n := k)
    hG.contDiff.contDiffAt (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))
  exact this.trans (mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _))


theorem hasFDerivAt_comp_sub {G : E → F} {x a : E} (h : DifferentiableAt ℝ G (x - a)) :
    HasFDerivAt (fun x => G (x - a)) (_root_.fderiv ℝ G (x - a)) x := by
  have := h.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const a)
  simpa [Function.comp_def] using this

section Measure

variable [MeasurableSpace E] [OpensMeasurableSpace E] [SecondCountableTopology E]

/-- The weighted convolution `y ↦ ∫ f a • G (y - a) ∂m`. -/
def wconv (G : E → F) (f : E → ℝ) (m : Measure E) (y : E) : F :=
  ∫ a, f a • G (y - a) ∂m

omit [NormedSpace ℝ E] in
theorem integrable_weighted_translate {G : E → F} (hG : Continuous G) {f : E → ℝ}
    (hf : Measurable f) {Cf CG : ℝ} (hfb : ∀ a, |f a| ≤ Cf) (hGb : ∀ x, ‖G x‖ ≤ CG)
    (m : Measure E) [IsFiniteMeasure m] (y : E) :
    Integrable (fun a => f a • G (y - a)) m := by
  refine Integrable.of_bound (C := Cf * CG) ?_ (Filter.Eventually.of_forall fun a => ?_)
  · exact hf.aestronglyMeasurable.smul
      ((hG.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hfb a) (hGb _) (norm_nonneg _) ((abs_nonneg _).trans (hfb a))

theorem hasFDerivAt_wconv {G : E → F} (hG : IsBoundedSmooth G) {f : E → ℝ} (hf : Measurable f)
    {Cf : ℝ} (hfb : ∀ a, |f a| ≤ Cf) (m : Measure E) [IsFiniteMeasure m] (y : E) :
    HasFDerivAt (wconv G f m) (wconv (_root_.fderiv ℝ G) f m y) y := by
  have hdiff : Differentiable ℝ G := hG.contDiff.differentiable (by simp)
  have hG' := hG.fderiv
  obtain ⟨C0, hC0⟩ := hG.bound_zero
  obtain ⟨C1, hC1⟩ := hG.bound_one
  have hGc : Continuous G := hG.contDiff.continuous
  have hG'c : Continuous (_root_.fderiv ℝ G) := hG'.contDiff.continuous
  have hmeas : ∀ x, AEStronglyMeasurable (fun a => f a • G (x - a)) m := fun x =>
    hf.aestronglyMeasurable.smul
      ((hGc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x a => f a • G (x - a))
    (F' := fun x a => f a • _root_.fderiv ℝ G (x - a)) (s := Set.univ) (x₀ := y)
    (bound := fun _ => Cf * C1) Filter.univ_mem
    (Filter.Eventually.of_forall hmeas)
    (integrable_weighted_translate hGc hf hfb hC0 m y)
    ?_ ?_ (integrable_const _) ?_
  · exact key
  · exact hf.aestronglyMeasurable.smul
      ((hG'c.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  · refine Filter.Eventually.of_forall fun a x _ => ?_
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hfb a) (hC1 _) (norm_nonneg _) ((abs_nonneg _).trans (hfb a))
  · refine Filter.Eventually.of_forall fun a x _ => ?_
    exact (hasFDerivAt_comp_sub (hdiff _)).const_smul (f a)

theorem fderiv_wconv {G : E → F} (hG : IsBoundedSmooth G) {f : E → ℝ} (hf : Measurable f)
    {Cf : ℝ} (hfb : ∀ a, |f a| ≤ Cf) (m : Measure E) [IsFiniteMeasure m] :
    _root_.fderiv ℝ (wconv G f m) = wconv (_root_.fderiv ℝ G) f m :=
  funext fun y => (hasFDerivAt_wconv hG hf hfb m y).fderiv

theorem differentiable_wconv {G : E → F} (hG : IsBoundedSmooth G) {f : E → ℝ}
    (hf : Measurable f) {Cf : ℝ} (hfb : ∀ a, |f a| ≤ Cf) (m : Measure E) [IsFiniteMeasure m] :
    Differentiable ℝ (wconv G f m) := fun y => (hasFDerivAt_wconv hG hf hfb m y).differentiableAt

theorem contDiff_wconv_nat {f : E → ℝ} (hf : Measurable f) {Cf : ℝ} (hfb : ∀ a, |f a| ≤ Cf)
    (m : Measure E) [IsFiniteMeasure m] (n : ℕ) :
    ∀ {F' : Type u} [NormedAddCommGroup F'] [NormedSpace ℝ F'] (G : E → F'),
      IsBoundedSmooth G → ContDiff ℝ n (wconv G f m) := by
  induction n with
  | zero =>
    intro F' _ _ G hG
    exact contDiff_zero.2 (differentiable_wconv hG hf hfb m).continuous
  | succ n ih =>
    intro F' _ _ G hG
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
    refine ⟨differentiable_wconv hG hf hfb m, by simp, ?_⟩
    rw [fderiv_wconv hG hf hfb m]
    exact ih _ hG.fderiv

/-- The weighted convolution of a bounded smooth function with a bounded measurable weight
against a finite measure is smooth. -/
theorem contDiff_wconv {G : E → F} (hG : IsBoundedSmooth G) {f : E → ℝ} (hf : Measurable f)
    {Cf : ℝ} (hfb : ∀ a, |f a| ≤ Cf) (m : Measure E) [IsFiniteMeasure m] :
    ContDiff ℝ (⊤ : ℕ∞) (wconv G f m) :=
  contDiff_infty.2 fun n => contDiff_wconv_nat hf hfb m n G hG

end Measure

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

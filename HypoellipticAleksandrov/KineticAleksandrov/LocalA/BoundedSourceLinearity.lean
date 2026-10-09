module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceApprox
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Literal bounded-source linearity and terminal truncation -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set Filter
variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/-- The actual source integral is additive for signed bounded Borel data. -/
theorem duhamelSourceIntegral_add_bounded (K : MovingFiberKernel Ω γ)
    (f g : KineticPoint d → ℝ) (hf : Measurable f) (hg : Measurable g)
    (M N : ℝ) (hfb : ∀ p, |f p| ≤ M) (hgb : ∀ p, |g p| ≤ N)
    (q : EvolutionQuery Ω γ) :
    duhamelSourceIntegral K (fun p => f p + g p) q =
      duhamelSourceIntegral K f q + duhamelSourceIntegral K g q := by
  have hm : Measurable (fun w : EvolutionAmbientState d =>
      (⟨q.1.2.1, w.1, w.2⟩ : KineticPoint d)) :=
    (KineticPoint.measurable_equivProd_symm d).comp
      (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))
  have hfi : Integrable (fun w : EvolutionAmbientState d => f ⟨q.1.2.1, w.1, w.2⟩)
      (K.master q) := ⟨(hf.comp hm).aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs]; exact hfb _)⟩
  have hgi : Integrable (fun w : EvolutionAmbientState d => g ⟨q.1.2.1, w.1, w.2⟩)
      (K.master q) := ⟨(hg.comp hm).aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs]; exact hgb _)⟩
  exact integral_add hfi hgi

/-- The zero-extended source integrand retains the same literal additivity. -/
theorem duhamelIntegrand_add_bounded (K : MovingFiberKernel Ω γ)
    (f g : KineticPoint d → ℝ) (hf : Measurable f) (hg : Measurable g)
    (M N : ℝ) (hfb : ∀ p, |f p| ≤ M) (hgb : ∀ p, |g p| ≤ N)
    (p : KineticPoint d) (r : ℝ) :
    duhamelIntegrand K (fun p => f p + g p) p r =
      duhamelIntegrand K f p r + duhamelIntegrand K g p r := by
  unfold duhamelIntegrand
  split
  · exact duhamelSourceIntegral_add_bounded K f g hf hg M N hfb hgb _
  · exact (zero_add 0).symm

/-- Finite-horizon potentials are additive for the actual signed bounded sources. -/
theorem duhamelPotential_add_bounded (K : MovingFiberKernel Ω γ)
    (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (f g : KineticPoint d → ℝ) (hf : Measurable f) (hg : Measurable g)
    (M N : ℝ) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hfb : ∀ p, |f p| ≤ M) (hgb : ∀ p, |g p| ≤ N)
    (T : ℝ) (p : KineticPoint d) :
    duhamelPotential K T (fun p => f p + g p) p =
      duhamelPotential K T f p + duhamelPotential K T g p := by
  unfold duhamelPotential
  simp_rw [duhamelIntegrand_add_bounded K f g hf hg M N hfb hgb]
  exact integral_add (integrableOn_duhamelIntegrand_bounded K hΩ hγ f hf M hM hfb p T)
    (integrableOn_duhamelIntegrand_bounded K hΩ hγ g hg N hN hgb p T)

/-- Negation is retained exactly by the master-kernel source integrand. -/
theorem duhamelIntegrand_neg (K : MovingFiberKernel Ω γ)
    (g : KineticPoint d → ℝ) (p : KineticPoint d) (r : ℝ) :
    duhamelIntegrand K (fun p => -g p) p r = -duhamelIntegrand K g p r := by
  unfold duhamelIntegrand
  split
  · exact integral_neg _
  · exact neg_zero.symm

/-- Negation is retained exactly by the literal finite-horizon potential. -/
theorem duhamelPotential_neg (K : MovingFiberKernel Ω γ)
    (g : KineticPoint d → ℝ) (T : ℝ) (p : KineticPoint d) :
    duhamelPotential K T (fun p => -g p) p = -duhamelPotential K T g p := by
  unfold duhamelPotential
  simp_rw [duhamelIntegrand_neg]
  exact integral_neg _

/-- A source that vanishes above a source time has zero integrand at that time. -/
theorem duhamelIntegrand_zero_above_source (K : MovingFiberKernel Ω γ)
    (g : KineticPoint d → ℝ) (s : ℝ) (hgz : ∀ p, s < p.time → g p = 0)
    (p : KineticPoint d) (r : ℝ) (hr : s < r) : duhamelIntegrand K g p r = 0 := by
  unfold duhamelIntegrand
  split
  · change (∫ w, g ⟨r, w.1, w.2⟩ ∂K.master _) = 0
    have hz (w : EvolutionAmbientState d) : g ⟨r, w.1, w.2⟩ = 0 :=
      hgz ⟨r, w.1, w.2⟩ hr
    simp_rw [hz]
    exact integral_zero _ _
  · rfl

/-- Removing terminal times above the source support does not change the actual potential. -/
theorem duhamelPotential_eq_short_terminal (K : MovingFiberKernel Ω γ)
    (g : KineticPoint d → ℝ) (s T : ℝ) (hsT : s ≤ T)
    (hgz : ∀ p, s < p.time → g p = 0) (p : KineticPoint d) :
    duhamelPotential K T g p = duhamelPotential K s g p := by
  unfold duhamelPotential
  apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioc.nullMeasurableSet
    (fun r hr => ⟨hr.1, hr.2.trans hsT⟩)
  exact Eventually.of_forall fun r hr => duhamelIntegrand_zero_above_source K g s hgz p r
    (lt_of_not_ge fun h => hr.2 ⟨hr.1.1, h⟩)

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

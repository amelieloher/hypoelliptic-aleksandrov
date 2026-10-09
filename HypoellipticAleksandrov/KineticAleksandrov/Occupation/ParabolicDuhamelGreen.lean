module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelSmooth
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The Duhamel potential as a Green integral

For a starting point `(s, v)` in `U₀` and any `z`, the parabolic Duhamel potential `W(s,v)` is the
integral of `g(s + τ, w₁)` against the Green measure `Γ` of the supplied evolution kernel from the
Dirac mass at `(v, z)` with horizon `T - s`: the Green identity of Lemma 2.3, carried to the
parabolic marginal, in absolute time.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Set Filter
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal ProbabilityTheory

/-- Integration over the elapsed-time carrier is Lebesgue integration over `(0, L)`. -/
theorem integral_elapsed_eq (L : ℝ) (hL : 0 < L) (f : ℝ → ℝ) (hf : Measurable f) :
    ∫ τ : ElapsedTime (ENNReal.ofReal L), f τ.1 ∂elapsedVolume (ENNReal.ofReal L) =
      ∫ x in Ioo 0 L, f x := by
  have h1 := integral_map (μ := elapsedVolume (ENNReal.ofReal L))
    (φ := (Subtype.val : ElapsedTime (ENNReal.ofReal L) → ℝ))
    measurable_subtype_coe.aemeasurable (f := f) hf.aestronglyMeasurable
  have h2 : (elapsedVolume (ENNReal.ofReal L)).map
      (Subtype.val : ElapsedTime (ENNReal.ofReal L) → ℝ) = volume.restrict (Ioo 0 L) := by
    have he : {τ : ℝ | 0 < τ ∧ ENNReal.ofReal τ < ENNReal.ofReal L} = Ioo 0 L := by
      ext τ
      simp only [mem_ofPred_eq, mem_Ioo, ENNReal.ofReal_lt_ofReal_iff hL]
    exact (map_comap_subtype_coe (measurableSet_elapsedTime (ENNReal.ofReal L)) volume).trans
      (by rw [he])
  rw [← h1, h2]

/-- A translation of the elapsed-time interval. -/
theorem integral_Ioo_shift (f : ℝ → ℝ) (s L : ℝ) (hL : 0 ≤ L) :
    ∫ x in Ioo 0 L, f (s + x) = ∫ r in Ioc s (s + L), f r := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hL,
    intervalIntegral.integral_comp_add_left f s, intervalIntegral.integral_of_le (by linarith)]
  simp

variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
variable (K : MovingFiberKernel Ω γ)

/-- **Green identity** for the parabolic Duhamel potential, in absolute time. -/
theorem parabolic_duhamel_green {B : CoefficientField d}
    (hΩa : IsAdmissibleEvolutionDomain Ω)
    (hP : HasParabolicMarginalBundle Ω γ
      (measurableSet_of_isAdmissibleEvolutionDomain hΩa) (zIndependentCoefficient B) K)
    (T : ℝ) (g : TimeVelocity d → ℝ) (hg0 : ∀ p, 0 ≤ g p) (hgs : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) (hγ : Continuous γ)
    (s : ℝ) (v : PDE.Vec d) (hv : (s, v) ∈ duhamelFiber Ω γ T) (z : PDE.Vec d)
    (Γ : Measure (ElapsedTime (ENNReal.ofReal (T - s)) × EvolutionAmbientState d))
    (hΓ : IsGreenMeasure K s (ENNReal.ofReal (T - s))
      (Measure.dirac (evolutionStateOfPosition Ω γ s ⟨v, hv.2⟩ z)) Γ) :
    parabolicDuhamelPotential K (measurableSet_of_isAdmissibleEvolutionDomain hΩa) T g (s, v) =
      ∫ q, g (s + q.1.1, q.2.1) ∂Γ := by
  have hΩm := measurableSet_of_isAdmissibleEvolutionDomain hΩa
  have hgm : Measurable g := hgs.continuous.measurable
  have hg : ∀ r, Measurable (fun v : PDE.Vec d => g (r, v)) := fun r =>
    hgm.comp (measurable_const.prodMk measurable_id)
  obtain ⟨C, hC⟩ := hgs.continuous.bounded_above_of_compact_support hgc
  have hgb : ∀ p, g p ≤ C := fun p => (le_abs_self _).trans (by simpa using hC p)
  obtain ⟨Q, h1, -, -, -, -, -, -, -, -, -⟩ := hP (fun _ _ _ _ => rfl)
  have hLpos : 0 < T - s := sub_pos.2 hv.1
  let y : EvolutionPosition Ω γ s := ⟨v, hv.2⟩
  let p0 := evolutionStateOfPosition Ω γ s y z
  let F : ElapsedTime (ENNReal.ofReal (T - s)) × EvolutionAmbientState d → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (g (s + q.1.1, q.2.1))
  have hFm : Measurable (fun q : ElapsedTime (ENNReal.ofReal (T - s)) × EvolutionAmbientState d =>
      g (s + q.1.1, q.2.1)) :=
    hgm.comp ((measurable_const.add (measurable_subtype_coe.comp measurable_fst)).prodMk
      (measurable_fst.comp measurable_snd))
  have hF : Measurable F := ENNReal.measurable_ofReal.comp hFm
  have hΓF := hΓ F hF
  rw [lintegral_dirac] at hΓF
  have hin : ∀ τ : ElapsedTime (ENNReal.ofReal (T - s)),
      ∫⁻ w, F (τ, w) ∂K.master (elapsedQuery s p0 τ) =
        ENNReal.ofReal (parabolicDuhamelIntegrand K hΩm g (s, v) (s + τ.1)) := by
    intro τ
    have hsr : s ≤ s + τ.1 := le_add_of_nonneg_right τ.2.1.le
    have hint : Integrable (fun w : EvolutionAmbientState d => g (s + τ.1, w.1))
        (K.master (elapsedQuery s p0 τ)) := by
      refine Integrable.mono' (integrable_const (max C 0)) (hg _ |>.comp measurable_fst
        |>.aestronglyMeasurable) (Eventually.of_forall fun w => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hg0 _)]
      exact (hgb _).trans (le_max_left _ _)
    have h2 : ∫⁻ w, F (τ, w) ∂K.master (elapsedQuery s p0 τ) =
        ENNReal.ofReal (∫ w, g (s + τ.1, w.1) ∂K.master (elapsedQuery s p0 τ)) :=
      (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun w => hg0 _)).symm
    rw [h2]
    congr 1
    have h3 := parabolicSourceIntegral_eq_master_of_state K hΩm g s (s + τ.1) hsr y z
      (h1 s (s + τ.1) hsr y z) (hg _)
    rw [parabolicDuhamelIntegrand_of_valid K hΩm g (s, v) (s + τ.1) ⟨hsr, hv.2⟩]
    exact h3.symm
  have hfm : Measurable (fun x : ℝ => parabolicDuhamelIntegrand K hΩm g (s, v) (s + x)) := by
    have := measurable_parabolicDuhamelIntegrand K hΩm hγ g hgm
    exact this.comp (measurable_const.prodMk (measurable_const.add measurable_id))
  have hfin : IsFiniteMeasure (elapsedVolume (ENNReal.ofReal (T - s))) :=
    ⟨by rw [elapsedVolume_univ _ hLpos]; exact ENNReal.ofReal_lt_top⟩
  have hnn : ∀ x, 0 ≤ parabolicDuhamelIntegrand K hΩm g (s, v) (s + x) := fun x =>
    parabolicDuhamelIntegrand_nonneg K hΩm g hg hg0 _ _
  have hfi : Integrable (fun τ : ElapsedTime (ENNReal.ofReal (T - s)) =>
      parabolicDuhamelIntegrand K hΩm g (s, v) (s + τ.1))
      (elapsedVolume (ENNReal.ofReal (T - s))) := by
    refine Integrable.mono' (integrable_const (max C 0))
      (hfm.comp measurable_subtype_coe).aestronglyMeasurable (Eventually.of_forall fun τ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn _)]
    exact (parabolicDuhamelIntegrand_le K hΩm g hg hg0 C hgb _ _).trans (le_max_left _ _)
  have hlint : ∫⁻ q, F q ∂Γ = ENNReal.ofReal
      (parabolicDuhamelPotential K hΩm T g (s, v)) := by
    rw [hΓF, lintegral_congr hin]
    rw [← ofReal_integral_eq_lintegral_ofReal hfi (Eventually.of_forall fun τ => hnn τ.1)]
    congr 1
    rw [integral_elapsed_eq (T - s) hLpos _ hfm, integral_Ioo_shift (fun r =>
      parabolicDuhamelIntegrand K hΩm g (s, v) r) s (T - s) hLpos.le]
    unfold parabolicDuhamelPotential
    simp
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun q => hg0 _)
    hFm.aestronglyMeasurable]
  change _ = (∫⁻ q, F q ∂Γ).toReal
  rw [hlint, ENNReal.toReal_ofReal (parabolicDuhamelPotential_nonneg K hΩm T g hg hg0 _)]

end HypoellipticAleksandrov.KineticAleksandrov.Occupation

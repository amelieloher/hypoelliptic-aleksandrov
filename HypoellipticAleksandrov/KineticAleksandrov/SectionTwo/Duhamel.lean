module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Green
public import HypoellipticAleksandrov.Geometry.KineticPointMeasure
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-! # Absolute-time Duhamel integrals without default evolution queries -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set
open scoped ENNReal ProbabilityTheory

/-- Integrate a source at the terminal time of a valid evolution query. -/
def duhamelSourceIntegral {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
    (K : MovingFiberKernel Ω γ) (g : KineticPoint d → ℝ)
    (q : EvolutionQuery Ω γ) : ℝ :=
  ∫ w, g ⟨q.1.2.1, w.1, w.2⟩ ∂K.master q

/-- The source-time integrand is zero outside the valid starting fiber. -/
def duhamelIntegrand {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
    (K : MovingFiberKernel Ω γ) (g : KineticPoint d → ℝ)
    (p : KineticPoint d) (r : ℝ) : ℝ := by
  classical
  exact if h : p.time ≤ r ∧ p.position ∈ movingDomain Ω γ p.time then
    duhamelSourceIntegral K g
      ⟨(p.time, (r, (p.position, p.velocity))), h.1, h.2, mem_univ _⟩
  else 0

/-- The Duhamel potential is the absolute-time source integral, extended by zero off the fiber. -/
def duhamelPotential {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
    (K : MovingFiberKernel Ω γ) (τplus : ℝ) (g : KineticPoint d → ℝ)
    (p : KineticPoint d) : ℝ :=
  ∫ r in Set.Ioc p.time τplus, duhamelIntegrand K g p r

/-- Nonnegative sources have nonnegative kernel integrals. -/
theorem duhamelSourceIntegral_nonneg {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ) (g : KineticPoint d → ℝ)
    (hgn : ∀ p, 0 ≤ g p) (q : EvolutionQuery Ω γ) :
    0 ≤ duhamelSourceIntegral K g q :=
  integral_nonneg (fun w => hgn ⟨q.1.2.1, w.1, w.2⟩)

/-- Contraction bounds each nonnegative source-time kernel integral. -/
theorem duhamelSourceIntegral_le {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ) (g : KineticPoint d → ℝ)
    (hgn : ∀ p, 0 ≤ g p) (C : ℝ) (hC : 0 ≤ C) (hgb : ∀ p, g p ≤ C)
    (q : EvolutionQuery Ω γ) : duhamelSourceIntegral K g q ≤ C := by
  have hn : ‖duhamelSourceIntegral K g q‖ ≤ C * (K.master q).real univ := by
    apply norm_integral_le_of_norm_le_const
    exact Filter.Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hgn _)]
      exact hgb _
  have hm : (K.master q).real univ ≤ 1 := by
    simpa only [Measure.real, ENNReal.toReal_one] using
      ENNReal.toReal_mono ENNReal.one_ne_top (K.mass_le_one q)
  rw [Real.norm_eq_abs] at hn
  exact (le_abs_self _).trans (hn.trans (by nlinarith))

/-- The valid-branch source-time integrand is nonnegative. -/
theorem duhamelIntegrand_nonneg {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ) (g : KineticPoint d → ℝ)
    (hgn : ∀ p, 0 ≤ g p) (p : KineticPoint d) (r : ℝ) :
    0 ≤ duhamelIntegrand K g p r := by
  unfold duhamelIntegrand
  split
  · exact duhamelSourceIntegral_nonneg K g hgn _
  · exact le_rfl

/-- Contraction also bounds the integrand on its zero branch. -/
theorem duhamelIntegrand_le {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ) (g : KineticPoint d → ℝ)
    (hgn : ∀ p, 0 ≤ g p) (C : ℝ) (hC : 0 ≤ C) (hgb : ∀ p, g p ≤ C)
    (p : KineticPoint d) (r : ℝ) : duhamelIntegrand K g p r ≤ C := by
  unfold duhamelIntegrand
  split
  · exact duhamelSourceIntegral_le K g hgn C hC hgb _
  · exact hC

/-- Query-dependent integration of a measurable source is Borel. -/
theorem measurable_duhamelSourceIntegral {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ) (g : KineticPoint d → ℝ)
    (hg : Measurable g) : Measurable (duhamelSourceIntegral K g) := by
  have hm : Measurable (fun q : EvolutionQuery Ω γ × EvolutionAmbientState d =>
      g ⟨q.1.1.2.1, q.2.1, q.2.2⟩) := by
    have ht : Measurable (fun q : EvolutionQuery Ω γ × EvolutionAmbientState d =>
        q.1.1.2.1) := measurable_subtype_coe.snd.fst.comp measurable_fst
    convert hg.comp ((KineticPoint.measurable_equivProd_symm d).comp
      (ht.prodMk (measurable_snd.fst.prodMk measurable_snd.snd))) using 1
    rfl
  exact (hm.stronglyMeasurable.integral_kernel_prod_right' (κ := K.master)).measurable

/-- Joint Borel dependence of the source-time integrand uses no default kernel query. -/
theorem measurable_duhamelIntegrand {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω)
    (hγ : Continuous γ) (g : KineticPoint d → ℝ) (hg : Measurable g) :
    Measurable (fun q : KineticPoint d × ℝ => duhamelIntegrand K g q.1 q.2) := by
  classical
  let D : Set (KineticPoint d × ℝ) :=
    {q | q.1.time ≤ q.2 ∧ q.1.position ∈ movingDomain Ω γ q.1.time}
  have hD : MeasurableSet D := by
    have ht : MeasurableSet {q : KineticPoint d × ℝ | q.1.time ≤ q.2} :=
      measurableSet_le (continuous_time.measurable.comp measurable_fst) measurable_snd
    have hp : MeasurableSet {q : KineticPoint d × ℝ | q.1.position - γ q.1.time ∈ Ω} :=
      hΩ.preimage
      ((continuous_position.measurable.comp measurable_fst).sub
        (hγ.measurable.comp (continuous_time.measurable.comp measurable_fst)))
    convert ht.inter hp using 1
    ext q
    simp only [D, mem_ofPred_eq, mem_inter_iff]
    change (_ ∧ _ ∈ PDE.translateSet (γ q.1.time) Ω) ↔ _
    rw [PDE.mem_translateSet_iff_sub_mem]
  let Q : D → EvolutionQuery Ω γ := fun q =>
    ⟨(q.1.1.time, (q.1.2, (q.1.1.position, q.1.1.velocity))),
      q.2.1, q.2.2, mem_univ _⟩
  have hQ : Measurable Q := by
    apply Measurable.subtype_mk
    change Measurable (fun q : D =>
      (q.1.1.time, (q.1.2, (q.1.1.position, q.1.1.velocity))))
    exact (continuous_time.measurable.comp measurable_subtype_coe.fst).prodMk
      (measurable_subtype_coe.snd.prodMk
        ((continuous_position.measurable.comp measurable_subtype_coe.fst).prodMk
          (continuous_velocity.measurable.comp measurable_subtype_coe.fst)))
  exact ((measurable_duhamelSourceIntegral K g hg).comp hQ).dite measurable_const hD

/-- The absolute-time Duhamel potential is Borel for every measurable source. -/
theorem measurable_duhamelPotential {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω)
    (hγ : Continuous γ) (τplus : ℝ) (g : KineticPoint d → ℝ) (hg : Measurable g) :
    Measurable (duhamelPotential K τplus g) := by
  let D : Set (KineticPoint d × ℝ) := {q | q.1.time < q.2 ∧ q.2 ≤ τplus}
  have hD : MeasurableSet D :=
    (measurableSet_lt (continuous_time.measurable.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)
  have hi := ((measurable_duhamelIntegrand K hΩ hγ g hg).indicator hD).stronglyMeasurable
  convert (hi.integral_prod_right' (ν := (volume : Measure ℝ))).measurable using 1
  funext p
  rw [duhamelPotential, ← integral_indicator measurableSet_Ioc]
  rfl

/-- Nonnegative bounded sources satisfy the advertised finite-horizon Duhamel estimate. -/
theorem duhamelPotential_nonneg_le {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ) (τplus : ℝ)
    (g : KineticPoint d → ℝ) (hgn : ∀ p, 0 ≤ g p)
    (C : ℝ) (hC : 0 ≤ C) (hgb : ∀ p, g p ≤ C)
    (p : KineticPoint d) (hp : p.time ≤ τplus) :
    0 ≤ duhamelPotential K τplus g p ∧
      duhamelPotential K τplus g p ≤ (τplus - p.time) * C := by
  have hnon : 0 ≤ duhamelPotential K τplus g p :=
    integral_nonneg (fun r => duhamelIntegrand_nonneg K g hgn p r)
  refine ⟨hnon, ?_⟩
  have hn := norm_integral_le_of_norm_le_const
    (μ := volume.restrict (Ioc p.time τplus)) (f := duhamelIntegrand K g p)
    (C := C) (Filter.Eventually.of_forall fun r => by
      rw [Real.norm_eq_abs, abs_of_nonneg (duhamelIntegrand_nonneg K g hgn p r)]
      exact duhamelIntegrand_le K g hgn C hC hgb p r)
  unfold duhamelPotential at hnon ⊢
  rw [Real.norm_eq_abs, abs_of_nonneg hnon] at hn
  simpa only [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hp), mul_comm] using hn

/-- At and after the terminal time the zero-extended potential vanishes. -/
theorem duhamelPotential_eq_zero_of_terminal_le {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ) (τplus : ℝ)
    (g : KineticPoint d → ℝ) (p : KineticPoint d) (hp : τplus ≤ p.time) :
    duhamelPotential K τplus g p = 0 := by
  rw [duhamelPotential, Ioc_eq_empty_of_le hp, Measure.restrict_empty, integral_zero_measure]

/-- Outside the open starting fiber the zero extension vanishes by definition. -/
theorem duhamelPotential_eq_zero_of_not_mem {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (K : MovingFiberKernel Ω γ) (τplus : ℝ)
    (g : KineticPoint d → ℝ) (p : KineticPoint d)
    (hp : p.position ∉ movingDomain Ω γ p.time) :
    duhamelPotential K τplus g p = 0 := by
  have hz : duhamelIntegrand K g p = 0 := by
    funext r
    exact dite_eq_right (fun h => hp h.2)
  simp only [duhamelPotential, hz, Pi.zero_apply, integral_zero]

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

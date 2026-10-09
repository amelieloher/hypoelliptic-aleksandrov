module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Green
public import HypoellipticAleksandrov.Parabolic.Geometry
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Parabolic Duhamel potentials against the marginal kernel

For a source `g` on `ℝ × ℝ^d` the parabolic Duhamel potential is
`W(s,v) = ∫_s^T ∫ g(r,w) P_{s,r}(v,dw) dr`, where `P` is the parabolic marginal kernel
`parabolicMarginalKernel` of a supplied moving-fiber kernel, extended by zero outside the
starting fiber.  This module defines the integrand and the potential, identifies the source
integrals with integrals against the master kernel, and proves joint Borel measurability and the
elementary bounds `0 ≤ W ≤ (T - s) sup g`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Set
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open scoped ENNReal ProbabilityTheory

variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/-- The source integral `∫ g(r,w) P_{s,r}(y,dw)` against the parabolic marginal kernel. -/
def parabolicSourceIntegral (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω)
    (g : TimeVelocity d → ℝ) (s r : ℝ) (h : s ≤ r) (y : EvolutionPosition Ω γ s) : ℝ :=
  ∫ y', g (r, y'.1) ∂(parabolicMarginalKernel K hΩ s r h y)

/-- The source-time integrand, extended by zero outside the valid starting fiber. -/
def parabolicDuhamelIntegrand (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω)
    (g : TimeVelocity d → ℝ) (p : TimeVelocity d) (r : ℝ) : ℝ := by
  classical
  exact if h : p.1 ≤ r ∧ p.2 ∈ movingDomain Ω γ p.1 then
    parabolicSourceIntegral K hΩ g p.1 r h.1 ⟨p.2, h.2⟩ else 0

/-- The parabolic Duhamel potential `W(s,v) = ∫_s^T ∫ g(r,w) P_{s,r}(v,dw) dr`,
extended by zero outside the starting fiber. -/
def parabolicDuhamelPotential (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω) (T : ℝ)
    (g : TimeVelocity d → ℝ) (p : TimeVelocity d) : ℝ :=
  ∫ r in Ioc p.1 T, parabolicDuhamelIntegrand K hΩ g p r

/-- The source integral against the master kernel, at a valid query. -/
def parabolicMasterIntegral (K : MovingFiberKernel Ω γ) (g : TimeVelocity d → ℝ)
    (q : EvolutionQuery Ω γ) : ℝ :=
  ∫ w, g (q.1.2.1, w.1) ∂K.master q

/-- If the marginal kernel at `y` is the first marginal of the fiber kernel at the state `(y, z)`,
the marginal-kernel source integral is the master-kernel integral of the first coordinate. -/
theorem parabolicSourceIntegral_eq_master_of_state (K : MovingFiberKernel Ω γ)
    (hΩ : MeasurableSet Ω) (g : TimeVelocity d → ℝ) (s r : ℝ) (h : s ≤ r)
    (y : EvolutionPosition Ω γ s) (z : PDE.Vec d)
    (hz : parabolicMarginalKernel K hΩ s r h y =
      K.fiberFirstMarginal hΩ s r h (evolutionStateOfPosition Ω γ s y z))
    (hg : Measurable (fun v : PDE.Vec d => g (r, v))) :
    parabolicSourceIntegral K hΩ g s r h y =
      parabolicMasterIntegral K g ⟨(s, (r, (y.1, z))), h, y.2, mem_univ _⟩ := by
  unfold parabolicSourceIntegral parabolicMasterIntegral
  rw [hz, MovingFiberKernel.fiberFirstMarginal,
    ProbabilityTheory.Kernel.map_apply _ (MovingFiberKernel.measurable_firstPosition Ω γ r)]
  have hf : Measurable (fun y' : EvolutionPosition Ω γ r => g (r, y'.1)) :=
    hg.comp measurable_subtype_coe
  rw [integral_map (f := fun y' : EvolutionPosition Ω γ r => g (r, y'.1))
    (MovingFiberKernel.measurable_firstPosition Ω γ r).aemeasurable hf.aestronglyMeasurable]
  have hq := K.map_fiberKernel_eq_master hΩ s r h (evolutionStateOfPosition Ω γ s y z)
  have hf2 : Measurable (fun w : EvolutionAmbientState d => g (r, w.1)) :=
    hg.comp measurable_fst
  change _ = ∫ w, g (r, w.1) ∂K.master
    (evolutionQueryOfState Ω γ s r h (evolutionStateOfPosition Ω γ s y z))
  rw [← hq, integral_map (f := fun w : EvolutionAmbientState d => g (r, w.1))
    measurable_subtype_coe.aemeasurable hf2.aestronglyMeasurable]
  rfl

/-- The marginal-kernel source integral is the master-kernel integral at `z = 0`. -/
theorem parabolicSourceIntegral_eq_master (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω)
    (g : TimeVelocity d → ℝ) (s r : ℝ) (h : s ≤ r) (y : EvolutionPosition Ω γ s)
    (hg : Measurable (fun v : PDE.Vec d => g (r, v))) :
    parabolicSourceIntegral K hΩ g s r h y =
      parabolicMasterIntegral K g ⟨(s, (r, (y.1, 0))), h, y.2, mem_univ _⟩ :=
  parabolicSourceIntegral_eq_master_of_state K hΩ g s r h y 0 rfl hg

/-- The master-kernel source integral is Borel in the query. -/
theorem measurable_parabolicMasterIntegral (K : MovingFiberKernel Ω γ)
    (g : TimeVelocity d → ℝ) (hg : Measurable g) :
    Measurable (parabolicMasterIntegral K g) := by
  have hm : Measurable (fun q : EvolutionQuery Ω γ × EvolutionAmbientState d =>
      g (q.1.1.2.1, q.2.1)) := by
    have ht : Measurable (fun q : EvolutionQuery Ω γ × EvolutionAmbientState d =>
        q.1.1.2.1) := measurable_subtype_coe.snd.fst.comp measurable_fst
    exact hg.comp (ht.prodMk (measurable_snd.fst))
  exact (hm.stronglyMeasurable.integral_kernel_prod_right' (κ := K.master)).measurable

/-- Nonnegative sources have nonnegative master integrals. -/
theorem parabolicMasterIntegral_nonneg (K : MovingFiberKernel Ω γ) (g : TimeVelocity d → ℝ)
    (hgn : ∀ p, 0 ≤ g p) (q : EvolutionQuery Ω γ) : 0 ≤ parabolicMasterIntegral K g q :=
  integral_nonneg (fun _ => hgn _)

/-- Contraction bounds the master integral of a bounded nonnegative source. -/
theorem parabolicMasterIntegral_le (K : MovingFiberKernel Ω γ) (g : TimeVelocity d → ℝ)
    (hgn : ∀ p, 0 ≤ g p) (C : ℝ) (hgb : ∀ p, g p ≤ C) (q : EvolutionQuery Ω γ) :
    parabolicMasterIntegral K g q ≤ C := by
  have hC : 0 ≤ C := (hgn (0, 0)).trans (hgb _)
  have hn : ‖parabolicMasterIntegral K g q‖ ≤ C * (K.master q).real univ := by
    apply norm_integral_le_of_norm_le_const
    exact Filter.Eventually.of_forall fun _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hgn _)]
      exact hgb _
  have hm : (K.master q).real univ ≤ 1 := by
    simpa only [Measure.real, ENNReal.toReal_one] using
      ENNReal.toReal_mono ENNReal.one_ne_top (K.mass_le_one q)
  rw [Real.norm_eq_abs] at hn
  exact (le_abs_self _).trans (hn.trans (by nlinarith))

variable (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω)

/-- Away from the valid fiber the integrand is zero. -/
theorem parabolicDuhamelIntegrand_of_not_valid (g : TimeVelocity d → ℝ) (p : TimeVelocity d)
    (r : ℝ) (h : ¬ (p.1 ≤ r ∧ p.2 ∈ movingDomain Ω γ p.1)) :
    parabolicDuhamelIntegrand K hΩ g p r = 0 := by
  unfold parabolicDuhamelIntegrand
  exact dite_eq_right h

/-- On the valid fiber the integrand is the marginal-kernel source integral. -/
theorem parabolicDuhamelIntegrand_of_valid (g : TimeVelocity d → ℝ) (p : TimeVelocity d)
    (r : ℝ) (h : p.1 ≤ r ∧ p.2 ∈ movingDomain Ω γ p.1) :
    parabolicDuhamelIntegrand K hΩ g p r =
      parabolicSourceIntegral K hΩ g p.1 r h.1 ⟨p.2, h.2⟩ := by
  unfold parabolicDuhamelIntegrand
  exact dite_eq_left h

open Classical in
/-- The integrand equals the zero-extended master-kernel integral. -/
theorem parabolicDuhamelIntegrand_eq_master (g : TimeVelocity d → ℝ)
    (hg : ∀ r, Measurable (fun v : PDE.Vec d => g (r, v))) (p : TimeVelocity d) (r : ℝ) :
    parabolicDuhamelIntegrand K hΩ g p r =
      if h : p.1 ≤ r ∧ p.2 ∈ movingDomain Ω γ p.1 then
        parabolicMasterIntegral K g ⟨(p.1, (r, (p.2, 0))), h.1, h.2, mem_univ _⟩ else 0 := by
  by_cases h : p.1 ≤ r ∧ p.2 ∈ movingDomain Ω γ p.1
  · rw [parabolicDuhamelIntegrand_of_valid K hΩ g p r h]
    simp only [h, and_self, ↓reduceDIte]
    exact parabolicSourceIntegral_eq_master K hΩ g p.1 r h.1 ⟨p.2, h.2⟩ (hg r)
  · rw [parabolicDuhamelIntegrand_of_not_valid K hΩ g p r h]
    simp only [h, ↓reduceDIte]

/-- Nonnegativity of the integrand for a nonnegative Borel source. -/
theorem parabolicDuhamelIntegrand_nonneg (g : TimeVelocity d → ℝ)
    (hg : ∀ r, Measurable (fun v : PDE.Vec d => g (r, v))) (hgn : ∀ p, 0 ≤ g p)
    (p : TimeVelocity d) (r : ℝ) : 0 ≤ parabolicDuhamelIntegrand K hΩ g p r := by
  rw [parabolicDuhamelIntegrand_eq_master K hΩ g hg]
  split_ifs
  · exact parabolicMasterIntegral_nonneg K g hgn _
  · exact le_rfl

/-- Upper bound of the integrand by any upper bound of a nonnegative source. -/
theorem parabolicDuhamelIntegrand_le (g : TimeVelocity d → ℝ)
    (hg : ∀ r, Measurable (fun v : PDE.Vec d => g (r, v))) (hgn : ∀ p, 0 ≤ g p)
    (C : ℝ) (hgb : ∀ p, g p ≤ C) (p : TimeVelocity d) (r : ℝ) :
    parabolicDuhamelIntegrand K hΩ g p r ≤ C := by
  rw [parabolicDuhamelIntegrand_eq_master K hΩ g hg]
  split_ifs
  · exact parabolicMasterIntegral_le K g hgn C hgb _
  · exact (hgn (0, 0)).trans (hgb _)

/-- Joint Borel dependence of the integrand on the point and the source time. -/
theorem measurable_parabolicDuhamelIntegrand (hγ : Continuous γ) (g : TimeVelocity d → ℝ)
    (hgm : Measurable g) :
    Measurable (fun q : TimeVelocity d × ℝ => parabolicDuhamelIntegrand K hΩ g q.1 q.2) := by
  classical
  have hg : ∀ r, Measurable (fun v : PDE.Vec d => g (r, v)) := fun r =>
    hgm.comp (measurable_const.prodMk measurable_id)
  let D : Set (TimeVelocity d × ℝ) :=
    {q | q.1.1 ≤ q.2 ∧ q.1.2 ∈ movingDomain Ω γ q.1.1}
  have hD : MeasurableSet D := by
    have ht : MeasurableSet {q : TimeVelocity d × ℝ | q.1.1 ≤ q.2} :=
      measurableSet_le (measurable_fst.fst) measurable_snd
    have hp : MeasurableSet {q : TimeVelocity d × ℝ | q.1.2 - γ q.1.1 ∈ Ω} :=
      hΩ.preimage ((measurable_fst.snd).sub (hγ.measurable.comp measurable_fst.fst))
    convert ht.inter hp using 1
    ext q
    simp only [D, mem_ofPred_eq, mem_inter_iff]
    change (_ ∧ _ ∈ PDE.translateSet (γ q.1.1) Ω) ↔ _
    rw [PDE.mem_translateSet_iff_sub_mem]
  let Q : D → EvolutionQuery Ω γ := fun q =>
    ⟨(q.1.1.1, (q.1.2, (q.1.1.2, 0))), q.2.1, q.2.2, mem_univ _⟩
  have hQ : Measurable Q := by
    apply Measurable.subtype_mk
    change Measurable (fun q : D => (q.1.1.1, (q.1.2, (q.1.1.2, (0 : PDE.Vec d)))))
    exact (measurable_subtype_coe.fst.fst).prodMk
      (measurable_subtype_coe.snd.prodMk
        ((measurable_subtype_coe.fst.snd).prodMk measurable_const))
  have hmi : Measurable (fun q : TimeVelocity d × ℝ =>
      if h : q.1.1 ≤ q.2 ∧ q.1.2 ∈ movingDomain Ω γ q.1.1 then
        parabolicMasterIntegral K g ⟨(q.1.1, (q.2, (q.1.2, 0))), h.1, h.2, mem_univ _⟩
      else 0) :=
    ((measurable_parabolicMasterIntegral K g hgm).comp hQ).dite measurable_const hD
  convert hmi using 1
  funext q
  exact parabolicDuhamelIntegrand_eq_master K hΩ g hg q.1 q.2

/-- The integrand vanishes at source times whose slice of the source is zero. -/
theorem parabolicDuhamelIntegrand_eq_zero_of_slice (g : TimeVelocity d → ℝ)
    (hg : ∀ r, Measurable (fun v : PDE.Vec d => g (r, v))) (p : TimeVelocity d) (r : ℝ)
    (h0 : ∀ v, g (r, v) = 0) : parabolicDuhamelIntegrand K hΩ g p r = 0 := by
  rw [parabolicDuhamelIntegrand_eq_master K hΩ g hg]
  split_ifs
  · simp only [parabolicMasterIntegral, h0, integral_zero]
  · exact rfl

/-- The potential is Borel for every measurable source. -/
theorem measurable_parabolicDuhamelPotential (hγ : Continuous γ) (T : ℝ)
    (g : TimeVelocity d → ℝ) (hg : Measurable g) :
    Measurable (parabolicDuhamelPotential K hΩ T g) := by
  let D : Set (TimeVelocity d × ℝ) := {q | q.1.1 < q.2 ∧ q.2 ≤ T}
  have hD : MeasurableSet D :=
    (measurableSet_lt measurable_fst.fst measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)
  have hi := ((measurable_parabolicDuhamelIntegrand K hΩ hγ g hg).indicator hD
    ).stronglyMeasurable
  convert (hi.integral_prod_right' (ν := (volume : Measure ℝ))).measurable using 1
  funext p
  rw [parabolicDuhamelPotential, ← integral_indicator measurableSet_Ioc]
  rfl

/-- The potential of a nonnegative source is nonnegative. -/
theorem parabolicDuhamelPotential_nonneg (T : ℝ) (g : TimeVelocity d → ℝ)
    (hg : ∀ r, Measurable (fun v : PDE.Vec d => g (r, v))) (hgn : ∀ p, 0 ≤ g p)
    (p : TimeVelocity d) : 0 ≤ parabolicDuhamelPotential K hΩ T g p :=
  integral_nonneg (fun r => parabolicDuhamelIntegrand_nonneg K hΩ g hg hgn p r)

/-- Contraction gives the Duhamel estimate `W ≤ (T - s) C` for `g ≤ C`. -/
theorem parabolicDuhamelPotential_le (T : ℝ) (g : TimeVelocity d → ℝ)
    (hg : ∀ r, Measurable (fun v : PDE.Vec d => g (r, v))) (hgn : ∀ p, 0 ≤ g p)
    (C : ℝ) (hgb : ∀ p, g p ≤ C) (p : TimeVelocity d) (hp : p.1 ≤ T) :
    parabolicDuhamelPotential K hΩ T g p ≤ (T - p.1) * C := by
  have hnon := parabolicDuhamelPotential_nonneg K hΩ T g hg hgn p
  have hn := norm_integral_le_of_norm_le_const
    (μ := volume.restrict (Ioc p.1 T)) (f := parabolicDuhamelIntegrand K hΩ g p)
    (C := C) (Filter.Eventually.of_forall fun r => by
      rw [Real.norm_eq_abs, abs_of_nonneg (parabolicDuhamelIntegrand_nonneg K hΩ g hg hgn p r)]
      exact parabolicDuhamelIntegrand_le K hΩ g hg hgn C hgb p r)
  unfold parabolicDuhamelPotential at hnon ⊢
  rw [Real.norm_eq_abs, abs_of_nonneg hnon] at hn
  simpa only [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hp), mul_comm] using hn

/-- At and after the terminal time the potential vanishes. -/
theorem parabolicDuhamelPotential_eq_zero_of_terminal_le (T : ℝ) (g : TimeVelocity d → ℝ)
    (p : TimeVelocity d) (hp : T ≤ p.1) : parabolicDuhamelPotential K hΩ T g p = 0 := by
  rw [parabolicDuhamelPotential, Ioc_eq_empty_of_le hp, Measure.restrict_empty,
    integral_zero_measure]

/-- Outside the open starting fiber the zero extension vanishes. -/
theorem parabolicDuhamelPotential_eq_zero_of_not_mem (T : ℝ) (g : TimeVelocity d → ℝ)
    (p : TimeVelocity d) (hp : p.2 ∉ movingDomain Ω γ p.1) :
    parabolicDuhamelPotential K hΩ T g p = 0 := by
  have hz : parabolicDuhamelIntegrand K hΩ g p = 0 := by
    funext r
    exact parabolicDuhamelIntegrand_of_not_valid K hΩ g p r (fun h => hp h.2)
  simp only [parabolicDuhamelPotential, hz, Pi.zero_apply, integral_zero]

end HypoellipticAleksandrov.KineticAleksandrov.Occupation

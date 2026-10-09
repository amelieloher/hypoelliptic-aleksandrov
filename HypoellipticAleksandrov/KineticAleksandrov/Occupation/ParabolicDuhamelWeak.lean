module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelTerminal

/-!
# The weak equation of the Duhamel potential

Integrating the slice identities `∫_{σ<r} u_r Lop^*ψ + ∫ g(r,·)ψ(r,·) = 0` over the source time
`r` (Fubini) gives `∫ W Lop^*ψ = -∫ g ψ` for every test `ψ` supported in `π ⁻¹' U₀`, where `W` is
the parabolic Duhamel potential regarded as a `z`-independent function of the packed point.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Set Filter
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.Evolution
open scoped Topology

variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
variable (K : MovingFiberKernel Ω γ)

/-- The source slice integrand vanishes after the terminal time. -/
theorem integrand_eq_zero_of_ge {hΩ : MeasurableSet Ω} (g : TimeVelocity d → ℝ)
    (hg : ∀ r, Measurable (fun v : PDE.Vec d => g (r, v))) (T : ℝ)
    (hgU : tsupport g ⊆ duhamelFiber Ω γ T) (p : TimeVelocity d) {r : ℝ} (hr : T ≤ r) :
    parabolicDuhamelIntegrand K hΩ g p r = 0 := by
  refine parabolicDuhamelIntegrand_eq_zero_of_slice K hΩ g hg p r (fun v => ?_)
  apply image_eq_zero_of_notMem_tsupport
  intro h
  exact absurd (hgU h).1 (not_lt.2 hr)

/-- The potential is the integral of the integrand over all later source times. -/
theorem potential_eq_integral_Ioi {hΩ : MeasurableSet Ω} (g : TimeVelocity d → ℝ)
    (hg : ∀ r, Measurable (fun v : PDE.Vec d => g (r, v))) (T : ℝ)
    (hgU : tsupport g ⊆ duhamelFiber Ω γ T) (p : TimeVelocity d) :
    parabolicDuhamelPotential K hΩ T g p =
      ∫ r in Ioi p.1, parabolicDuhamelIntegrand K hΩ g p r := by
  unfold parabolicDuhamelPotential
  symm
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    Ioc_subset_Ioi_self (fun r hr => ?_)
  have hrT : T ≤ r := not_lt.1 fun h => hr.2 ⟨hr.1, h.le⟩
  exact integrand_eq_zero_of_ge K g hg T hgU p hrT

/-- **The weak equation of the Duhamel potential.**  For every smooth compactly supported test
`ψ` with support in the preimage of `U₀`, `∫ W Lop^* ψ = -∫ g ψ`. -/
theorem duhamel_weak_identity {B : CoefficientField d}
    (hΩa : IsAdmissibleEvolutionDomain Ω) (hγ : Continuous γ)
    (hP : SectionTwo.HasParabolicMarginalBundle Ω γ
      (measurableSet_of_isAdmissibleEvolutionDomain hΩa) (zIndependentCoefficient B) K)
    (hB : IsSmoothFullKineticCoefficient (zIndependentCoefficient B))
    {b : PDE.Vec d → PDE.Vec d} (hb : IsSmoothDrift b)
    (g : TimeVelocity d → ℝ) (hgn : ∀ p, 0 ≤ g p) (hgs : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) (T : ℝ) (hgU : tsupport g ⊆ duhamelFiber Ω γ T)
    {ψ : EvolutionVec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ evolutionToTimeVelocity d ⁻¹' duhamelFiber Ω γ T) :
    (∫ x, parabolicDuhamelPotential K (measurableSet_of_isAdmissibleEvolutionDomain hΩa) T g
        (evolutionToTimeVelocity d x) *
        transportedAdjoint (zIndependentCoefficient B) b ψ x) =
      -∫ x, g (evolutionToTimeVelocity d x) * ψ x := by
  have hΩ := measurableSet_of_isAdmissibleEvolutionDomain hΩa
  obtain ⟨a, b₀, hab⟩ := exists_time_range g hgc
  obtain ⟨C, hC⟩ := hgs.continuous.bounded_above_of_compact_support hgc
  have hgb : ∀ p, g p ≤ C := fun p => (le_abs_self _).trans (by simpa using hC p)
  have hC0 : 0 ≤ C := (hgn (0, 0)).trans (hgb _)
  have hgm : Measurable g := hgs.continuous.measurable
  have hg : ∀ r, Measurable (fun v : PDE.Vec d => g (r, v)) := fun r =>
    hgm.comp (measurable_const.prodMk measurable_id)
  have hmeas := measurable_parabolicDuhamelIntegrand K hΩ hγ g hgm
  have hub : ∀ p r, |parabolicDuhamelIntegrand K hΩ g p r| ≤ C := fun p r => by
    rw [abs_of_nonneg (parabolicDuhamelIntegrand_nonneg K hΩ g hg hgn p r)]
    exact parabolicDuhamelIntegrand_le K hΩ g hg hgn C hgb p r
  let Λ : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ := fun q =>
    transportedAdjoint (zIndependentCoefficient B) b ψ (packQ d q)
  let Ψ : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ := fun q => ψ (packQ d q)
  have hΛc : Continuous Λ :=
    (contDiff_transportedAdjoint hB hb hψ).continuous.comp continuous_packQ
  have hΛs : HasCompactSupport Λ :=
    hasCompactSupport_comp_packQ (hasCompactSupport_transportedAdjoint hc)
  have hΨc : Continuous Ψ := hψ.continuous.comp continuous_packQ
  have hΨs : HasCompactSupport Ψ := hasCompactSupport_comp_packQ hc
  have per : ∀ r : ℝ, (∫ q : ℝ × (PDE.Vec d × PDE.Vec d),
      {q : ℝ × (PDE.Vec d × PDE.Vec d) | q.1 < r}.indicator
        (fun q => parabolicDuhamelIntegrand K hΩ g (q.1, q.2.1) r * Λ q) q) +
      ∫ w : PDE.Vec d × PDE.Vec d, g (r, w.1) * Ψ (r, w) = 0 := by
    intro r
    obtain ⟨V, -, -, hVsm, hVeq, -, hVint⟩ := slice_regularity K hΩa hP g hgs hgc T hgU r
    have hD : IsOpen (sliceOpenCylinder Ω γ r) :=
      isOpen_duhamelFiber (isOpen_of_isAdmissibleEvolutionDomain hΩa) hγ r
    exact slice_weak_identity (u := fun p => parabolicDuhamelIntegrand K hΩ g p r) hB hb hD
      hVsm hVeq (fun p hp => hVint p ⟨hp.1.le, subset_closure hp.2⟩)
      (hmeas.comp (measurable_id.prodMk measurable_const)) C hC0 (fun p => hub p r) hψ hc r
      (fun x hx hxr => ⟨hxr, (hψs hx).2⟩)
      (fun w => g (r, w.1) * ψ (packQ d (r, w)))
      (slice_terminal_limit K hΩa hγ hP g hgs hgc T hgU C hub hψ.continuous hψs r)
  -- Fubini in the source time `r` and the packed coordinates `q`.
  let F1 : ℝ × (ℝ × (PDE.Vec d × PDE.Vec d)) → ℝ := fun z =>
    {z : ℝ × (ℝ × (PDE.Vec d × PDE.Vec d)) | z.2.1 < z.1}.indicator
      (fun z => parabolicDuhamelIntegrand K hΩ g (z.2.1, z.2.2.1) z.1 * Λ z.2) z
  have hS : MeasurableSet {z : ℝ × (ℝ × (PDE.Vec d × PDE.Vec d)) | z.2.1 < z.1} :=
    measurableSet_lt (measurable_snd.fst) measurable_fst
  have hGm : Measurable (fun z : ℝ × (ℝ × (PDE.Vec d × PDE.Vec d)) =>
      parabolicDuhamelIntegrand K hΩ g (z.2.1, z.2.2.1) z.1 * Λ z.2) :=
    (hmeas.comp (((measurable_snd.fst).prodMk (measurable_snd.snd.fst)).prodMk
      measurable_fst)).mul (hΛc.measurable.comp measurable_snd)
  have hF1m : Measurable F1 := hGm.indicator hS
  have hbnd : Integrable (fun z : ℝ × (ℝ × (PDE.Vec d × PDE.Vec d)) =>
      (Icc a b₀).indicator (fun _ => C) z.1 * ‖Λ z.2‖)
      ((volume : Measure ℝ).prod (volume : Measure (ℝ × (PDE.Vec d × PDE.Vec d)))) :=
    Integrable.mul_prod ((integrable_indicator_iff measurableSet_Icc).2
      (integrableOn_const (by simp))) (hΛc.integrable_of_hasCompactSupport hΛs).norm
  have hF1int : Integrable F1
      ((volume : Measure ℝ).prod (volume : Measure (ℝ × (PDE.Vec d × PDE.Vec d)))) := by
    refine hbnd.mono' hF1m.aestronglyMeasurable (Eventually.of_forall fun z => ?_)
    have hnn : 0 ≤ (Icc a b₀).indicator (fun _ => C) z.1 * ‖Λ z.2‖ :=
      mul_nonneg (indicator_nonneg (fun _ _ => hC0) _) (norm_nonneg _)
    by_cases hz : z.2.1 < z.1
    · have hF : F1 z = parabolicDuhamelIntegrand K hΩ g (z.2.1, z.2.2.1) z.1 * Λ z.2 :=
        indicator_of_mem (show z ∈ {z : ℝ × (ℝ × (PDE.Vec d × PDE.Vec d)) | z.2.1 < z.1} from hz) _
      rw [hF, norm_mul, Real.norm_eq_abs]
      by_cases hr : z.1 ∈ Icc a b₀
      · rw [indicator_of_mem hr]
        exact mul_le_mul_of_nonneg_right (hub _ _) (norm_nonneg _)
      · rw [parabolicDuhamelIntegrand_eq_zero_of_slice K hΩ g hg _ _ (hab _ hr)]
        simpa using hnn
    · have hF : F1 z = 0 :=
        indicator_of_notMem
          (show z ∉ {z : ℝ × (ℝ × (PDE.Vec d × PDE.Vec d)) | z.2.1 < z.1} from hz) _
      rw [hF, norm_zero]
      exact hnn
  let F2 : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ := fun q => g (q.1, q.2.1) * Ψ q
  have hF2c : Continuous F2 :=
    (hgs.continuous.comp (continuous_fst.prodMk (continuous_snd.fst))).mul hΨc
  have hF2int : Integrable F2
      ((volume : Measure ℝ).prod (volume : Measure (PDE.Vec d × PDE.Vec d))) :=
    hF2c.integrable_of_hasCompactSupport hΨs.mul_left
  have hAint : Integrable (fun r => ∫ q, F1 (r, q)) :=
    hF1int.integral_prod_left
  have hMint : Integrable (fun r => ∫ w, F2 (r, w)) :=
    hF2int.integral_prod_left
  have hsum : (∫ r, ∫ q, F1 (r, q)) + ∫ r, ∫ w, F2 (r, w) = 0 := by
    rw [← integral_add hAint hMint]
    have : (fun r => (∫ q, F1 (r, q)) + ∫ w, F2 (r, w)) = fun _ => (0 : ℝ) := funext per
    rw [this, integral_zero]
  have hA : (∫ r, ∫ q, F1 (r, q)) =
      ∫ q : ℝ × (PDE.Vec d × PDE.Vec d), Λ q *
        parabolicDuhamelPotential K hΩ T g (q.1, q.2.1) := by
    rw [← integral_prod F1 hF1int, integral_prod_symm F1 hF1int]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    have hfun : (fun r => F1 (r, q)) = (Ioi q.1).indicator
        (fun r => Λ q * parabolicDuhamelIntegrand K hΩ g (q.1, q.2.1) r) := by
      funext r
      by_cases hr : q.1 < r
      · rw [indicator_of_mem (show r ∈ Ioi q.1 from hr)]
        exact (indicator_of_mem (show (r, q) ∈ {z : ℝ × (ℝ × (PDE.Vec d × PDE.Vec d)) |
          z.2.1 < z.1} from hr) _).trans (mul_comm _ _)
      · rw [indicator_of_notMem (show r ∉ Ioi q.1 from hr)]
        exact indicator_of_notMem (show (r, q) ∉ {z : ℝ × (ℝ × (PDE.Vec d × PDE.Vec d)) |
          z.2.1 < z.1} from hr) _
    have hq : ∫ r, F1 (r, q) = Λ q * ∫ r in Ioi q.1,
        parabolicDuhamelIntegrand K hΩ g (q.1, q.2.1) r := by
      change ∫ r, (fun r => F1 (r, q)) r = _
      rw [hfun, integral_indicator measurableSet_Ioi, integral_const_mul]
    show (∫ r, F1 (r, q)) = Λ q * parabolicDuhamelPotential K hΩ T g (q.1, q.2.1)
    rw [hq, potential_eq_integral_Ioi K g hg T hgU (q.1, q.2.1)]
  have hM : (∫ r, ∫ w, F2 (r, w)) = ∫ q : ℝ × (PDE.Vec d × PDE.Vec d), F2 q :=
    (integral_prod F2 hF2int).symm
  rw [hA, hM] at hsum
  have e1 : (∫ x, parabolicDuhamelPotential K hΩ T g (evolutionToTimeVelocity d x) *
      transportedAdjoint (zIndependentCoefficient B) b ψ x) =
      ∫ q : ℝ × (PDE.Vec d × PDE.Vec d), Λ q *
        parabolicDuhamelPotential K hΩ T g (q.1, q.2.1) := by
    rw [integral_evolution_eq_prod]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    simp only [evolutionToTimeVelocity_packQ, Λ]
    ring
  have e2 : (∫ x, g (evolutionToTimeVelocity d x) * ψ x) = ∫ q, F2 q := by
    rw [integral_evolution_eq_prod]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    simp only [evolutionToTimeVelocity_packQ, F2, Ψ]
  rw [e1, e2]
  linarith

end HypoellipticAleksandrov.KineticAleksandrov.Occupation

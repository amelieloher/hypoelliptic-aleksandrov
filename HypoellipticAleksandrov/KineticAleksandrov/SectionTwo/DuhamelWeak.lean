module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelTerminal

/-! # Distributional equation for the kinetic Duhamel potential -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set Filter
open Evolution Occupation
open scoped Topology
variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/-- Packing the product coordinates agrees with the existing kinetic coordinate homeomorphism. -/
@[simp] theorem duhamel_homeomorph_packQ (q : ℝ × EvolutionAmbientState d) :
    evolutionHomeomorph d (packQ d q) = ⟨q.1, q.2.1, q.2.2⟩ := by
  simp only [evolutionHomeomorph_apply, packQ, timeCoord_packPoint,
    diffusedCoord_packPoint, transportedCoord_packPoint]

/-- Source integrands vanish at all source times at or beyond the terminal face. -/
theorem duhamelIntegrand_eq_zero_of_ge (K : MovingFiberKernel Ω γ)
    (g : KineticPoint d → ℝ) (T : ℝ)
    (hU : tsupport g ⊆ evolutionPastOpenCylinder Ω γ T)
    (p : KineticPoint d) {r : ℝ} (hr : T ≤ r) : duhamelIntegrand K g p r = 0 := by
  unfold duhamelIntegrand
  split
  · unfold duhamelSourceIntegral
    have hz : ∀ w : EvolutionAmbientState d, g ⟨r, w.1, w.2⟩ = 0 := by
      intro w
      apply image_eq_zero_of_notMem_tsupport
      intro h
      exact absurd (hU h).1 (not_lt.2 hr)
    simp only [hz, integral_zero]
  · rfl

/-- Compact interior source support allows integration over every later source time. -/
theorem duhamelPotential_eq_integral_Ioi (K : MovingFiberKernel Ω γ)
    (g : KineticPoint d → ℝ) (T : ℝ)
    (hU : tsupport g ⊆ evolutionPastOpenCylinder Ω γ T) (p : KineticPoint d) :
    duhamelPotential K T g p = ∫ r in Ioi p.time, duhamelIntegrand K g p r := by
  unfold duhamelPotential
  symm
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    Ioc_subset_Ioi_self (fun r hr => ?_)
  have hrT : T ≤ r := not_lt.1 fun h => hr.2 ⟨hr.1, h.le⟩
  exact duhamelIntegrand_eq_zero_of_ge K g T hU p hrT

/-- The kinetic source potential satisfies the exact full adjoint distributional identity. -/
theorem duhamel_weak_identity (hΩa : IsAdmissibleEvolutionDomain Ω)
    (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K)
    (hB : IsSmoothFullKineticCoefficient B) (hBs : IsSymmetricFullKineticCoefficient B)
    (hb : IsSmoothDrift b) (g : KineticPoint d → ℝ) (hgn : ∀ p, 0 ≤ g p)
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgs : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × EvolutionAmbientState d =>
      g ⟨q.1, q.2.1, q.2.2⟩)) (T : ℝ)
    (hgU : tsupport g ⊆ evolutionPastOpenCylinder Ω γ T)
    {ψ : EvolutionVec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ evolutionHomeomorph d ⁻¹' evolutionPastOpenCylinder Ω γ T) :
    (∫ x, duhamelPotential K T g (evolutionHomeomorph d x) * transportedAdjoint B b ψ x) =
      -∫ x, g (evolutionHomeomorph d x) * ψ x := by
  obtain ⟨a, b₀, -, hab⟩ := exists_time_window_of_hasCompactSupport g hgc
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hgc
  have hgb : ∀ p, g p ≤ C := fun p => (le_abs_self _).trans (by simpa using hC p)
  have hC0 : 0 ≤ C := (hgn ⟨0, 0, 0⟩).trans (hgb _)
  have hgm : Measurable g := hg.measurable
  have hmeas := measurable_duhamelIntegrand K hΩ hγ g hgm
  have hub : ∀ p r, |duhamelIntegrand K g p r| ≤ C := fun p r => by
    rw [abs_of_nonneg (duhamelIntegrand_nonneg K g hgn p r)]
    exact duhamelIntegrand_le K g hgn C hC0 hgb p r
  let Λ : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ := fun q =>
    transportedAdjoint B b ψ (packQ d q)
  let Ψ : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ := fun q => ψ (packQ d q)
  have hΛc : Continuous Λ :=
    (contDiff_transportedAdjoint hB hb hψ).continuous.comp continuous_packQ
  have hΛs : HasCompactSupport Λ :=
    hasCompactSupport_comp_packQ (hasCompactSupport_transportedAdjoint hc)
  have hΨc : Continuous Ψ := hψ.continuous.comp continuous_packQ
  have hΨs : HasCompactSupport Ψ := hasCompactSupport_comp_packQ hc
  have per : ∀ r : ℝ, (∫ q : ℝ × (PDE.Vec d × PDE.Vec d),
      {q : ℝ × (PDE.Vec d × PDE.Vec d) | q.1 < r}.indicator
        (fun q => duhamelIntegrand K g ⟨q.1, q.2.1, q.2.2⟩ r * Λ q) q) +
      ∫ w : PDE.Vec d × PDE.Vec d, g ⟨r, w.1, w.2⟩ * Ψ (r, w) = 0 := by
    intro r
    obtain ⟨V, hV, hVe⟩ := exists_duhamelSlice_solution hΩ B b S K hreal
      g hg hgc hgs T hgU r
    let D := evolutionHomeomorph d ⁻¹' evolutionPastOpenCylinder Ω γ r
    have hD : IsOpen D := (isOpen_duhamelCylinder
      (isOpen_of_isAdmissibleEvolutionDomain hΩa) hγ r).preimage (evolutionHomeomorph d).continuous
    have hVsm : ContDiffOn ℝ (⊤ : ℕ∞) (V ∘ evolutionHomeomorph d) D :=
      hV.2.2.1.comp (evolutionProdCLE d).contDiff.contDiffOn (fun x hx => hx)
    have hVeq : ∀ x ∈ D, transportedOperator B b (V ∘ evolutionHomeomorph d) x = 0 := by
      intro x hx
      rw [transportedOperator_comp ((hVsm.contDiffAt (hD.mem_nhds hx)).of_le (by simp))]
      exact hV.2.2.2.1 _ hx
    have huV : ∀ x ∈ D, duhamelIntegrand K g (evolutionHomeomorph d x) r =
        (V ∘ evolutionHomeomorph d) x := fun x hx =>
      duhamelIntegrand_eq_slice_solution hΩa K g r V hV.2.2.2.2.2 hVe _
        ⟨hx.1.le, subset_closure hx.2⟩
    have hm : Measurable (fun x => duhamelIntegrand K g (evolutionHomeomorph d x) r) :=
      hmeas.comp ((evolutionHomeomorph d).continuous.measurable.prodMk measurable_const)
    have key := kinetic_slice_weak_identity hB hBs hb hD hVsm hVeq huV hm C hC0
      (fun x => hub _ r) hψ hc r (fun x hx hxr => ⟨hxr, (hψs hx).2⟩)
      (fun w => g ⟨r, w.1, w.2⟩ * ψ (packQ d (r, w)))
      (by simpa only [duhamel_homeomorph_packQ] using
        (duhamelSlice_terminalLimit hΩa hΩ hγ B b S K hreal g hg hgc hgs T hgU C hub
          hψ.continuous hψs r))
    simpa only [duhamel_homeomorph_packQ] using key
  -- Fubini in the source time `r` and the packed coordinates `q`.
  let F1 : ℝ × (ℝ × (PDE.Vec d × PDE.Vec d)) → ℝ := fun z =>
    {z : ℝ × (ℝ × (PDE.Vec d × PDE.Vec d)) | z.2.1 < z.1}.indicator
      (fun z => duhamelIntegrand K g ⟨z.2.1, z.2.2.1, z.2.2.2⟩ z.1 * Λ z.2) z
  have hS : MeasurableSet {z : ℝ × (ℝ × (PDE.Vec d × PDE.Vec d)) | z.2.1 < z.1} :=
    measurableSet_lt (measurable_snd.fst) measurable_fst
  have hGm : Measurable (fun z : ℝ × (ℝ × (PDE.Vec d × PDE.Vec d)) =>
      duhamelIntegrand K g ⟨z.2.1, z.2.2.1, z.2.2.2⟩ z.1 * Λ z.2) :=
    (hmeas.comp (((KineticPoint.measurable_equivProd_symm d).comp measurable_snd).prodMk
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
    · have hF : F1 z = duhamelIntegrand K g ⟨z.2.1, z.2.2.1, z.2.2.2⟩ z.1 * Λ z.2 :=
        indicator_of_mem (show z ∈ {z : ℝ × (ℝ × (PDE.Vec d × PDE.Vec d)) | z.2.1 < z.1} from hz) _
      rw [hF, norm_mul, Real.norm_eq_abs]
      by_cases hr : z.1 ∈ Icc a b₀
      · rw [indicator_of_mem hr]
        exact mul_le_mul_of_nonneg_right (hub _ _) (norm_nonneg _)
      · rw [duhamelIntegrand_eq_zero_of_time_not_mem K g a b₀ hab _ _ hr]
        simpa using hnn
    · have hF : F1 z = 0 :=
        indicator_of_notMem
          (show z ∉ {z : ℝ × (ℝ × (PDE.Vec d × PDE.Vec d)) | z.2.1 < z.1} from hz) _
      rw [hF, norm_zero]
      exact hnn
  let F2 : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ := fun q => g ⟨q.1, q.2.1, q.2.2⟩ * Ψ q
  have hF2c : Continuous F2 :=
    (hg.comp (KineticPoint.homeomorphProd d).symm.continuous).mul hΨc
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
        duhamelPotential K T g ⟨q.1, q.2.1, q.2.2⟩ := by
    rw [← integral_prod F1 hF1int, integral_prod_symm F1 hF1int]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    have hfun : (fun r => F1 (r, q)) = (Ioi q.1).indicator
        (fun r => Λ q * duhamelIntegrand K g ⟨q.1, q.2.1, q.2.2⟩ r) := by
      funext r
      by_cases hr : q.1 < r
      · rw [indicator_of_mem (show r ∈ Ioi q.1 from hr)]
        exact (indicator_of_mem (show (r, q) ∈ {z : ℝ × (ℝ × (PDE.Vec d × PDE.Vec d)) |
          z.2.1 < z.1} from hr) _).trans (mul_comm _ _)
      · rw [indicator_of_notMem (show r ∉ Ioi q.1 from hr)]
        exact indicator_of_notMem (show (r, q) ∉ {z : ℝ × (ℝ × (PDE.Vec d × PDE.Vec d)) |
          z.2.1 < z.1} from hr) _
    have hq : ∫ r, F1 (r, q) = Λ q * ∫ r in Ioi q.1,
        duhamelIntegrand K g ⟨q.1, q.2.1, q.2.2⟩ r := by
      change ∫ r, (fun r => F1 (r, q)) r = _
      rw [hfun, integral_indicator measurableSet_Ioi, integral_const_mul]
    show (∫ r, F1 (r, q)) = Λ q * duhamelPotential K T g ⟨q.1, q.2.1, q.2.2⟩
    rw [hq, duhamelPotential_eq_integral_Ioi K g T hgU ⟨q.1, q.2.1, q.2.2⟩]
  have hM : (∫ r, ∫ w, F2 (r, w)) = ∫ q : ℝ × (PDE.Vec d × PDE.Vec d), F2 q :=
    (integral_prod F2 hF2int).symm
  rw [hA, hM] at hsum
  have e1 : (∫ x, duhamelPotential K T g (evolutionHomeomorph d x) *
      transportedAdjoint B b ψ x) =
      ∫ q : ℝ × (PDE.Vec d × PDE.Vec d), Λ q *
        duhamelPotential K T g ⟨q.1, q.2.1, q.2.2⟩ := by
    rw [integral_evolution_eq_prod]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    simp only [duhamel_homeomorph_packQ, Λ]
    ring
  have e2 : (∫ x, g (evolutionHomeomorph d x) * ψ x) = ∫ q, F2 q := by
    rw [integral_evolution_eq_prod]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    simp only [duhamel_homeomorph_packQ, F2, Ψ]
  rw [e1, e2]
  linarith

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

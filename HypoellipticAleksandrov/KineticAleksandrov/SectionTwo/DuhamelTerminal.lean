module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelBoundary
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelLayer
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeTransfer
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeOperator

/-! # Terminal source limits for full kinetic Duhamel slices -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set Filter
open Evolution Occupation
open scoped Topology
variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/-- The kinetic past cylinder is open for an open base domain and continuous motion. -/
theorem isOpen_duhamelCylinder (hΩ : IsOpen Ω) (hγ : Continuous γ) (T : ℝ) :
    IsOpen (evolutionPastOpenCylinder Ω γ T) := by
  have hc : Continuous (fun p : KineticPoint d => p.position - γ p.time) :=
    continuous_position.sub (hγ.comp continuous_time)
  convert (isOpen_lt continuous_time (continuous_const (y := T))).inter (hΩ.preimage hc) using 1
  ext p
  simp only [evolutionPastOpenCylinder, mem_ofPred_eq, mem_inter_iff]
  change (_ ∧ _ ∈ PDE.translateSet (γ p.time) Ω) ↔ _
  rw [PDE.mem_translateSet_iff_sub_mem]
  rfl

/-- The source integrand tends to its terminal datum at every interior terminal state. -/
theorem duhamelSlice_leftLimit (hΩa : IsAdmissibleEvolutionDomain Ω)
    (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K)
    (g : KineticPoint d → ℝ) (hg : Continuous g) (hc : HasCompactSupport g)
    (hs : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × EvolutionAmbientState d =>
      g ⟨q.1, q.2.1, q.2.2⟩)) (T : ℝ)
    (hU : tsupport g ⊆ evolutionPastOpenCylinder Ω γ T)
    (r : ℝ) (w : EvolutionAmbientState d)
    (hw : (KineticPoint.mk r w.1 w.2) ∈ evolutionPastOpenCylinder Ω γ T) :
    Tendsto (fun t => duhamelIntegrand K g ⟨t, w.1, w.2⟩ r)
      (𝓝[<] r) (𝓝 (g ⟨r, w.1, w.2⟩)) := by
  obtain ⟨V, hV, hVe⟩ := exists_duhamelSlice_solution hΩ B b S K hreal g hg hc hs T hU r
  have hopen := isOpen_duhamelCylinder (isOpen_of_isAdmissibleEvolutionDomain hΩa) hγ T
  have hmapc : Continuous (fun t : ℝ => (KineticPoint.mk t w.1 w.2)) :=
    KineticPoint.continuous_mk continuous_id continuous_const continuous_const
  have hcl : (KineticPoint.mk r w.1 w.2) ∈ evolutionPastClosedCylinder Ω γ r :=
    ⟨le_rfl, subset_closure hw.2⟩
  have hev : ∀ᶠ t in 𝓝[<] r,
      (KineticPoint.mk t w.1 w.2) ∈ evolutionPastClosedCylinder Ω γ r := by
    have hn := hmapc.continuousAt.eventually (hopen.mem_nhds hw)
    filter_upwards [hn.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht ht2
    exact ⟨le_of_lt ht2, subset_closure ht.2⟩
  have hmap : Tendsto (fun t => (KineticPoint.mk t w.1 w.2)) (𝓝[<] r)
      (𝓝[evolutionPastClosedCylinder Ω γ r] (KineticPoint.mk r w.1 w.2)) :=
    tendsto_nhdsWithin_iff.2 ⟨(hmapc.tendsto r).mono_left nhdsWithin_le_nhds, hev⟩
  have h1 := (hV.2.1 _ hcl).tendsto.comp hmap
  have ht := hV.2.2.2.2.1 ⟨r, w.1, w.2⟩ ⟨rfl, hcl.2⟩
  change V ⟨r, w.1, w.2⟩ = g ⟨r, w.1, w.2⟩ at ht
  rw [ht] at h1
  refine h1.congr' ?_
  filter_upwards [hev] with t ht
  exact (duhamelIntegrand_eq_slice_solution hΩa K g r V hV.2.2.2.2.2 hVe _ ht).symm

/-- The slice times a compact test has the precise terminal limit, also outside the test support. -/
theorem duhamelSlice_terminalLimit (hΩa : IsAdmissibleEvolutionDomain Ω)
    (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K)
    (g : KineticPoint d → ℝ) (hg : Continuous g) (hc : HasCompactSupport g)
    (hs : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × EvolutionAmbientState d =>
      g ⟨q.1, q.2.1, q.2.2⟩)) (T : ℝ)
    (hU : tsupport g ⊆ evolutionPastOpenCylinder Ω γ T) (C : ℝ)
    (hub : ∀ p r, |duhamelIntegrand K g p r| ≤ C)
    {ψ : EvolutionVec d → ℝ} (hψ : Continuous ψ)
    (hψs : tsupport ψ ⊆ evolutionHomeomorph d ⁻¹' evolutionPastOpenCylinder Ω γ T)
    (r : ℝ) (w : EvolutionAmbientState d) :
    Tendsto (fun t => duhamelIntegrand K g ⟨t, w.1, w.2⟩ r * ψ (packQ d (t, w)))
      (𝓝[<] r) (𝓝 (g ⟨r, w.1, w.2⟩ * ψ (packQ d (r, w)))) := by
  have hψt : Tendsto (fun t => ψ (packQ d (t, w))) (𝓝[<] r)
      (𝓝 (ψ (packQ d (r, w)))) :=
    ((hψ.comp (continuous_packQ.comp (continuous_id.prodMk continuous_const))).tendsto r
      ).mono_left nhdsWithin_le_nhds
  by_cases h0 : ψ (packQ d (r, w)) = 0
  · rw [h0, mul_zero]
    have hb : Tendsto (fun t => C * |ψ (packQ d (t, w))|) (𝓝[<] r) (𝓝 0) := by
      simpa [h0] using hψt.abs.const_mul C
    refine squeeze_zero_norm (fun t => ?_) hb
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hub _ _) (abs_nonneg _)
  · have hw := hψs (subset_closure h0)
    have hp : (KineticPoint.mk r w.1 w.2) ∈ evolutionPastOpenCylinder Ω γ T := by
      simpa only [mem_preimage, evolutionHomeomorph_apply, packQ, timeCoord_packPoint,
        diffusedCoord_packPoint, transportedCoord_packPoint] using hw
    exact (duhamelSlice_leftLimit hΩa hΩ hγ B b S K hreal g hg hc hs T hU r w hp).mul hψt

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

module

public import HypoellipticAleksandrov.KineticAleksandrov.Scaling.Solutions
public import HypoellipticAleksandrov.KineticAleksandrov.Scaling.Pushforward
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Realization
public import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# Transport of the terminal evolution under an affine change of variables

If `(S, K)` realizes the terminal evolution for the data `(Ω, γ, B, b)` and `Φ` is a kinetic
affine scaling with compatible moving domains, then the pushed-forward pair
`(Ŝ, K̂)` (`K̂.master q' = (K.master (Φ q')).map (Φ_{τ'})⁻¹`, `Ŝ` by integration against `K̂`)
realizes the terminal evolution for the rescaled data `(Ω', γ', Φ.coefficient B, Φ.drift b)`.

Every clause of `RealizesTerminalEvolution` is proved by change of variables: classical
solutions transform by the chain rule (`Scaling.Solutions`), uniqueness is inherited from the
original, and endpoint and composition follow from `kernelConj_id`, `kernelConj_comp`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Scaling

open MeasureTheory ProbabilityTheory Set
open HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo (boundedBorel_integrable)
open scoped ENNReal

/-- The terminal operator family obtained by integrating bounded Borel data against the
fibre kernels of `K`. -/
def fiberOperator {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω) : TerminalOperatorFamily Ω γ :=
  fun σ τ hστ =>
    { toFun := fun f =>
        ⟨fun p => ∫ q, f q ∂K.fiberKernel hΩ σ τ hστ p,
          ⟨(StronglyMeasurable.integral_kernel (κ := K.fiberKernel hΩ σ τ hστ)
              f.measurable.stronglyMeasurable).measurable, by
            obtain ⟨C, hC, hb⟩ := f.exists_bound
            refine ⟨C, hC, fun p => ?_⟩
            have : IsFiniteMeasure (K.fiberKernel hΩ σ τ hστ p) :=
              ⟨(K.fiberKernel_mass_le_one hΩ σ τ hστ p).trans_lt ENNReal.one_lt_top⟩
            have h1 := norm_integral_le_of_norm_le_const (μ := K.fiberKernel hΩ σ τ hστ p)
              (f := f) (C := C) (Filter.Eventually.of_forall fun x => by
                simpa only [Real.norm_eq_abs] using hb x)
            have h2 : (K.fiberKernel hΩ σ τ hστ p).real univ ≤ 1 := by
              rw [measureReal_def]
              simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top
                (K.fiberKernel_mass_le_one hΩ σ τ hστ p)
            calc |∫ q, f q ∂K.fiberKernel hΩ σ τ hστ p|
                = ‖∫ q, f q ∂K.fiberKernel hΩ σ τ hστ p‖ := (Real.norm_eq_abs _).symm
              _ ≤ C * (K.fiberKernel hΩ σ τ hστ p).real univ := h1
              _ ≤ C * 1 := by gcongr
              _ = C := mul_one C⟩⟩
      map_add' := by
        intro f g
        apply BoundedBorel.ext
        intro p
        have : IsFiniteMeasure (K.fiberKernel hΩ σ τ hστ p) :=
          ⟨(K.fiberKernel_mass_le_one hΩ σ τ hστ p).trans_lt ENNReal.one_lt_top⟩
        exact integral_add (boundedBorel_integrable f _) (boundedBorel_integrable g _)
      map_smul' := by
        intro c f
        apply BoundedBorel.ext
        intro p
        exact integral_smul c f }

theorem fiberOperator_apply {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω) (σ τ : ℝ) (hστ : σ ≤ τ)
    (f : BoundedBorel (EvolutionState Ω γ τ)) (p : EvolutionState Ω γ σ) :
    fiberOperator K hΩ σ τ hστ f p = ∫ q, f q ∂K.fiberKernel hΩ σ τ hστ p := rfl

namespace KineticAffineScaling

variable {d : ℕ} {Φ : KineticAffineScaling d} {Ω Ω' : Set (PDE.Vec d)}
  {γ γ' : ℝ → PDE.Vec d}

theorem contDiff_ambientSymm (Φ : KineticAffineScaling d) (τ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : EvolutionAmbientState d => (Φ.ambientEquiv τ).symm x) := by
  simp only [ambientEquiv_symm_apply]
  unfold positionInv transportInv
  fun_prop

/-- Terminal data of the rescaled problem come from terminal data of the original one. -/
theorem exists_datum_of_hat (h : Φ.MapsDomain Ω γ Ω' γ') (τ : ℝ)
    (F' : BoundedBorel (EvolutionAmbientState d))
    (hF' : IsSmoothCompactTerminalDatum Ω' γ' τ F') :
    ∃ F : BoundedBorel (EvolutionAmbientState d),
      IsSmoothCompactTerminalDatum Ω γ (Φ.time τ) F ∧
        ∀ x, F' x = F (Φ.ambientEquiv τ x) := by
  refine ⟨F'.pullback (Φ.ambientEquiv τ).symm (Φ.ambientEquiv τ).symm.measurable, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · exact hF'.1.comp (Φ.contDiff_ambientSymm τ)
    · exact hF'.2.1.comp_homeomorph (Φ.ambientHomeo τ).symm
    · intro x hx
      have hx1 := tsupport_comp_subset_preimage (F' : EvolutionAmbientState d → ℝ)
        (Φ.ambientHomeo τ).symm.continuous hx
      have hx' := hF'.2.2 hx1
      have := (h.stateSet_mem_iff τ _).1 hx'
      simpa [Φ.position_positionInv, Φ.transport_transportInv] using this
  · intro x
    simp only [BoundedBorel.pullback_apply, MeasurableEquiv.symm_apply_apply]

/-- The fibre kernels of `K̂` are conjugates of those of `K`. -/
theorem fiberKernel_pushKernel_eq_conj (h : Φ.MapsDomain Ω γ Ω' γ') (K : MovingFiberKernel Ω γ)
    (hΩ : MeasurableSet Ω) (hΩ' : MeasurableSet Ω') (τ τ' : ℝ) (hττ' : τ ≤ τ') :
    (pushKernel h K).fiberKernel hΩ' τ τ' hττ' =
      kernelConj (stateEquiv h τ) (stateEquiv h τ')
        (K.fiberKernel hΩ (Φ.time τ) (Φ.time τ') (Φ.time_le_iff.2 hττ')) := by
  ext p : 1
  rw [kernelConj_apply]
  exact fiberKernel_pushKernel h K hΩ hΩ' τ τ' hττ' p

/-- Integrals against the rescaled fibre kernel are integrals against the original one. -/
theorem integral_fiberKernel_pushKernel (h : Φ.MapsDomain Ω γ Ω' γ')
    (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω) (hΩ' : MeasurableSet Ω')
    (τ τ' : ℝ) (hττ' : τ ≤ τ') (p : EvolutionState Ω' γ' τ)
    (f : EvolutionState Ω' γ' τ' → ℝ) :
    ∫ q, f q ∂(pushKernel h K).fiberKernel hΩ' τ τ' hττ' p =
      ∫ q, f ((stateEquiv h τ').symm q)
        ∂K.fiberKernel hΩ (Φ.time τ) (Φ.time τ') (Φ.time_le_iff.2 hττ') (stateEquiv h τ p) := by
  rw [fiberKernel_pushKernel h K hΩ hΩ' τ τ' hττ' p, integral_map_equiv]

/-- **Realization transport.**  If `(S, K)` realizes the terminal evolution for the data
`(Ω, γ, B, b)` (`Ω` open, `γ` continuous), then `(Ŝ, K̂)` realizes it for the rescaled data
`(Ω', γ', Φ.coefficient B, Φ.drift b)`. -/
theorem realizes_pushKernel (h : Φ.MapsDomain Ω γ Ω' γ') (hΩo : IsOpen Ω)
    (hγ : Continuous γ) (hΩ' : MeasurableSet Ω')
    {B : FullKineticCoefficient d} {b : PDE.Vec d → PDE.Vec d}
    {S : TerminalOperatorFamily Ω γ} {K : MovingFiberKernel Ω γ}
    (hreal : SectionTwo.RealizesTerminalEvolution Ω γ hΩo.measurableSet B b S K) :
    SectionTwo.RealizesTerminalEvolution Ω' γ' hΩ' (Φ.coefficient B) (Φ.drift b)
      (fiberOperator (pushKernel h K) hΩ') (pushKernel h K) := by
  refine ⟨?_, fun σ τ hστ p f => rfl, ?_, ?_⟩
  · intro τ F' hF'
    obtain ⟨F, hF, hFF'⟩ := exists_datum_of_hat h τ F' hF'
    obtain ⟨u, hu, hup, huniq⟩ := hreal.1 (Φ.time τ) F hF
    refine ⟨fun p => u (Φ.point p), ?_, ?_, ?_⟩
    · exact (Φ.isClassicalTerminalSolution_comp_point_iff h hΩo hγ B b τ F F' hFF' u).2 hu
    · intro σ hστ p
      have hlhs : u (Φ.point ⟨σ, p.1.1, p.1.2⟩) =
          u ⟨Φ.time σ, (stateEquiv h σ p).1.1, (stateEquiv h σ p).1.2⟩ := rfl
      beta_reduce
      rw [hlhs, hup (Φ.time σ) (Φ.time_le_iff.2 hστ) (stateEquiv h σ p),
        hreal.2.1 (Φ.time σ) (Φ.time τ) (Φ.time_le_iff.2 hστ) (stateEquiv h σ p),
        fiberOperator_apply, integral_fiberKernel_pushKernel h K hΩo.measurableSet hΩ' σ τ hστ p]
      refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
      change F q.1 = F' ((Φ.ambientEquiv τ).symm q.1)
      rw [hFF', MeasurableEquiv.apply_symm_apply]
    · intro v' hv'
      have hv : IsClassicalTerminalSolution Ω γ B b (Φ.time τ) F
          (fun p => v' (Φ.pointInv p)) := by
        rw [← Φ.isClassicalTerminalSolution_comp_point_iff h hΩo hγ B b τ F F' hFF'
          (fun p => v' (Φ.pointInv p))]
        have : (fun p => (fun p => v' (Φ.pointInv p)) (Φ.point p)) = v' := by
          funext p
          simp only [Φ.pointInv_point]
        rw [this]
        exact hv'
      intro p hp
      have h1 := huniq _ hv ((h.mem_closedCylinder_iff τ p).1 hp)
      simpa only [Φ.pointInv_point] using h1
  · intro σ
    rw [fiberKernel_pushKernel_eq_conj h K hΩo.measurableSet hΩ']
    rw [hreal.2.2.1 (Φ.time σ), kernelConj_id (stateEquiv h σ)]
  · intro σ r τ hσr hrτ
    rw [fiberKernel_pushKernel_eq_conj h K hΩo.measurableSet hΩ' σ τ (hσr.trans hrτ),
      fiberKernel_pushKernel_eq_conj h K hΩo.measurableSet hΩ' r τ hrτ,
      fiberKernel_pushKernel_eq_conj h K hΩo.measurableSet hΩ' σ r hσr,
      hreal.2.2.2 (Φ.time σ) (Φ.time r) (Φ.time τ) (Φ.time_le_iff.2 hσr)
        (Φ.time_le_iff.2 hrτ),
      kernelConj_comp (stateEquiv h σ) (stateEquiv h r) (stateEquiv h τ)]

theorem measurable_evolutionStateShift (Ω : Set (PDE.Vec d)) (γ : ℝ → PDE.Vec d) (σ : ℝ)
    (v : PDE.Vec d) : Measurable (evolutionStateShift Ω γ σ v) := by
  apply Measurable.subtype_mk
  exact (measurable_fst.comp measurable_subtype_coe).prodMk
    ((measurable_snd.comp measurable_subtype_coe).add_const v)

/-- The state change of variables intertwines the shifts of the transported coordinate. -/
theorem stateEquiv_shift (h : Φ.MapsDomain Ω γ Ω' γ') (τ : ℝ) (v : PDE.Vec d)
    (p : EvolutionState Ω' γ' τ) :
    stateEquiv h τ (evolutionStateShift Ω' γ' τ v p) =
      evolutionStateShift Ω γ (Φ.time τ) (Φ.e • v) (stateEquiv h τ p) := by
  apply Subtype.ext
  change (Φ.position p.1.1, Φ.transport τ (p.1.2 + v)) =
    (Φ.position p.1.1, Φ.transport τ p.1.2 + Φ.e • v)
  simp only [transport, Prod.mk.injEq, true_and]
  rw [smul_add]
  abel

/-- **Translation covariance is transported.**  If `K` is translation covariant (the clause
of the terminal evolution after `z`-independence), so is the pushed-forward kernel. -/
theorem isTranslationCovariantEvolution_pushKernel (h : Φ.MapsDomain Ω γ Ω' γ')
    (K : MovingFiberKernel Ω γ) (hΩ : MeasurableSet Ω) (hΩ' : MeasurableSet Ω')
    (hK : SectionTwo.IsTranslationCovariantEvolution Ω γ hΩ K) :
    SectionTwo.IsTranslationCovariantEvolution Ω' γ' hΩ' (pushKernel h K) := by
  intro σ τ hστ v p
  rw [fiberKernel_pushKernel h K hΩ hΩ' σ τ hστ p,
    fiberKernel_pushKernel h K hΩ hΩ' σ τ hστ (evolutionStateShift Ω' γ' σ v p),
    stateEquiv_shift h σ v p, ← hK (Φ.time σ) (Φ.time τ) (Φ.time_le_iff.2 hστ) (Φ.e • v)
      (stateEquiv h σ p),
    Measure.map_map (measurable_evolutionStateShift Ω' γ' τ v) (stateEquiv h τ).symm.measurable,
    Measure.map_map (stateEquiv h τ).symm.measurable
      (measurable_evolutionStateShift Ω γ (Φ.time τ) (Φ.e • v))]
  congr 1
  funext q
  apply (stateEquiv h τ).injective
  simp only [Function.comp_apply, MeasurableEquiv.apply_symm_apply]
  rw [stateEquiv_shift, MeasurableEquiv.apply_symm_apply]

end KineticAffineScaling

end HypoellipticAleksandrov.KineticAleksandrov.Scaling

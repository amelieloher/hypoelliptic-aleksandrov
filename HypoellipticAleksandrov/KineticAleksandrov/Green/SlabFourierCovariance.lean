module

public import HypoellipticAleksandrov.KineticAleksandrov.Scaling.Radius
public import HypoellipticAleksandrov.KineticAleksandrov.Scaling.Unique
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.FourierKernelsTranslation

/-!
# Translation covariance of the realized evolution (Proposition 2.1, item 4)

For a `z`-independent coefficient, the realized kernel is translation covariant in `z`
(`IsTranslationCovariantEvolution`).  Proof: the `z`-translate of `K` (the kinetic affine scaling
`ofRadius 0 0 h 1`) again realizes the terminal evolution of the same data
(`Scaling.realizes_ofRadius_wholeSpace`), so it is `K` by uniqueness
(`Scaling.KineticAffineScaling.realizes_master_eq_map`).
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Green

open MeasureTheory Set
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Scaling
open scoped ENNReal

/-- **Translation covariance from the realization.** -/
theorem isTranslationCovariant_of_realizes {d : ℕ} (B : CoefficientField d)
    (S : TerminalOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (hreal : RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d))
      MeasurableSet.univ (zIndependentCoefficient B) (identityDrift d) S K) :
    IsTranslationCovariantEvolution (wholeSpace d) (fun _ => 0) MeasurableSet.univ K := by
  intro σ τ hστ h0 p
  let r1 : {r : ℝ // 0 < r} := ⟨1, one_pos⟩
  let Φ := KineticAffineScaling.ofRadius (d := d) 0 0 h0 (identityDrift d) r1
  have hmaps : Φ.MapsDomain (wholeSpace d) (fun _ => (0 : PDE.Vec d)) (wholeSpace d)
      (fun _ => (0 : PDE.Vec d)) := KineticAffineScaling.mapsDomain_wholeSpace Φ
  have hB : scaledCoefficient B 0 0 r1 = B := by
    funext t Y
    simp [scaledCoefficient, r1]
  have hreal' : RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d))
      (measurableSet_of_isAdmissibleEvolutionDomain (wholeSpace_admissible d))
      (Φ.coefficient (zIndependentCoefficient B)) (Φ.drift (identityDrift d)) S K := by
    rw [KineticAffineScaling.ofRadius_coefficient, KineticAffineScaling.ofRadius_drift,
      scaledDrift_identity, hB]
    exact hreal
  have hmaster : ∀ q' : EvolutionQuery (wholeSpace d) (fun _ => (0 : PDE.Vec d)),
      K.master q' = (K.master (KineticAffineScaling.queryMap hmaps q')).map
        (Φ.ambientEquiv q'.1.2.1).symm := fun q' =>
    KineticAffineScaling.realizes_master_eq_map hmaps
      (wholeSpace_admissible d) (zeroCurve_piecewiseC1 d) (wholeSpace_admissible d) hreal hreal' q'
  set q' := evolutionQueryOfState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ τ hστ p with hq'
  have hqm : KineticAffineScaling.queryMap hmaps q' =
      evolutionQueryOfState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ τ hστ
        (evolutionStateShift (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ h0 p) := by
    apply Subtype.ext
    simp [KineticAffineScaling.queryMap, KineticAffineScaling.rawQuery, KineticAffineScaling.time,
      KineticAffineScaling.position, KineticAffineScaling.transport, Φ,
      KineticAffineScaling.ofRadius,
      r1, hq', evolutionQueryOfState, evolutionStateShift, evolutionAmbientStateShift,
      identityDrift, add_comm]
  have hM : Measure.map (evolutionAmbientStateShift h0) (K.master q') =
      K.master (evolutionQueryOfState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ τ hστ
        (evolutionStateShift (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ h0 p)) := by
    rw [hmaster q', hqm, Measure.map_map (measurable_evolutionAmbientStateShift h0)
      (Φ.ambientEquiv _).symm.measurable]
    have hid : evolutionAmbientStateShift h0 ∘ (Φ.ambientEquiv (q'.1.2.1)).symm = id := by
      funext x
      simp [evolutionAmbientStateShift, KineticAffineScaling.positionInv,
        KineticAffineScaling.transportInv, Φ, KineticAffineScaling.ofRadius, r1, identityDrift]
    rw [hid, Measure.map_id]
  have hU : MeasurableSet (wholeSpace d) := MeasurableSet.univ
  -- pass from master measures to fibre kernels
  have hemb := MeasurableEmbedding.subtype_coe
    (measurableSet_evolutionStateSet (γ := fun _ => (0 : PDE.Vec d)) hU τ)
  rw [← hemb.comap_map (Measure.map (evolutionStateShift (wholeSpace d) (fun _ => 0) τ h0)
      (K.fiberKernel hU σ τ hστ p)),
    ← hemb.comap_map (K.fiberKernel hU σ τ hστ
      (evolutionStateShift (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ h0 p))]
  congr 1
  rw [Measure.map_map measurable_subtype_coe (measurable_evolutionStateShift _ _ _ _),
    K.map_fiberKernel_eq_master hU σ τ hστ _]
  have hc : ((↑) : EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) τ →
      EvolutionAmbientState d) ∘ evolutionStateShift (wholeSpace d) (fun _ => 0) τ h0 =
      evolutionAmbientStateShift h0 ∘ ((↑) : EvolutionState (wholeSpace d)
        (fun _ => (0 : PDE.Vec d)) τ → EvolutionAmbientState d) := rfl
  rw [hc, ← Measure.map_map (measurable_evolutionAmbientStateShift h0) measurable_subtype_coe,
    K.map_fiberKernel_eq_master hU σ τ hστ p]
  exact hM

end HypoellipticAleksandrov.KineticAleksandrov.Green

module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.ContinuationMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.SourceNotation
import HypoellipticAleksandrov.KineticAleksandrov.Decay.MinorantScaling
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-! # Domination of continued retained measures -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open Set MeasureTheory
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

private theorem le_of_map_subtype_le {d : ℕ} {D : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} {s : ℝ} (hD : MeasurableSet D)
    (μ ν : Measure (EvolutionState D γ s))
    (h : μ.map Subtype.val ≤ ν.map Subtype.val) : μ ≤ ν := by
  let he := MeasurableEmbedding.subtype_coe
    (measurableSet_evolutionStateSet (γ := γ) hD s)
  apply Measure.le_iff.mpr
  intro A hA
  have hh := h (Subtype.val '' A)
  simpa only [he.map_apply, Subtype.coe_injective.preimage_image] using hh

private theorem continued_full_composition {d : ℕ} {D : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (hD : MeasurableSet D) (K : MovingFiberKernel D γ)
    (hcomp : K.HasComposition hD) (σ s T : ℝ) (hσs : σ ≤ s) (hsT : s ≤ T)
    (p : EvolutionState D γ σ) :
    continuedMeasure K hsT (K.fiberKernel hD σ s hσs p) =
      K.master (evolutionQueryOfState D γ σ T (hσs.trans hsT) p) := by
  apply Measure.ext
  intro A hA
  rw [continuedMeasure_apply K hsT _ hA,
    ← K.map_fiberKernel_eq_master hD σ T (hσs.trans hsT) p,
    Measure.map_apply measurable_subtype_coe hA, hcomp σ s T hσs hsT,
    ProbabilityTheory.Kernel.comp_apply' _ _ _ (measurable_subtype_coe hA)]
  apply lintegral_congr
  intro q
  rw [← K.map_fiberKernel_eq_master hD s T hsT q,
    Measure.map_apply measurable_subtype_coe hA]

/-- Continuation in a smaller domain preserves joint domination by the full evolution. -/
theorem continued_measures_dominated {d : ℕ}
    (D D0 : Set (PDE.Vec d)) (hD : MeasurableSet D) (hD0 : MeasurableSet D0)
    (B : CoefficientField d) (b : PDE.Vec d → PDE.Vec d)
    (SD : TerminalOperatorFamily D stationary) (KD : MovingFiberKernel D stationary)
    (S0 : TerminalOperatorFamily D0 stationary) (K0 : MovingFiberKernel D0 stationary)
    (hreal : RealizesTerminalEvolution D stationary hD (zIndependentCoefficient B) b SD KD)
    (hreal0 : RealizesTerminalEvolution D0 stationary hD0 (zIndependentCoefficient B) b S0 K0)
    (hmono : IsDomainMonotoneEvolution D stationary (zIndependentCoefficient B) b KD)
    (hD0adm : IsAdmissibleEvolutionDomain D0) (hsub : D0 ⊆ D)
    (σ s T : ℝ) (hσs : σ ≤ s) (hsT : s ≤ T)
    (qearly qterminal : EvolutionQuery D stationary)
    (hqe : qearly.1.1 = σ ∧ qearly.1.2.1 = s)
    (hqt : qterminal.1 = (σ, T, qearly.1.2.2))
    (R1 R2 : Measure (EvolutionState D0 stationary s))
    [IsFiniteMeasure R1] [IsFiniteMeasure R2]
    (hR : Measure.map Subtype.val R1 + Measure.map Subtype.val R2 ≤ KD.master qearly)
    (E1 E2 : Measure (EvolutionAmbientState d))
    (hE1 : ∀ A, MeasurableSet A → E1 A =
      ∫⁻ p, K0.master (movingQuery s T hsT p.1.1 p.1.2 p.2.1) A ∂R1)
    (hE2 : ∀ A, MeasurableSet A → E2 A =
      ∫⁻ p, K0.master (movingQuery s T hsT p.1.1 p.1.2 p.2.1) A ∂R2) :
    E1 + E2 ≤ KD.master qterminal := by
  let incl : EvolutionState D0 stationary s → EvolutionState D stationary s :=
    fun p => ⟨p.1, by
      simpa only [movingDomain_stationary] using
        hsub (by simpa only [movingDomain_stationary] using p.2.1), p.2.2⟩
  have hincl : Measurable incl := measurable_subtype_coe.subtype_mk
  let R := (R1 + R2).map incl
  let p : EvolutionState D stationary σ :=
    ⟨qearly.1.2.2, by simpa only [← hqe.1] using qearly.2.2⟩
  have hqearly : evolutionQueryOfState D stationary σ s hσs p = qearly := by
    apply Subtype.ext
    exact Prod.ext hqe.1.symm (Prod.ext hqe.2.symm rfl)
  have hqterminal : evolutionQueryOfState D stationary σ T (hσs.trans hsT) p =
      qterminal := Subtype.ext hqt.symm
  have hRfull : R ≤ KD.fiberKernel hD σ s hσs p := by
    apply le_of_map_subtype_le hD
    rw [KD.map_fiberKernel_eq_master hD σ s hσs p, hqearly]
    dsimp only [R]
    rw [Measure.map_map measurable_subtype_coe hincl]
    change (R1 + R2).map Subtype.val ≤ KD.master qearly
    rw [Measure.map_add _ _ measurable_subtype_coe]
    exact hR
  have hsubs : ∀ r, movingDomain D0 stationary r ⊆ movingDomain D stationary r := by
    intro r v hv
    simpa only [movingDomain_stationary] using
      hsub (by simpa only [movingDomain_stationary] using hv)
  have hdom := domainMonotone_of_realizes (zIndependentCoefficient B) b KD hmono
    D0 stationary hD0adm (zeroCurve_piecewiseC1 d) hsubs S0 K0 hreal0
  have hle : continuedMeasure K0 hsT (R1 + R2) ≤ continuedMeasure KD hsT R := by
    apply Measure.le_iff.mpr
    intro A hA
    rw [continuedMeasure_apply K0 hsT _ hA, continuedMeasure_apply KD hsT R hA]
    dsimp only [R]
    change _ ≤ ∫⁻ q, continuationKernel KD hsT q A ∂(R1 + R2).map incl
    rw [lintegral_map ((continuationKernel KD hsT).measurable_coe hA) hincl]
    apply lintegral_mono
    intro q
    exact hdom (evolutionQueryOfState D0 stationary s T hsT q) A
  rw [eq_continuedMeasure_of_apply K0 hsT R1 hE1,
    eq_continuedMeasure_of_apply K0 hsT R2 hE2,
    ← continuedMeasure_add]
  calc
    _ ≤ continuedMeasure KD hsT R := hle
    _ ≤ continuedMeasure KD hsT (KD.fiberKernel hD σ s hσs p) :=
      continuedMeasure_mono KD hsT hRfull
    _ = KD.master qterminal := by
      rw [continued_full_composition hD KD hreal.2.2.2, hqterminal]

end HypoellipticAleksandrov.KineticAleksandrov.Decay

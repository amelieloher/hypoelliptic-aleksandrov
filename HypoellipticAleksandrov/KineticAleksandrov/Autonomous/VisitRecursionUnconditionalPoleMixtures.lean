module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalMixtures
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripRestartPoles
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripKernelIntegral

/-! # Exact physical visit mixtures on the finite-union pole carrier used by nested strips -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory

/-- Pull back an actual physical source to the existing finite-union pole subtype. -/
def visitUnionPoleMeasure (H : FiniteIntervalUnion) (T : ℝ) (mu : Measure Point) :
    Measure (FiniteUnionPole H (T : WithTop ℝ)) := mu.comap Subtype.val

/-- Pullback to physical poles preserves finite source mass. -/
instance visitUnionPoleMeasure_isFiniteMeasure (H : FiniteIntervalUnion) (T : ℝ)
    (mu : Measure Point) [IsFiniteMeasure mu] : IsFiniteMeasure (visitUnionPoleMeasure H T mu) := by
  unfold visitUnionPoleMeasure
  infer_instance

/-- Mapping the union poles back recovers the entire supported physical source. -/
theorem visitUnionPoleMeasure_map (H : FiniteIntervalUnion) (s T : ℝ) (mu : Measure Point)
    (hmu : ∀ᵐ p ∂mu, p ∈ visitPoleSet H s T) :
    (visitUnionPoleMeasure H T mu).map Subtype.val = mu := by
  apply visitPoleMeasure_map_comap _ (measurableSet_finiteUnionPole H T)
  exact hmu.mono fun p hp => ⟨WithTop.coe_lt_coe.mpr hp.2.1, hp.2.2⟩

/-- The lifted actual source has the strict lower-time support of the corrected nested theorem. -/
theorem visitUnionPoleMeasure_ae_time_gt (H : FiniteIntervalUnion) (s T : ℝ)
    (mu : Measure Point) (hmu : ∀ᵐ p ∂mu, p ∈ visitPoleSet H s T) :
    ∀ᵐ e ∂visitUnionPoleMeasure H T mu, s < e.1.time := by
  have ht := hmu.mono (fun p hp => hp.1)
  rw [← visitUnionPoleMeasure_map H s T mu hmu] at ht
  exact ((MeasurableEmbedding.subtype_coe (measurableSet_finiteUnionPole H T)).ae_map_iff).mp ht

/-- Any actual union-pole family has the same mixture as its strict physical zero extension. -/
theorem visitExtendKernel_comp_unionPole (H : FiniteIntervalUnion) (s T : ℝ)
    (f : FiniteUnionPole H (T : WithTop ℝ) → Measure Point) (hf : Measurable f)
    (mu : Measure Point) (hmu : ∀ᵐ p ∂mu, p ∈ visitPoleSet H s T) :
    visitExtendKernel (visitPoleSet H s T) (measurableSet_visitPoleSet H s T)
      (fun p => f (visitPoleInclusion H s T p)) (hf.comp (measurable_visitPoleInclusion H s T))
      ∘ₘ mu = (visitUnionPoleMeasure H T mu).bind f := by
  classical
  let nu := visitUnionPoleMeasure H T mu
  let k := visitExtendKernel (visitPoleSet H s T) (measurableSet_visitPoleSet H s T)
    (fun p => f (visitPoleInclusion H s T p)) (hf.comp (measurable_visitPoleInclusion H s T))
  have hm : nu.map Subtype.val = mu := visitUnionPoleMeasure_map H s T mu hmu
  have hb := nested_bind_map nu Subtype.val measurable_subtype_coe k k.measurable
  change mu.bind k = nu.bind f
  rw [← hm]
  apply hb.trans
  apply Measure.bind_congr_right
  filter_upwards [visitUnionPoleMeasure_ae_time_gt H s T mu hmu] with e he
  have hp : e.1 ∈ visitPoleSet H s T :=
    ⟨he, WithTop.coe_lt_coe.mp e.2.1, e.2.2⟩
  have hi : visitPoleInclusion H s T ⟨e.1, hp⟩ = e := Subtype.ext rfl
  change (if ht : e.1 ∈ visitPoleSet H s T then
    f (visitPoleInclusion H s T ⟨e.1, ht⟩) else 0) = f e
  rw [dite_eq_left hp, hi]

/-- The actual physical Green composition is exactly the nested theorem's Green mixture. -/
theorem visitUnionGreenKernel_comp_poles
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (s T : ℝ) (mu : Measure Point)
    (hmu : ∀ᵐ p ∂mu, p ∈ visitPoleSet H s T) :
    visitUnionGreenKernel hH hLE hlam hLam A H s T ∘ₘ mu =
      finiteUnionGreenMixture hH hLE hlam hLam A H T (visitUnionPoleMeasure H T mu) :=
  visitExtendKernel_comp_unionPole H s T _ (finiteUnionGreen_measurable hH hLE hlam hLam A H T)
    mu hmu

/-- The actual physical exit composition is exactly the nested theorem's exit mixture. -/
theorem visitUnionExitKernel_comp_poles
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (s T : ℝ) (mu : Measure Point)
    (hmu : ∀ᵐ p ∂mu, p ∈ visitPoleSet H s T) :
    visitUnionExitKernel hH hLE hlam hLam A H s T ∘ₘ mu =
      finiteUnionExitMixture hH hLE hlam hLam A H T (visitUnionPoleMeasure H T mu) :=
  visitExtendKernel_comp_unionPole H s T _ (finiteUnionExit_measurable hH hLE hlam hLam A H T)
    mu hmu

/-- Including source poles into the larger union retains exactly their physical measure. -/
theorem visitUnionPoleMeasure_nested_map (H1 H2 : FiniteIntervalUnion)
    (hsub : H1.carrier ⊆ H2.carrier) (s T : ℝ) (mu : Measure Point)
    (hmu : ∀ᵐ p ∂mu, p ∈ visitPoleSet H1 s T) :
    ((visitUnionPoleMeasure H1 T mu).map
      (finiteUnionNestedPoleInclusion H1 H2 hsub T)).map Subtype.val = mu := by
  rw [Measure.map_map measurable_subtype_coe
    (measurable_finiteUnionNestedPoleInclusion H1 H2 hsub T)]
  exact visitUnionPoleMeasure_map H1 s T mu hmu

/-- Mapping smaller source poles into the larger domain is exactly the larger pole pullback. -/
theorem visitUnionPoleMeasure_nested_eq (H1 H2 : FiniteIntervalUnion)
    (hsub : H1.carrier ⊆ H2.carrier) (s T : ℝ) (mu : Measure Point)
    (hmu : ∀ᵐ p ∂mu, p ∈ visitPoleSet H1 s T) :
    (visitUnionPoleMeasure H1 T mu).map (finiteUnionNestedPoleInclusion H1 H2 hsub T) =
      visitUnionPoleMeasure H2 T mu := by
  apply (MeasurableEmbedding.subtype_coe (measurableSet_finiteUnionPole H2 T)).map_injective
  have hlarge : ∀ᵐ p ∂mu, p ∈ visitPoleSet H2 s T :=
    hmu.mono (fun p hp => ⟨hp.1, hp.2.1, hsub hp.2.2⟩)
  exact (visitUnionPoleMeasure_nested_map H1 H2 hsub s T mu hmu).trans
    (visitUnionPoleMeasure_map H2 s T mu hlarge).symm

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

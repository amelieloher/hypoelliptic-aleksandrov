module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripSourceRestart
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FiniteUnionDomainsMass
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripKernelIntegral

/-! # The genuine internal restart measure on larger interval poles -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open scoped ENNReal

/-- The larger-interval restart measure is the subtype pullback of the actual restricted exit. -/
def nestedIntervalRestartPoles
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : Interval) (sMinus T : ℝ)
    (e : StripPole H1 (T : WithTop ℝ)) : Measure (StripPole H2 (T : WithTop ℝ)) :=
  ((stripExit hH hLE hlam hLam A H1 T e).restrict
    (nestedIntervalInternalExit H1 H2 sMinus T)).comap Subtype.val

/-- The actual restart pole measure is finite. -/
instance nestedIntervalRestartPoles_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : Interval) (sMinus T : ℝ)
    (e : StripPole H1 (T : WithTop ℝ)) :
    IsFiniteMeasure (nestedIntervalRestartPoles hH hLE hlam hLam A H1 H2 sMinus T e) := by
  unfold nestedIntervalRestartPoles
  infer_instance

/-- The finite pole predicate for an interval is a Borel set in physical coordinates. -/
theorem measurableSet_nestedIntervalPole (H : Interval) (T : ℝ) :
    MeasurableSet {p : Point | (p.time : WithTop ℝ) < T ∧ p.velocity 0 ∈ H.carrier} := by
  convert (isOpen_stripPast H T).measurableSet using 1
  ext p
  exact and_congr WithTop.coe_lt_coe Iff.rfl

/-- The restart poles recover precisely the actual smaller exit restricted to the internal face. -/
theorem nestedIntervalRestartPoles_map
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : Interval) (sMinus T : ℝ)
    (e : StripPole H1 (T : WithTop ℝ)) :
    (nestedIntervalRestartPoles hH hLE hlam hLam A H1 H2 sMinus T e).map Subtype.val =
      (stripExit hH hLE hlam hLam A H1 T e).restrict
        (nestedIntervalInternalExit H1 H2 sMinus T) := by
  unfold nestedIntervalRestartPoles
  refine (map_comap_subtype_coe (measurableSet_nestedIntervalPole H2 T) _).trans ?_
  apply Measure.restrict_eq_self_of_ae_mem
  filter_upwards [ae_restrict_mem
    (measurableSet_nestedIntervalInternalExit H1 H2 sMinus T)] with p hp
  exact ⟨WithTop.coe_lt_coe.mpr hp.2.1, hp.2.2.2⟩

/-- Genuine restart poles retain the strict lower-time support of the internal face. -/
theorem nestedIntervalRestartPoles_ae_time_gt
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : Interval) (sMinus T : ℝ)
    (e : StripPole H1 (T : WithTop ℝ)) :
    ∀ᵐ ep ∂nestedIntervalRestartPoles hH hLE hlam hLam A H1 H2 sMinus T e,
      sMinus < ep.1.time := by
  have ht : ∀ᵐ p ∂(stripExit hH hLE hlam hLam A H1 T e).restrict
      (nestedIntervalInternalExit H1 H2 sMinus T), sMinus < p.time := by
    filter_upwards [ae_restrict_mem
      (measurableSet_nestedIntervalInternalExit H1 H2 sMinus T)] with p hp
    exact hp.1
  rw [← nestedIntervalRestartPoles_map hH hLE hlam hLam A H1 H2 sMinus T e] at ht
  exact ((MeasurableEmbedding.subtype_coe (measurableSet_nestedIntervalPole H2 T)).ae_map_iff).mp ht

/-- The larger Green mixture of internal restart poles is the actual measurable measure bind. -/
def nestedIntervalRestartGreen
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : Interval) (sMinus T : ℝ)
    (e : StripPole H1 (T : WithTop ℝ)) : Measure Point :=
  (nestedIntervalRestartPoles hH hLE hlam hLam A H1 H2 sMinus T e).bind
    (stripGreen hH hLE hlam hLam A H2 T)

/-- Uniform interval geometry makes the actual restart Green mixture finite. -/
instance nestedIntervalRestartGreen_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : Interval) (sMinus T : ℝ)
    (e : StripPole H1 (T : WithTop ℝ)) :
    IsFiniteMeasure (nestedIntervalRestartGreen hH hLE hlam hLam A H1 H2 sMinus T e) := by
  let τ := nestedIntervalRestartPoles hH hLE hlam hLam A H1 H2 sMinus T e
  let C := finiteUnionGreenMassBound lam H2.toFiniteUnion
  have hb (ep : StripPole H2 (T : WithTop ℝ)) :
      stripGreen hH hLE hlam hLam A H2 T ep univ ≤ C := by
    let i : Fin H2.toFiniteUnion.count := ⟨0, by change 0 < 1; omega⟩
    have h := finiteUnionGreen_mass_le hH hLE hlam hLam A H2.toFiniteUnion T
      (componentPoleInclusion H2.toFiniteUnion i T ep)
    have hc := congrArg (fun ρ : Measure Point => ρ univ)
      (finiteUnionGreen_component hH hLE hlam hLam A H2.toFiniteUnion i T ep)
    exact hc ▸ h
  constructor
  change τ.bind (stripGreen hH hLE hlam hLam A H2 T) univ < ⊤
  rw [Measure.bind_apply MeasurableSet.univ]
  · apply (lintegral_mono hb).trans_lt
    rw [lintegral_const]
    exact ENNReal.mul_lt_top
      (lt_top_iff_ne_top.mpr (finiteUnionGreenMassBound_ne_top lam H2.toFiniteUnion))
      (measure_lt_top τ univ)
  · exact (Measure.measurable_measure.mpr (fun B hB =>
      stripGreen_measurable_apply hH hLE hlam hLam A H2 T B hB)).aemeasurable

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

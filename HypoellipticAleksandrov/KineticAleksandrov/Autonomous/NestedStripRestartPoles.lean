module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripRestart

/-! # The internal-exit measure on the existing larger-strip pole carrier -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- The finite-horizon pole predicate is Borel in physical coordinates. -/
theorem measurableSet_finiteUnionPole (H : FiniteIntervalUnion) (T : ℝ) :
    MeasurableSet {p : Point | (p.time : WithTop ℝ) < T ∧ p.velocity 0 ∈ H.carrier} := by
  have ht : {p : Point | (p.time : WithTop ℝ) < T} = {p | p.time < T} := by
    ext p
    exact WithTop.coe_lt_coe
  rw [show {p : Point | (p.time : WithTop ℝ) < T ∧ p.velocity 0 ∈ H.carrier} =
    {p | (p.time : WithTop ℝ) < T} ∩ {p | p.velocity 0 ∈ H.carrier} from rfl, ht]
  exact (measurableSet_lt continuous_time.measurable measurable_const).inter
    (H.isOpen_carrier.measurableSet.preimage
      ((continuous_apply 0).comp continuous_velocity).measurable)

/-- The restart measure on valid larger-strip poles is the actual subtype pullback. -/
def finiteUnionRestartPoleMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : FiniteIntervalUnion) (sMinus T : ℝ)
    (nu : Measure (FiniteUnionPole H1 (T : WithTop ℝ))) :
    Measure (FiniteUnionPole H2 (T : WithTop ℝ)) :=
  (finiteUnionRestartMeasure hH hLE hlam hLam A H1 H2 sMinus T nu).comap Subtype.val

/-- Subtype pullback preserves finiteness of the internal-exit measure. -/
instance finiteUnionRestartPoleMeasure_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : FiniteIntervalUnion) (sMinus T : ℝ)
    (nu : Measure (FiniteUnionPole H1 (T : WithTop ℝ))) [IsFiniteMeasure nu] :
    IsFiniteMeasure (finiteUnionRestartPoleMeasure hH hLE hlam hLam A H1 H2 sMinus T nu) := by
  unfold finiteUnionRestartPoleMeasure
  infer_instance

/-- Returning the restart poles to physical coordinates recovers exactly the internal exits. -/
theorem finiteUnionRestartPoleMeasure_map
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : FiniteIntervalUnion) (sMinus T : ℝ)
    (nu : Measure (FiniteUnionPole H1 (T : WithTop ℝ))) :
    (finiteUnionRestartPoleMeasure hH hLE hlam hLam A H1 H2 sMinus T nu).map
      Subtype.val = finiteUnionRestartMeasure hH hLE hlam hLam A H1 H2 sMinus T nu := by
  unfold finiteUnionRestartPoleMeasure
  refine (map_comap_subtype_coe (measurableSet_finiteUnionPole H2 T)
    (finiteUnionRestartMeasure hH hLE hlam hLam A H1 H2 sMinus T nu)).trans ?_
  apply Measure.restrict_eq_self_of_ae_mem
  filter_upwards [finiteUnionRestartMeasure_ae_valid hH hLE hlam hLam A H1 H2 sMinus T nu]
    with p hp
  exact ⟨WithTop.coe_lt_coe.mpr hp.2.1, hp.2.2⟩

/-- Restart poles inherit the strict open-strip lower-time support. -/
theorem finiteUnionRestartPoleMeasure_ae_time_gt
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : FiniteIntervalUnion) (sMinus T : ℝ)
    (nu : Measure (FiniteUnionPole H1 (T : WithTop ℝ))) :
    ∀ᵐ e ∂finiteUnionRestartPoleMeasure hH hLE hlam hLam A H1 H2 sMinus T nu,
      sMinus < e.1.time := by
  have ht : ∀ᵐ p ∂finiteUnionRestartMeasure hH hLE hlam hLam A H1 H2 sMinus T nu,
      sMinus < p.time :=
    (finiteUnionRestartMeasure_ae_valid hH hLE hlam hLam A H1 H2 sMinus T nu).mono
      (fun _ hp => hp.1)
  rw [← finiteUnionRestartPoleMeasure_map hH hLE hlam hLam A H1 H2 sMinus T nu] at ht
  exact ((MeasurableEmbedding.subtype_coe
    (measurableSet_finiteUnionPole H2 T)).ae_map_iff).mp ht

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

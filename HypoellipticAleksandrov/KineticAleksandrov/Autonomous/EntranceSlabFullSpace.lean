module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EntranceSlabOccupation
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VelocityReturnAction
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationFiniteBounds
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedVisitMassCapacity

/-! # Literal full-space active-band masses in physical time slabs -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory HypoellipticAleksandrov
open scoped ENNReal

/-- Full-space terminal measures are finite in physical spacetime. -/
instance entranceSlab_fullSpaceTerminal_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (P : Point) (b : ℝ) :
    IsFiniteMeasure (enlargedFullSpaceTerminal hH hLE hlam hLam A P b) := by
  exact ⟨(enlargedFullSpaceTerminal_mass_le_one hH hLE hlam hLam A P b).trans_lt
    ENNReal.one_lt_top⟩

/-- Full-space occupation on a finite observation window is a finite physical measure. -/
instance entranceSlab_fullSpaceOccupation_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (P : Point) (T : ℝ) :
    IsFiniteMeasure (enlargedFullSpaceOccupation hH hLE hlam hLam A P T) := by
  unfold enlargedFullSpaceOccupation
  infer_instance

/-- Reinserting physical time does not change the active-velocity terminal probability. -/
theorem entranceSlab_fullSpaceTerminal_active
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (P : Point) (b : ℝ) :
    enlargedFullSpaceTerminal hH hLE hlam hLam A P (P.time + b)
      {q | q.velocity 0 ∈ c.active} =
      kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal b)
        (P.position 0, P.velocity 0) {z | z.2 ∈ c.active} := by
  have hB : MeasurableSet {q : Point | q.velocity 0 ∈ c.active} :=
    isOpen_Ioo.measurableSet.preimage
      ((continuous_apply 0).comp continuous_velocity).measurable
  have he := Measure.map_apply
    (μ := kernelXV (fullSpaceEvolution hH hLE hlam hLam A)
      (Real.toNNReal (P.time + b - P.time)) (P.position 0, P.velocity 0))
    (enlargedTerminalPoint_measurable (P.time + b)) hB
  have ht : P.time + b - P.time = b := by ring
  rw [ht] at he
  unfold enlargedFullSpaceTerminal
  rw [ht]
  exact he

/-- Physical time-slab occupation is exactly the elapsed active-band kernel integral. -/
theorem entranceSlab_fullSpaceOccupation_active
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (P : Point) (T a b : ℝ)
    (ha : 0 ≤ a) (hbT : b ≤ T) :
    enlargedFullSpaceOccupation hH hLE hlam hLam A P T
      {q | q.time ∈ Ioc (P.time + a) (P.time + b) ∧ q.velocity 0 ∈ c.active} =
      ∫⁻ t in Ioc a b,
        kernelXV (fullSpaceEvolution hH hLE hlam hLam A) (Real.toNNReal t)
          (P.position 0, P.velocity 0) {z | z.2 ∈ c.active} := by
  let B : Set Point :=
    {q | q.time ∈ Ioc (P.time + a) (P.time + b) ∧ q.velocity 0 ∈ c.active}
  let V : Set Z := {z | z.2 ∈ c.active}
  have hB : MeasurableSet B :=
    (measurableSet_Ioc.preimage continuous_time.measurable).inter
      (isOpen_Ioo.measurableSet.preimage
        ((continuous_apply 0).comp continuous_velocity).measurable)
  have hV : MeasurableSet V := isOpen_Ioo.measurableSet.preimage measurable_snd
  let K := fun t : ℝ => kernelXV (fullSpaceEvolution hH hLE hlam hLam A)
    (Real.toNNReal t) (P.position 0, P.velocity 0)
  have hi (t : ℝ) : (∫⁻ z, B.indicator 1
      (enlargedTerminalPoint (P.time + t) z) ∂K t) =
      (Ioc a b).indicator (fun t => K t V) t := by
    have ht : P.time + t ∈ Ioc (P.time + a) (P.time + b) ↔ t ∈ Ioc a b := by
      simp only [mem_Ioc, add_lt_add_iff_left, add_le_add_iff_left]
    by_cases h : t ∈ Ioc a b
    · have htime := ht.mpr h
      rw [indicator_of_mem h]
      have he : (fun z => B.indicator (1 : Point → ℝ≥0∞)
          (enlargedTerminalPoint (P.time + t) z)) = V.indicator 1 := by
        funext z
        have hm : enlargedTerminalPoint (P.time + t) z ∈ B ↔ z ∈ V := by
          change (P.time + t ∈ Ioc (P.time + a) (P.time + b) ∧ z.2 ∈ c.active) ↔
            z.2 ∈ c.active
          exact and_iff_right htime
        by_cases hz : z ∈ V
        · rw [indicator_of_mem (hm.mpr hz), indicator_of_mem hz]
          rfl
        · rw [indicator_of_notMem (mt hm.mp hz), indicator_of_notMem hz]
      rw [he, lintegral_indicator_one hV]
    · have htime := mt ht.mp h
      rw [indicator_of_notMem h]
      have he : (fun z => B.indicator (1 : Point → ℝ≥0∞)
          (enlargedTerminalPoint (P.time + t) z)) = 0 := by
        funext z
        have hm : enlargedTerminalPoint (P.time + t) z ∉ B := by
          intro hp
          exact htime hp.1
        rw [indicator_of_notMem hm]
        rfl
      rw [he, lintegral_zero_fun]
  change enlargedFullSpaceOccupation hH hLE hlam hLam A P T B =
    ∫⁻ t in Ioc a b, K t V
  calc
    _ = ∫⁻ q, B.indicator 1 q
        ∂enlargedFullSpaceOccupation hH hLE hlam hLam A P T :=
      (lintegral_indicator_one hB).symm
    _ = ∫⁻ t in Ioc 0 T, ∫⁻ z, B.indicator 1
        (enlargedTerminalPoint (P.time + t) z) ∂K t :=
      enlargedFullSpaceOccupation_lintegral hH hLE hlam hLam A P T
        (B.indicator 1) (measurable_const.indicator hB)
    _ = ∫⁻ t in Ioc 0 T, (Ioc a b).indicator (fun t => K t V) t :=
      lintegral_congr hi
    _ = _ := by
      rw [lintegral_indicator measurableSet_Ioc,
        Measure.restrict_restrict measurableSet_Ioc,
        inter_eq_left.mpr (show Ioc a b ⊆ Ioc 0 T from
          fun _ ht => ⟨ha.trans_lt ht.1, ht.2.trans hbT⟩)]

/-- The real physical slab mass is exactly the source active-velocity action integral. -/
theorem entranceSlab_fullSpaceOccupation_active_real
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (P : Point) (T a b : ℝ)
    (ha : 0 ≤ a) (hbT : b ≤ T) :
    (enlargedFullSpaceOccupation hH hLE hlam hLam A P T
      {q | q.time ∈ Ioc (P.time + a) (P.time + b) ∧ q.velocity 0 ∈ c.active}).toReal =
      ∫ t in Ioc a b,
        S hH hLE hlam hLam A t (activeVelocityDatum c) (P.position 0, P.velocity 0) := by
  let E := fullSpaceEvolution hH hLE hlam hLam A
  let z : Z := (P.position 0, P.velocity 0)
  let B : Set Z := {w | w.2 ∈ c.active}
  let f := fun t : ℝ => kernelXV E (Real.toNNReal t) z B
  have hf : Measurable f :=
    (physicalElapsedKernel E z).measurable_coe (isOpen_Ioo.measurableSet.preimage measurable_snd)
  have hfinite (t : ℝ) : f t < ⊤ :=
    ((measure_mono (subset_univ B)).trans (kernelXV_mass_le_one E (Real.toNNReal t) z)).trans_lt
      ENNReal.one_lt_top
  have hi : (∫ t in Ioc a b, (f t).toReal) = (∫⁻ t in Ioc a b, f t).toReal :=
    integral_toReal hf.aemeasurable (Filter.Eventually.of_forall hfinite)
  have hS : (∫ t in Ioc a b,
      S hH hLE hlam hLam A t (activeVelocityDatum c) z) = ∫ t in Ioc a b, (f t).toReal := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact activeVelocityDatum_action_eq hH hLE hlam hLam A c t (ha.trans ht.1.le) z
  have he := congrArg ENNReal.toReal
    (entranceSlab_fullSpaceOccupation_active hH hLE hlam hLam A c P T a b ha hbT)
  exact he.trans (hi.symm.trans hS.symm)

/-- The actual source active-band action is integrable on every nonnegative finite slab. -/
theorem entranceSlab_activeAction_integrableOn
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (z : Z) (a b : ℝ) (ha : 0 ≤ a) :
    IntegrableOn (fun t => S hH hLE hlam hLam A t (activeVelocityDatum c) z) (Ioc a b) := by
  let E := fullSpaceEvolution hH hLE hlam hLam A
  let B : Set Z := {w | w.2 ∈ c.active}
  have hm : Measurable (fun t : ℝ => kernelXV E (Real.toNNReal t) z B) :=
    (physicalElapsedKernel E z).measurable_coe (isOpen_Ioo.measurableSet.preimage measurable_snd)
  have hi : IntegrableOn (fun t => (kernelXV E (Real.toNNReal t) z B).toReal)
      (Ioc a b) := by
    apply Integrable.mono' (integrable_const (1 : ℝ)) hm.ennreal_toReal.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun t => by
      rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
      simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top
        ((measure_mono (subset_univ B)).trans (kernelXV_mass_le_one E (Real.toNNReal t) z))
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact (activeVelocityDatum_action_eq hH hLE hlam hLam A c t (ha.trans ht.1.le) z).symm

/-- The real finite occupation sum is bounded by the literal source active-band integral. -/
theorem entranceSlab_partial_occupation_mass_le
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T a b : ℝ)
    (hT : 0 < T) (ha : 0 ≤ a) (hbT : b ≤ T) (hJ : closure c.active ⊆ J.carrier)
    (P : Point) (hv : P.velocity 0 ∈ J.carrier) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      ((enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) (P.time + b) ∘ₘ
        (enlargedVisitEntrance hH hLE hlam hLam A c J P.time (P.time + T) P n).restrict
          {p | p.time ∈ Ioc (P.time + a) (P.time + b)}) univ).toReal) ≤
      ∫ t in Ioc a b,
        S hH hLE hlam hLam A t (activeVelocityDatum c) (P.position 0, P.velocity 0) := by
  let gm := fun n => enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J)
    (P.time + b) ∘ₘ
      (enlargedVisitEntrance hH hLE hlam hLam A c J P.time (P.time + T) P n).restrict
        {p | p.time ∈ Ioc (P.time + a) (P.time + b)}
  have : ∀ n, IsFiniteMeasure (gm n) := fun n =>
    entranceSlabGreen_isFiniteMeasure hH hLE hlam hLam A c J (P.time + a) (P.time + b) _
      ((ae_restrict_mem (measurableSet_Ioc.preimage continuous_time.measurable)).mono
        fun _ hp => hp.1.le)
  have hm := entranceSlab_partial_occupation_le_fullspace
    hH hLE hlam hLam A c J T a b hT hbT hJ P hv N
  have hr := ENNReal.toReal_mono (measure_ne_top _ univ) (hm univ)
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter,
    entranceSlab_fullSpaceOccupation_active_real hH hLE hlam hLam A c P T a b ha hbT] at hr
  rw [visit_partial_real_mass gm N univ MeasurableSet.univ] at hr
  exact hr

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

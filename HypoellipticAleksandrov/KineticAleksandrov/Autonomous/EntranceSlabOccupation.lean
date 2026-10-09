module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EntranceSlabHorizon
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonGreenSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionOccupation

/-! # Localized occupation domination for starts in a time slab -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory HypoellipticAleksandrov

/-- Restricting starts and shortening the horizon can only decrease actual occupation. -/
theorem entranceSlab_greenMixture_le
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (b T : ℝ)
    (hBT : b ≤ T) (mu : Measure Point) (D : Set Point) :
    enlargedVisitGreenKernel hH hLE hlam hLam A H b ∘ₘ mu.restrict D ≤
      enlargedVisitGreenKernel hH hLE hlam hLam A H T ∘ₘ mu := by
  let G := enlargedVisitGreenKernel hH hLE hlam hLam A H b
  let GT := enlargedVisitGreenKernel hH hLE hlam hLam A H T
  apply Measure.le_iff.mpr
  intro B hB
  rw [Measure.bind_apply hB G.aemeasurable, Measure.bind_apply hB GT.aemeasurable]
  apply lintegral_mono' Measure.restrict_le_self
  intro p
  exact ((entranceSlab_greenKernel_horizon_le hH hLE hlam hLam A H b T hBT p).trans
    Measure.restrict_le_self) B


/-- An active Green kernel lives strictly between its starting time and its horizon. -/
theorem entranceSlab_greenKernel_ae_support
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ)
    (hJ : closure c.active ⊆ J.carrier) (p : Point) :
    ∀ᵐ q ∂enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b p,
      p.time < q.time ∧ q.time < b ∧ q.velocity 0 ∈ c.active := by
  classical
  rw [enlarged_activeUnion_eq c J hJ]
  change ∀ᵐ q ∂(if hp : p ∈ enlargedVisitPoleSet c.activeInterval.toFiniteUnion b then
    finiteUnionGreen hH hLE hlam hLam A c.activeInterval.toFiniteUnion b
      (enlargedVisitPole _ b ⟨p, hp⟩) else 0), _
  split
  · rename_i hp
    have hv : p.velocity 0 ∈ c.activeInterval.carrier := by
      simpa only [Interval.toFiniteUnion_carrier] using hp.2
    let e : StripPole c.activeInterval ⊤ := ⟨p, WithTop.coe_lt_top _, hv⟩
    change ∀ᵐ q ∂stripGreen hH hLE hlam hLam A c.activeInterval b
      (stripPoleFinite c.activeInterval e b hp.1), _
    rw [stripGreen_finite_restrict_infinite hH hLE hlam hLam A c.activeInterval e b hp.1]
    have hf := (stripGreen_infinite_ae_future_carrier
      hH hLE hlam hLam A c.activeInterval e).filter_mono
        (ae_mono (Measure.restrict_le_self (s := {q | q.time < b})))
    have ht : ∀ᵐ q ∂(stripGreen hH hLE hlam hLam A c.activeInterval ⊤ e).restrict
        {q | q.time < b}, q.time < b :=
      ae_restrict_mem (isOpen_lt continuous_time continuous_const).measurableSet
    filter_upwards [hf, ht] with q hq hqt
    exact ⟨hq.1, hqt, hq.2⟩
  · simp only [ae_zero, Filter.eventually_bot]

/-- New starts in `(a,b]` produce occupation only in that same physical slab and active band. -/
theorem entranceSlab_greenMixture_ae_support
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (a b : ℝ)
    (hJ : closure c.active ⊆ J.carrier) (mu : Measure Point) :
    ∀ᵐ q ∂(enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b ∘ₘ
      mu.restrict {p | p.time ∈ Ioc a b}),
      q.time ∈ Ioc a b ∧ q.velocity 0 ∈ c.active := by
  apply Measure.ae_comp_of_ae_ae
    ((measurableSet_Ioc.preimage continuous_time.measurable).inter
      (isOpen_Ioo.measurableSet.preimage
        ((continuous_apply 0).comp continuous_velocity).measurable))
  filter_upwards [ae_restrict_mem
    (measurableSet_Ioc.preimage continuous_time.measurable)] with p hp
  exact (entranceSlab_greenKernel_ae_support hH hLE hlam hLam A c J b hJ p).mono
    fun q hq => ⟨⟨hp.1.trans hq.1, hq.2.1.le⟩, hq.2.2⟩

/-- Localized active occupation is bounded by the same slab of the actual full occupation. -/
theorem entranceSlab_greenMixture_le_restrict
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (a b T : ℝ)
    (hBT : b ≤ T) (hJ : closure c.active ⊆ J.carrier) (mu : Measure Point) :
    enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b ∘ₘ
      mu.restrict {p | p.time ∈ Ioc a b} ≤
      (enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) T ∘ₘ mu).restrict
        {q | q.time ∈ Ioc a b ∧ q.velocity 0 ∈ c.active} := by
  have hle := Measure.restrict_mono (subset_refl
    {q : Point | q.time ∈ Ioc a b ∧ q.velocity 0 ∈ c.active})
      (entranceSlab_greenMixture_le hH hLE hlam hLam A (visitActiveUnion c J) b T hBT
        mu {p | p.time ∈ Ioc a b})
  have heq : (enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b ∘ₘ
      mu.restrict {p | p.time ∈ Ioc a b}).restrict
        {q | q.time ∈ Ioc a b ∧ q.velocity 0 ∈ c.active} =
      enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b ∘ₘ
        mu.restrict {p | p.time ∈ Ioc a b} :=
    Measure.restrict_eq_self_of_ae_mem
      (entranceSlab_greenMixture_ae_support hH hLE hlam hLam A c J a b hJ mu)
  exact heq.symm.le.trans hle

/-- Every finite canonical sum of new-start occupations inherits full-space slab domination. -/
theorem entranceSlab_partial_occupation_le_fullspace
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (T a b : ℝ)
    (hT : 0 < T) (hbT : b ≤ T) (hJ : closure c.active ⊆ J.carrier)
    (P : Point) (hv : P.velocity 0 ∈ J.carrier) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) (P.time + b) ∘ₘ
        (enlargedVisitEntrance hH hLE hlam hLam A c J P.time (P.time + T) P n).restrict
          {p | p.time ∈ Ioc (P.time + a) (P.time + b)}) ≤
      (enlargedFullSpaceOccupation hH hLE hlam hLam A P T).restrict
        {q | q.time ∈ Ioc (P.time + a) (P.time + b) ∧ q.velocity 0 ∈ c.active} := by
  let S : Set Point :=
    {q | q.time ∈ Ioc (P.time + a) (P.time + b) ∧ q.velocity 0 ∈ c.active}
  let gm := enlargedActivePiece hH hLE hlam hLam A c J P.time (P.time + T) P
  have he : ∀ N : ℕ, (∑ n ∈ Finset.range N, (gm n).restrict S) =
      (∑ n ∈ Finset.range N, gm n).restrict S := by
    intro N
    induction N with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, Measure.restrict_zero]
    | succ N ih => rw [Finset.sum_range_succ, Finset.sum_range_succ,
        Measure.restrict_add, ih]
  have hle := Finset.sum_le_sum (s := Finset.range N) (fun n _ =>
    entranceSlab_greenMixture_le_restrict hH hLE hlam hLam A c J
      (P.time + a) (P.time + b) (P.time + T) (by linarith only [hbT]) hJ
      (enlargedVisitEntrance hH hLE hlam hLam A c J P.time (P.time + T) P n))
  exact hle.trans ((he N).le.trans (Measure.restrict_mono (subset_refl S)
    (enlarged_active_occupation_le_fullspace hH hLE hlam hLam A c J T hT P hv N)))

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

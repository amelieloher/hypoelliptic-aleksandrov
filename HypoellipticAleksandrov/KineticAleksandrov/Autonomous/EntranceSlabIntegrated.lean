module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EntranceSlabKernel

/-! # Integrated quadratic counting for starts in a closed-right time slab -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory HypoellipticAleksandrov

/-- A lower time bound makes the clipped active occupation of any finite start measure finite. -/
theorem entranceSlabGreen_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (a b : ℝ)
    (mu : Measure Point) [IsFiniteMeasure mu] (ha : ∀ᵐ p ∂mu, a ≤ p.time) :
    IsFiniteMeasure
      (enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b ∘ₘ mu) := by
  rw [enlargedVisitGreen_comp_eq_clipped hH hLE hlam hLam A (visitActiveUnion c J) a b mu ha]
  infer_instance

/-- Finite mixtures of starts up to `b` obey the exact actual terminal/occupation identity. -/
theorem entranceSlabQuadratic_integrated_identity
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (a b : ℝ)
    (hJ : closure c.active ⊆ J.carrier) (mu : Measure Point) [IsFiniteMeasure mu]
    (hmu : ∀ᵐ p ∂mu, a ≤ p.time ∧ p.time ≤ b ∧
      p.velocity 0 ∈ (visitActiveUnion c J).carrier) :
    (∫ p, visitQuadratic c (p.velocity 0) ∂mu) =
      (∫ q, visitQuadratic c (q.velocity 0)
        ∂mu.bind (enlargedActiveTerminalFamily hH hLE hlam hLam A c J b)) +
      ∫ q, 2 * A.a (q.position 0) (q.velocity 0)
        ∂(enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b ∘ₘ mu) := by
  let K := entranceSlabTerminalKernel hH hLE hlam hLam A c J b
  let G := enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b
  let f := fun p : Point => visitQuadratic c (p.velocity 0)
  let g := fun p : Point => 2 * A.a (p.position 0) (p.velocity 0)
  have : IsFiniteMeasure (G ∘ₘ mu) := entranceSlabGreen_isFiniteMeasure
    hH hLE hlam hLam A c J a b mu (hmu.mono fun _ hp => hp.1)
  have hK : Integrable f (K ∘ₘ mu) :=
    entranceSlabTerminal_quadratic_integrable hH hLE hlam hLam A c J b mu
  have hG : Integrable g (G ∘ₘ mu) := visitCoefficient_integrable hlam A _
  have hiK : Integrable (fun p => ∫ q, f q ∂K p) mu := by
    rw [Measure.comp_eq_comp_const_apply] at hK
    simpa only [Kernel.const_apply] using hK.integral_comp
  have hiG : Integrable (fun p => ∫ q, g q ∂G p) mu := by
    rw [Measure.comp_eq_comp_const_apply] at hG
    simpa only [Kernel.const_apply] using hG.integral_comp
  have hp : f =ᵐ[mu] fun p => (∫ q, f q ∂K p) + ∫ q, g q ∂G p := by
    filter_upwards [hmu] with p hp
    exact entranceSlabQuadratic_closed_point_identity
      hH hLE hlam hLam A c J b hJ p hp.2.1 hp.2.2
  change (∫ p, f p ∂mu) = (∫ q, f q ∂K ∘ₘ mu) + ∫ q, g q ∂G ∘ₘ mu
  rw [integral_congr_ae hp, integral_add hiK hiG]
  rw [nested_integral_bind mu K K.measurable f hK,
    nested_integral_bind mu G G.measurable g hG]

/-- The exact source quadratic bounds starts by their actual terminal and clipped occupation. -/
theorem entranceSlabQuadratic_mass_bound
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (a b : ℝ)
    (hJ : closure c.active ⊆ J.carrier) (mu : Measure Point) [IsFiniteMeasure mu]
    (hmu : ∀ᵐ p ∂mu, a ≤ p.time ∧ p.time ≤ b ∧ p.velocity 0 ∈ closure c.entrance) :
    5 * c.r ^ 2 / 16 * (mu univ).toReal ≤
      9 * c.r ^ 2 / 16 *
        (mu.bind (enlargedActiveTerminalFamily hH hLE hlam hLam A c J b)
          {q | q.velocity 0 ∈ c.active}).toReal +
      2 * Lam *
        ((enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b ∘ₘ mu)
          univ).toReal := by
  have : IsFiniteMeasure
      (enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b ∘ₘ mu) :=
    entranceSlabGreen_isFiniteMeasure hH hLE hlam hLam A c J a b mu
      (hmu.mono fun _ hp => hp.1)
  have hi := entranceSlabQuadratic_integrated_identity hH hLE hlam hLam A c J a b hJ mu
    (hmu.mono fun _ hp => ⟨hp.1, hp.2.1, by
      rw [visitActiveUnion_carrier]
      have hv := enlarged_closedEntrance_subset_active c hp.2.2
      exact ⟨hv, hJ (subset_closure hv)⟩⟩)
  have hm := entranceSlabQuadratic_mass_lower c mu (hmu.mono fun _ hp => hp.2.2)
  rw [hi] at hm
  have ht' := entranceSlabQuadratic_integral_le_active c
    (mu.bind (enlargedActiveTerminalFamily hH hLE hlam hLam A c J b))
    (entranceSlabTerminal_quadratic_integrable hH hLE hlam hLam A c J b mu)
  exact hm.trans (add_le_add ht' (visitCoefficient_integral_le hlam A _))

/-- Finite canonical slab counts satisfy the source quadratic estimate without a past-mass term. -/
theorem entranceSlabQuadratic_partial_mass_bound
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (s T : ℝ)
    (P : Point) (hs : s ≤ P.time) (hT : P.time < T)
    (hJ : closure c.active ⊆ J.carrier) (a b : ℝ) (N : ℕ) :
    let mu := fun n => (enlargedVisitEntrance hH hLE hlam hLam A c J s T P n).restrict
      {p | p.time ∈ Ioc a b}
    5 * c.r ^ 2 / 16 * (∑ n ∈ Finset.range N, (mu n univ).toReal) ≤
      9 * c.r ^ 2 / 16 * (∑ n ∈ Finset.range N,
        ((mu n).bind (enlargedActiveTerminalFamily hH hLE hlam hLam A c J b)
          {q | q.velocity 0 ∈ c.active}).toReal) +
      2 * Lam * (∑ n ∈ Finset.range N,
        ((enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b ∘ₘ mu n)
          univ).toReal) := by
  dsimp only
  let mu := fun n => (enlargedVisitEntrance hH hLE hlam hLam A c J s T P n).restrict
    {p | p.time ∈ Ioc a b}
  have hm (n : ℕ) : ∀ᵐ p ∂mu n,
      a ≤ p.time ∧ p.time ≤ b ∧ p.velocity 0 ∈ closure c.entrance := by
    have hv : ∀ᵐ p ∂mu n, p.velocity 0 ∈ closure c.entrance :=
      ((enlargedVisitEntrance_ae_support
      hH hLE hlam hLam A c J s T P hs hT n).mono fun _ hp => hp.2.2).filter_mono
        (ae_mono Measure.restrict_le_self)
    have ht : ∀ᵐ p ∂mu n, p.time ∈ Ioc a b :=
      ae_restrict_mem (measurableSet_Ioc.preimage continuous_time.measurable)
    filter_upwards [ht, hv] with p hp hvel
    exact ⟨hp.1.le, hp.2, hvel⟩
  have h := Finset.sum_le_sum (s := Finset.range N) (fun n _ =>
    entranceSlabQuadratic_mass_bound hH hLE hlam hLam A c J a b hJ (mu n) (hm n))
  simpa only [Finset.mul_sum, Finset.sum_add_distrib] using h

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreStartBandVisits
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationStatement
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FarVelocityDensityDomination

/-! # The source core-start band estimate in an arbitrary observation velocity strip -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory
open scoped ENNReal

/-- A literal bounded outer interval containing both closed velocity intervals. -/
def coreStartOuterInterval (H : Interval) (c : Clock) : Interval where
  lo := min H.lo c.activeInterval.lo - 1
  hi := max H.hi c.activeInterval.hi + 1
  ordered := by
    have hl := min_le_left H.lo c.activeInterval.lo
    have hh := le_max_left H.hi c.activeInterval.hi
    linarith [H.ordered]

/-- The observation interval lies inside the chosen bounded outer interval. -/
theorem coreStartOuterInterval_contains (H : Interval) (c : Clock) :
    H.carrier ⊆ (coreStartOuterInterval H c).carrier := by
  intro v hv
  change min H.lo c.activeInterval.lo - 1 < v ∧ v < max H.hi c.activeInterval.hi + 1
  constructor
  · linarith [hv.1, min_le_left H.lo c.activeInterval.lo]
  · linarith [hv.2, le_max_left H.hi c.activeInterval.hi]

/-- The closed active interval lies strictly inside the chosen bounded outer interval. -/
theorem coreStartOuterInterval_contains_active (H : Interval) (c : Clock) :
    closure c.active ⊆ (coreStartOuterInterval H c).carrier := by
  change closure (Ioo c.activeInterval.lo c.activeInterval.hi) ⊆ _
  rw [closure_Ioo c.activeInterval.ordered.ne]
  intro v hv
  change min H.lo c.activeInterval.lo - 1 < v ∧ v < max H.hi c.activeInterval.hi + 1
  constructor
  · linarith [hv.1, min_le_right H.lo c.activeInterval.lo]
  · linarith [hv.2, le_max_right H.hi c.activeInterval.hi]

/-- The improved core-start norm is uniform in all positions and starting times in the strip. -/
theorem below_four_core_start_band (hpush : PushforwardStatement)
    (htail : RestartTailStatement) (hvisits : PositionVisitsStatement)
    (hmasses : PositionVisitMassesStatement) (hcore : CoreDominationStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (alpha q : ℝ)
    (ha : enlargedAdmissibleAlpha lam Lam hlam hLam alpha) (hq : 1 < q ∧ q < 3 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock)
      (H : Interval) (s R : ℝ) (_hR : 0 < R)
      (e : StripPole H ((s + R ^ 2 : ℝ) : WithTop ℝ)),
      s ≤ e.1.time → e.1.velocity 0 ∈ closure c.entrance →
      |c.vbar| = 2 * c.r → c.r ≤ 6 * R →
      ∃ G : Point → ℝ, Measurable G ∧ (∀ z, 0 ≤ G z) ∧
        (stripGreen hH hLE hlam hLam A H (s + R ^ 2) e).restrict
          {z | z.velocity 0 ∈ c.core} =
            volume.withDensity (fun z => ENNReal.ofReal (G z)) ∧
        MemLp G (ENNReal.ofReal q) volume ∧
        (eLpNorm G (ENNReal.ofReal q) volume).toReal ≤
          (C * R ^ (6 - 4 * q) *
            (c.r / R) ^ (4 - 3 * q + (1 - alpha) * (q - 1))) ^ (1 / q) := by
  obtain ⟨C, hC, hd⟩ := core_start_visit_density hpush htail hvisits hmasses
    hH hLE hlam hLam alpha q ha hq
  refine ⟨C, hC, ?_⟩
  intro A c H s R hR e hs he hc hr
  let J := coreStartOuterInterval H c
  let T := s + R ^ 2 - e.1.time
  have ht : 0 < T := sub_pos.mpr (WithTop.coe_lt_coe.mp e.2.1)
  have htR : T ≤ R ^ 2 := by dsimp [T]; linarith
  have hJ := coreStartOuterInterval_contains_active H c
  obtain ⟨G, hG, hG0, hGd, hGp, hGn⟩ := hd A c J R T e.1 hR ht htR hc hr hJ he
  have hsub := coreStartOuterInterval_contains H c
  let ep := stripEnlargePole H J hsub (s + R ^ 2) (s + R ^ 2) le_rfl e
  have hh := hcore hH hLE lam Lam hlam hLam A c J e.1.time (s + R ^ 2) e.1
    ⟨WithTop.coe_lt_coe.mp e.2.1, hsub e.2.2⟩ hc hJ le_rfl
  have heq : e.1.time + T = s + R ^ 2 := by dsimp [T]; ring
  have hnu : visitsFromZero hH hLE hlam hLam A c J T e.1 =
      enlargedVisitStarts hH hLE hlam hLam A c J e.1.time (s + R ^ 2) e.1 := by
    unfold visitsFromZero
    rw [heq]
  rw [hnu] at hGd
  have hle := (Measure.restrict_mono_measure
    (stripGreen_mono hH hLE hlam hLam A H J hsub
      (s + R ^ 2) (s + R ^ 2) le_rfl e) {z | z.velocity 0 ∈ c.core}).trans hh.2
  have hdle := hle.trans Measure.restrict_le_self
  rw [hGd] at hdle
  have : SigmaFinite (volume : Measure Point) := density_volume_sigmaFinite
  obtain ⟨g, hgm, hg0, hgd, hgp, hgn⟩ := density_of_le_withDensity volume
    ((stripGreen hH hLE hlam hLam A H (s + R ^ 2) e).restrict
      {z | z.velocity 0 ∈ c.core}) G hG hG0 (ENNReal.ofReal q) hGp hdle
  exact ⟨g, hgm, hg0, hgd, hgp,
    (ENNReal.toReal_mono hGp.ne hgn).trans hGn⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

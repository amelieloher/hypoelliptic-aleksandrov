module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EvolutionInstance
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.Green

/-! # Physical strip Green measures

Poles have valid time order and interior velocity. The measure is the physical-coordinate
image of the uniquely characterized Green measure, for finite or infinite horizons.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal

/-- A valid physical pole; no value is assigned to an invalid source point. -/
abbrev StripPole (H : Interval) (T : WithTop ℝ) :=
  {e : Point // (e.time : WithTop ℝ) < T ∧ e.velocity 0 ∈ H.carrier}

/-- The elapsed horizon of a valid pole. -/
def stripHorizon (T : WithTop ℝ) (s : ℝ) : ℝ≥0∞ :=
  match T with
  | ⊤ => ⊤
  | (t : ℝ) => ENNReal.ofReal (t - s)

/-- Valid poles have strictly positive elapsed horizons. -/
theorem stripHorizon_pos (H : Interval) (T : WithTop ℝ) (e : StripPole H T) :
    0 < stripHorizon T e.1.time := by
  cases T with
  | top => exact ENNReal.zero_lt_top
  | coe t =>
    apply ENNReal.ofReal_pos.mpr
    exact sub_pos.mpr (WithTop.coe_lt_coe.mp e.2.1)

/-- The pole's native state, with physical velocity first. -/
def stripPoleState (H : Interval) (T : WithTop ℝ) (e : StripPole H T) :
    EvolutionState (intervalDomain H) (fun _ => 0) e.1.time :=
  ⟨(e.1.velocity, e.1.position), by
    refine ⟨?_, mem_univ _⟩
    apply PDE.mem_translateSet_iff_sub_mem.mpr
    simpa only [sub_zero, intervalDomain, PDE.mem_oneDimensionalAxisBox_iff,
      Interval.carrier, mem_Ioo, PDE.vecOneCoordinate] using e.2.2⟩

/-- Restore absolute time and physical position-velocity order. -/
def elapsedPhysicalPoint (s : ℝ) {R : ℝ≥0∞}
    (q : ElapsedTime R × EvolutionAmbientState 1) : Point :=
  ⟨s + q.1.1, q.2.2, q.2.1⟩

/-- The elapsed-to-physical coordinate map is Borel. -/
theorem measurable_elapsedPhysicalPoint (s : ℝ) (R : ℝ≥0∞) :
    Measurable (elapsedPhysicalPoint s (R := R)) := by
  exact (KineticPoint.measurable_equivProd_symm 1).comp
    ((measurable_const.add (measurable_subtype_coe.comp measurable_fst)).prodMk
      ((measurable_snd.comp measurable_snd).prodMk
        (measurable_fst.comp measurable_snd)))

/-- The physical Green measure of a supplied killed kernel, uniquely fixed by its action. -/
def stripGreenOfKernel (H : Interval) (K : MovingFiberKernel (intervalDomain H) (fun _ => 0))
    (T : WithTop ℝ) (e : StripPole H T) : Measure Point :=
  (greenMeasure K e.1.time (stripHorizon T e.1.time) (stripHorizon_pos H T e)
    (Measure.dirac (stripPoleState H T e))).map (elapsedPhysicalPoint e.1.time)

/-- The canonical autonomous Green measure uses the unique autonomous evolution. -/
def stripGreen
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (T : WithTop ℝ)
    (e : StripPole H T) : Measure Point :=
  stripGreenOfKernel H (stripEvolution hH hLE hlam hLam A H).2 T e

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

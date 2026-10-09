module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockExtensionsAssembly
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EvolutionInstance

/-! # The unique actual normalized case-I killed evolution of the position clock -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution

/-- The fixed normalized active interval, with the source's exact endpoints. -/
def clockNormalizedInterval : Interval := ⟨-3 / 4, 3 / 4, by norm_num⟩

/-- Realization of the literal globally extended normalized coefficient and drift. -/
def IsClockEvolution {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point)
    (E : StripEvolution clockNormalizedInterval) : Prop :=
  RealizesTerminalEvolution (intervalDomain clockNormalizedInterval) (fun _ => 0)
    (intervalDomain_measurable clockNormalizedInterval)
    (zIndependentCoefficient (c.extendedCoefficient lam A.a e)) c.extendedVectorDrift E.1 E.2

/-- The normalized clock setting produces an actual killed evolution through the
  full-coefficient existence theorem. -/
theorem exists_clockEvolution
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) :
    ∃ E : StripEvolution clockNormalizedInterval, IsClockEvolution A c e E := by
  have hs := c.extended_sourceSetting hlam hLam A e
  obtain ⟨hBs, hBsym, hBell⟩ := sectionTwoCoefficient_fullBounds (3 * lam / 5) (3 * Lam)
    (c.extendedCoefficient lam A.a e) hs.1
  obtain ⟨S, K, hc, -, -, -, -, hi, -, -, -, -, he, hcomp, -, -, -⟩ :=
    exists_terminalEvolution_of_classical hLE hH 1 (by omega) (3 * lam / 5) (3 * Lam)
      (9 / 25) 9 (by positivity) (by linarith) (by norm_num) (by norm_num)
      (intervalDomain clockNormalizedInterval) (fun _ => 0)
      (zIndependentCoefficient (c.extendedCoefficient lam A.a e)) c.extendedVectorDrift
      (intervalDomain_admissible clockNormalizedInterval) (zeroCurve_piecewiseC1 1)
      hBs hBsym hBell hs.2.1 hs.2.2.2.2.1.1 hs.2.2.2.2.1.2
  exact ⟨(S, K), hc, hi, he, hcomp⟩

/-- The normalized realization is unique among all genuine realizing pairs. -/
theorem clockEvolution_unique {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (c : Clock) (e : Point) (E E' : StripEvolution clockNormalizedInterval)
    (hE : IsClockEvolution A c e E) (hE' : IsClockEvolution A c e E') : E = E' := by
  obtain ⟨hS, hK⟩ := terminalEvolution_unique (intervalDomain clockNormalizedInterval)
    (fun _ => 0) (intervalDomain_admissible clockNormalizedInterval)
    (zIndependentCoefficient (c.extendedCoefficient lam A.a e)) c.extendedVectorDrift
    E.1 E'.1 E.2 E'.2 hE hE'
  exact Prod.ext hS hK

/-- Existence and uniqueness precede the canonical normalized family. -/
theorem existsUnique_clockEvolution
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) :
    ∃! E : StripEvolution clockNormalizedInterval, IsClockEvolution A c e E := by
  obtain ⟨E, hE⟩ := exists_clockEvolution hH hLE hlam hLam A c e
  exact ⟨E, hE, fun E' hE' => clockEvolution_unique A c e E' E hE' hE⟩

/-- The actual normalized clock evolution, selected only from its proved unique characterization. -/
def clockEvolution
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) :
    StripEvolution clockNormalizedInterval :=
  (existsUnique_clockEvolution hH hLE hlam hLam A c e).exists.choose

/-- The selected clock pair realizes exactly the extended case-I coefficient and drift. -/
theorem clockEvolution_spec
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) :
    IsClockEvolution A c e (clockEvolution hH hLE hlam hLam A c e) :=
  (existsUnique_clockEvolution hH hLE hlam hLam A c e).exists.choose_spec

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockGreenTestSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Interval.Green
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripGreen

/-! # The actual normalized infinite Green measure of the position clock -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution Green
open scoped ENNReal NNReal

/-- The starting state for the normalized killed evolution has normalized transported coordinate
  zero. -/
def clockInitialState (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active) :
    EvolutionState (intervalDomain clockNormalizedInterval) (fun _ => 0) 0 :=
  ⟨((fun _ => (e.velocity 0 - c.vbar) / c.r), fun _ => 0), by
    refine ⟨?_, mem_univ _⟩
    change (fun _ : Fin 1 => (e.velocity 0 - c.vbar) / c.r) ∈
      movingDomain (intervalDomain clockNormalizedInterval) (fun _ => 0) 0
    rw [mem_movingDomain_iff, sub_zero, intervalDomain, PDE.mem_oneDimensionalAxisBox_iff]
    exact (c.mem_active_iff (e.velocity 0)).mp he⟩

/-- The normalized Green carrier measure is obtained from the actual, uniquely realized
  evolution. -/
def clockNativeGreen
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active) :
    Measure (GreenCarrier 1) :=
  greenMeasure (clockEvolution hH hLE hlam hLam A c e).2 0 ⊤ (by simp)
    (Measure.dirac (clockInitialState c e he))

/-- The normalized physical Green measure uses the established elapsed-to-physical coordinate
  map. -/
def clockGreen
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active) :
    Measure Point :=
  (clockNativeGreen hH hLE hlam hLam A c e he).map (elapsedPhysicalPoint 0)

/-- The actual normalized carrier measure has the exact canonical Green characterization. -/
theorem clockNativeGreen_spec
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active) :
    IsGreenMeasure (clockEvolution hH hLE hlam hLam A c e).2 0 ⊤
      (Measure.dirac (clockInitialState c e he))
      (clockNativeGreen hH hLE hlam hLam A c e he) :=
  greenMeasure_spec _ 0 ⊤ (by simp) _

/-- The landed interval theorem gives a uniform density for the actual normalized clock Green.
The constant depends only on ellipticity and the exponent, not on the clock or coefficient jets. -/
theorem clockNativeGreen_density
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (q : ℝ) (hq : 1 < q) (hq2 : q < (3 : ℝ) / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point)
      (he : e.velocity 0 ∈ c.active),
      ∃ G : GreenCarrier 1 → ℝ≥0∞, Measurable G ∧
        clockNativeGreen hH hLE hlam hLam A c e he = (greenLebesgue 1).withDensity G ∧
        eLpNorm G (ENNReal.ofReal q) (greenLebesgue 1) ≤ ENNReal.ofReal C ∧
        clockNativeGreen hH hLE hlam hLam A c e he univ < ⊤ := by
  obtain ⟨C, hC, hc⟩ := Interval.interval_green_density hH hLE
    (3 * lam / 5) (3 * Lam) (9 / 25) 9 (3 / 2)
    (by positivity) (by linarith) (by norm_num) (by norm_num) (by norm_num) q hq hq2
  refine ⟨C, hC, ?_⟩
  intro A c e he
  obtain ⟨G, hm, hd, hn, hf⟩ := @hc (-3 / 4) (3 / 4) (by norm_num)
    (c.extendedCoefficient lam A.a e) c.extendedVectorDrift
    (c.extended_sourceSetting hlam hLam A e)
    (intervalDomain_measurable clockNormalizedInterval)
    (clockEvolution hH hLE hlam hLam A c e).1
    (clockEvolution hH hLE hlam hLam A c e).2
    (clockEvolution_spec hH hLE hlam hLam A c e) (by norm_num) 0
    (Measure.dirac (clockInitialState c e he)) isFiniteMeasure_dirac
    (clockNativeGreen hH hLE hlam hLam A c e he)
    (clockNativeGreen_spec hH hLE hlam hLam A c e he)
  have hm1 : (Measure.dirac (clockInitialState c e he)) univ = 1 :=
    Measure.dirac_apply_of_mem (mem_univ _)
  exact ⟨G, hm, hd, hn.trans (le_of_eq ((congrArg (fun x : ℝ≥0∞ => ENNReal.ofReal C * x) hm1).trans
    (mul_one _))), hf⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

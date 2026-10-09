module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.IntegratedVelocitySource
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.IntegratedVelocityMeasure
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! # Full-space Green measure in raw elapsed-time coordinates -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set MeasureTheory Filter
open SectionTwo
open scoped ENNReal

/-- Actual native initial state corresponding to a physical point. -/
def velocityInitialState (z : Z) : EvolutionState autonomousWholeDomain (fun _ => 0) 0 :=
  ⟨(wholeQuery 0 z).1.2.2, (wholeQuery 0 z).2.2⟩

/-- Actual finite-horizon occupation measure. -/
def velocityGreen (E : FullSpaceEvolution) (T : ℝ) (hT : 0 < T) (z : Z) :
    Measure (ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState 1) :=
  greenMeasure E.2 0 (ENNReal.ofReal T) (ENNReal.ofReal_pos.mpr hT)
    (Measure.dirac (velocityInitialState z))

/-- Finite-horizon occupation has mass at most the elapsed horizon. -/
theorem velocityGreen_mass_le (E : FullSpaceEvolution) (T : ℝ) (hT : 0 < T) (z : Z) :
    velocityGreen E T hT z univ ≤ ENNReal.ofReal T := by
  have h := greenMeasure_timeMarginal_le E.2 0 (ENNReal.ofReal T)
    (Measure.dirac (velocityInitialState z)) (velocityGreen E T hT z)
    (greenMeasure_spec E.2 0 _ _ _) univ MeasurableSet.univ
  simpa only [preimage_univ, Measure.dirac_apply_of_mem (mem_univ _), one_mul,
    elapsedVolume_univ T hT] using h

/-- Finite-horizon occupation is a finite measure. -/
instance velocityGreen_isFiniteMeasure (E : FullSpaceEvolution) (T : ℝ)
    (hT : 0 < T) (z : Z) : IsFiniteMeasure (velocityGreen E T hT z) :=
  ⟨(velocityGreen_mass_le E T hT z).trans_lt ENNReal.ofReal_lt_top⟩

/-- Remove only the elapsed-time subtype; spatial coordinates remain native. -/
def velocityElapsedRaw {T : ℝ}
    (q : ElapsedTime (ENNReal.ofReal T) × EvolutionAmbientState 1) :
    ℝ × EvolutionAmbientState 1 := (q.1.1, q.2)

/-- The raw elapsed-coordinate map is measurable. -/
theorem velocityElapsedRaw_measurable (T : ℝ) :
    Measurable (velocityElapsedRaw (T := T)) :=
  (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd

/-- Occupation measure on the ambient finite-dimensional raw coordinates. -/
def velocityGreenRaw (E : FullSpaceEvolution) (T : ℝ) (hT : 0 < T) (z : Z) :
    Measure (ℝ × EvolutionAmbientState 1) :=
  (velocityGreen E T hT z).map velocityElapsedRaw

/-- Raw occupation is finite. -/
instance velocityGreenRaw_isFiniteMeasure (E : FullSpaceEvolution) (T : ℝ)
    (hT : 0 < T) (z : Z) : IsFiniteMeasure (velocityGreenRaw E T hT z) := by
  unfold velocityGreenRaw
  infer_instance

/-- Every raw occupation point lies strictly before the terminal time. -/
theorem velocityGreenRaw_restrict_past (E : FullSpaceEvolution) (T : ℝ)
    (hT : 0 < T) (z : Z) :
    (velocityGreenRaw E T hT z).restrict {q | q.1 < T} = velocityGreenRaw E T hT z := by
  apply Measure.restrict_eq_self_of_ae_mem
  change ∀ᵐ q ∂(velocityGreen E T hT z).map velocityElapsedRaw, q.1 < T
  apply (ae_map_iff (velocityElapsedRaw_measurable T).aemeasurable
    (measurableSet_lt measurable_fst measurable_const)).2
  exact Eventually.of_forall fun q => (ENNReal.ofReal_lt_ofReal_iff hT).mp q.1.2.2

/-- The compact convex-source bound holds for its literal raw Green integral. -/
theorem velocityGreenRaw_source_integral_le (hH : HormanderHypoellipticityStatement)
    {lam Lam r T : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (hr : 0 < r) (hT : 0 < T) (z : Z)
    (f : ℝ × EvolutionAmbientState 1 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ {q | q.1 < T})
    (hf01 : ∀ q, 0 ≤ f q ∧ f q ≤ 1) :
    (∫ q, f q * (lam * velocityOccupationDensity r (q.2.1 0))
      ∂velocityGreenRaw E T hT z) ≤ Real.sqrt (2 * Lam * T) := by
  let g := fun q : Point => f (q.time, q.position, q.velocity) *
    (lam * velocityOccupationDensity r (q.position 0))
  have hs : ContDiff ℝ (⊤ : ℕ∞) (rawLift g) := hf.mul
    (contDiff_const.mul ((velocityOccupationDensity_contDiff hr).comp
      ((contDiff_apply ℝ ℝ 0).comp contDiff_snd.fst)))
  have hc : HasCompactSupport g :=
    (hfc.comp_homeomorph (KineticPoint.homeomorphProd 1)).mul_right
  have hg : Continuous g := hs.continuous.comp (KineticPoint.homeomorphProd 1).continuous
  have hn : ∀ q, 0 ≤ g q := fun q => mul_nonneg (hf01 _).1
    (mul_nonneg hlam.le (velocityOccupationDensity_nonneg r _))
  have hrep := duhamelPotential_eq_greenMeasure E.2 autonomousWholeDomain_measurable
    continuous_const T g hn hg hc 0 hT (velocityInitialState z)
  have hb := velocity_profile_source_bound hH hlam hLam A E hE hr T f hf hfc hfU hf01
    ⟨0, fun _ => z.2, fun _ => z.1⟩ hT
  change (∫ q, rawLift g q ∂(velocityGreen E T hT z).map velocityElapsedRaw) ≤ _
  rw [integral_map (velocityElapsedRaw_measurable T).aemeasurable
    hs.continuous.aestronglyMeasurable]
  have hI (D : ℝ) (hD : 0 < D) (hDT : D = T) :
      (∫ q : ElapsedTime (ENNReal.ofReal D) × EvolutionAmbientState 1,
        g ⟨0 + q.1.1, q.2.1, q.2.2⟩ ∂greenMeasure E.2 0 (ENNReal.ofReal D)
          (ENNReal.ofReal_pos.mpr hD) (Measure.dirac (velocityInitialState z))) =
      ∫ q, rawLift g (velocityElapsedRaw q) ∂velocityGreen E T hT z := by
    subst D
    apply integral_congr_ae
    exact Eventually.of_forall fun q => by
      change g ⟨0 + q.1.1, q.2.1, q.2.2⟩ = g ⟨q.1.1, q.2.1, q.2.2⟩
      rw [show (0 : ℝ) + q.1.1 = q.1.1 by ring]
  have hi := (hI (T - 0) (sub_pos.mpr hT) (by ring)).symm.trans hrep.symm
  exact hi.trans_le (by simpa only [velocityInitialState, wholeQuery, wholeSpaceQuery,
    sub_zero] using hb)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

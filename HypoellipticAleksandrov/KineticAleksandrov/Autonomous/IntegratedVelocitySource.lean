module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.IntegratedVelocityComparison
import Mathlib.Tactic

/-! # Actual compact convex-profile source tests -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set MeasureTheory
open SectionTwo

/-- Positive forcing density supplied by the convex velocity profile. -/
def velocityOccupationDensity (r v : ℝ) : ℝ :=
  r ^ 2 / Real.sqrt (r ^ 2 + v ^ 2) ^ 3

/-- The convex forcing density is smooth. -/
theorem velocityOccupationDensity_contDiff {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ (⊤ : ℕ∞) (velocityOccupationDensity r) := by
  apply contDiff_const.div
    (((contDiff_const.add (contDiff_id.pow 2)).sqrt
      (fun v => ne_of_gt (by nlinarith [sq_pos_of_pos hr, sq_nonneg v]))).pow 3)
  intro v
  exact pow_ne_zero _ (ne_of_gt (Real.sqrt_pos.2
    (by nlinarith [sq_pos_of_pos hr, sq_nonneg v])))

/-- The forcing density is nonnegative everywhere. -/
theorem velocityOccupationDensity_nonneg (r v : ℝ) : 0 ≤ velocityOccupationDensity r v := by
  unfold velocityOccupationDensity
  positivity

/-- A smooth compact unit probe multiplied by the density is a valid compact source. -/
theorem velocity_profile_source_bound (hH : HormanderHypoellipticityStatement)
    {lam Lam r : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E)
    (hr : 0 < r) (T : ℝ)
    (f : ℝ × EvolutionAmbientState 1 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ {q | q.1 < T})
    (hf01 : ∀ q, 0 ≤ f q ∧ f q ≤ 1) (p : Point) (hp : p.time < T) :
    duhamelPotential E.2 T
      (fun q => f (q.time, q.position, q.velocity) *
        (lam * velocityOccupationDensity r (q.position 0))) p ≤
      Real.sqrt (2 * Lam * (T - p.time)) := by
  let g := fun q : Point => f (q.time, q.position, q.velocity) *
    (lam * velocityOccupationDensity r (q.position 0))
  have hgs : ContDiff ℝ (⊤ : ℕ∞) (rawLift g) := by
    exact hf.mul (contDiff_const.mul ((velocityOccupationDensity_contDiff hr).comp
      ((contDiff_apply ℝ ℝ 0).comp contDiff_snd.fst)))
  have hc : HasCompactSupport g :=
    (hfc.comp_homeomorph (KineticPoint.homeomorphProd 1)).mul_right
  have hu : tsupport g ⊆ evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) T := by
    intro q hq
    have hqf := tsupport_mul_subset_left hq
    have hraw : (q.time, q.position, q.velocity) ∈ tsupport f := by
      exact tsupport_comp_subset_preimage f
        (KineticPoint.homeomorphProd 1).continuous hqf
    refine ⟨hfU hraw, ?_⟩
    change q.position ∈ movingDomain (wholeSpace 1) (fun _ => 0) q.time
    rw [movingDomain_wholeSpace]
    trivial
  have hLn : 0 ≤ Lam := hlam.le.trans hLam
  have hpoint : p ∈ evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) T := by
    refine ⟨hp, ?_⟩
    change p.position ∈ movingDomain (wholeSpace 1) (fun _ => 0) p.time
    rw [movingDomain_wholeSpace]
    trivial
  have hb := velocity_duhamel_le_barrier hH hlam hLam A E hE T g
    (velocityOccupationBarrier r Lam T)
    (fun q => mul_nonneg (hf01 _).1
      (mul_nonneg hlam.le (velocityOccupationDensity_nonneg r _))) hgs hc hu
    (velocityOccupationBarrier_continuous r Lam T)
    (velocityOccupationBarrier_regular hr hLn T)
    (fun q hq => (velocityOccupationBarrier_bounds hr hLn T q hq.1).1)
    (fun q hq => by
      have he := velocityOccupationBarrier_operator hlam A hr T q hq.1.le
      have hm := mul_le_mul_of_nonneg_right (hf01 (q.time, q.position, q.velocity)).2
        (mul_nonneg hlam.le (velocityOccupationDensity_nonneg r (q.position 0)))
      change _ ≤ -(f _ * (lam * velocityOccupationDensity r (q.position 0)))
      change _ ≤ -lam * velocityOccupationDensity r (q.position 0) at he
      linarith) p hpoint
  exact hb.trans (velocityOccupationBarrier_bounds hr hLn T p hp.le).2

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceFutureContinuity
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.Order.Compact
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ClassicalTerminalWeak

/-! # Continuity strictly before a bounded source starts -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set Filter Evolution Metric
open scoped Topology
variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/-- A positive bounded future source has a continuous literal potential at every earlier
interior starting point. This is pointwise continuity, rather than an AE representative. -/
theorem continuousOn_duhamelFuture_before_source
    (hH : HormanderHypoellipticityStatement)
    (hΩa : IsAdmissibleEvolutionDomain Ω) (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K)
    (hB : IsSmoothFullKineticCoefficient B) (hBs : IsSymmetricFullKineticCoefficient B)
    (hb : IsSmoothDrift b) (lam Lam m : ℝ) (hlam : 0 < lam) (hm : 0 < m)
    (hell : HasEverywhereLoewnerBounds lam Lam B)
    (hcoerc : HasUnitDirectionDriftCoercivity m b)
    (s T : ℝ) (hsT : s ≤ T)
    (F : KineticPoint d → ℝ) (hF : Measurable F) (M : ℝ) (hM : 0 ≤ M)
    (hFb : ∀ p, 0 ≤ F p ∧ F p ≤ M)
    (hFz : ∀ p, KineticPoint.equivProd d p ∉ boundedSourceFutureSet Ω γ s T → F p = 0) :
    ContinuousOn (duhamelPotential K T F) (evolutionPastOpenCylinder Ω γ s) := by
  classical
  let P := evolutionHomeomorph d
  let D := P ⁻¹' evolutionPastOpenCylinder Ω γ s
  have hD : IsOpen D :=
    (isOpen_evolutionPastOpenCylinder (isOpen_of_isAdmissibleEvolutionDomain hΩa)
      hγ s).preimage P.continuous
  have hc : ContinuousOn (duhamelPotential K T F ∘ P) D := by
    intro z hz
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hD z hz
    let U := ball z r
    let C := closedBall z (r / 2)
    have hC : IsCompact C := isCompact_closedBall z (r / 2)
    have hCU : C ⊆ U := closedBall_subset_ball (half_lt_self hr)
    have hCi : C ⊆ closure (interior C) := by
      rw [interior_closedBall z (half_pos hr).ne', closure_ball z (half_pos hr).ne']
    have hbig : IsCompact (closedBall z r) := isCompact_closedBall z r
    let : IsFiniteMeasure (volume.restrict U) := ⟨by
      rw [Measure.restrict_apply_univ]
      exact (measure_mono ball_subset_closedBall).trans_lt hbig.measure_lt_top⟩
    have htime : Continuous (fun w : EvolutionVec d => (P w).time) :=
      continuous_time.comp P.continuous
    obtain ⟨q, hq, hmin⟩ := hbig.exists_isMinOn
      ⟨z, mem_closedBall_self hr.le⟩ htime.continuousOn
    let a := min (P q).time s
    have hfloor : ∀ w ∈ U, a ≤ (P w).time := by
      intro w hw
      exact (min_le_left _ _).trans (hmin (ball_subset_closedBall hw))
    have hcont := continuousOn_duhamelFuture_compact_collar hH hΩa hΩ hγ B b S K hreal
      hB hBs hb lam Lam m hlam hm hell hcoerc a s T (min_le_right _ _) hsT U C
      isOpen_ball hC hCi hCU hball hfloor F hF M hM hFb hFz
    exact (hcont.continuousAt (closedBall_mem_nhds z (half_pos hr))).continuousWithinAt
  have hcomp := hc.comp P.symm.continuous.continuousOn (fun p hp => by
    simpa only [D, mem_preimage, Homeomorph.apply_symm_apply] using hp)
  simpa only [Function.comp_def, Homeomorph.apply_symm_apply] using hcomp

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

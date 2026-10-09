module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionStartIdentity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CoreDominationAllTimeKernel
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.VisitRecursionUnconditionalInitial

/-! # Finite terminal kernels for the position-start identity -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov ProbabilityTheory
open scoped Classical

/-- The existing terminal family as a measurable kernel, including zero-duration starts. -/
def positionStartTerminalKernel
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ) :
    Kernel Point Point :=
  ⟨enlargedActiveTerminalFamily hH hLE hlam hLam A c J b,
    positionStartTerminalFamily_measurable hH hLE hlam hLam A c J b⟩

/-- Every actual active terminal family has mass at most one. -/
theorem positionStartTerminalKernel_mass_le_one
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ) (p : Point) :
    positionStartTerminalKernel hH hLE hlam hLam A c J b p univ ≤ 1 := by
  change (enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p) univ ≤ 1
  unfold enlargedActiveTerminalFamily
  split
  · simp only [Measure.dirac_apply_of_mem (mem_univ p), le_refl]
  · apply (Measure.restrict_le_self univ).trans
    change (if h : p ∈ enlargedVisitPoleSet (visitActiveUnion c J) b then _
      else (0 : Measure Point)) univ ≤ 1
    split
    · simp only [measure_univ, le_refl]
    · exact zero_le

/-- The terminal kernel is uniformly finite without a domination hypothesis. -/
instance positionStartTerminalKernel_isFiniteKernel
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ) :
    IsFiniteKernel (positionStartTerminalKernel hH hLE hlam hLam A c J b) :=
  ⟨1, ENNReal.one_lt_top,
    positionStartTerminalKernel_mass_le_one hH hLE hlam hLam A c J b⟩

/-- Terminal mixtures retain the closed active velocity support. -/
theorem positionStartTerminalMixture_ae_closedActive
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (b : ℝ)
    (mu : Measure Point) :
    ∀ᵐ q ∂(positionStartTerminalKernel hH hLE hlam hLam A c J b ∘ₘ mu),
      q.velocity 0 ∈ closure c.active := by
  apply Measure.ae_comp_of_ae_ae
    (isClosed_closure.measurableSet.preimage
      ((continuous_apply 0).comp continuous_velocity).measurable)
  apply Filter.Eventually.of_forall
  intro p
  change ∀ᵐ q ∂enlargedActiveTerminalFamily hH hLE hlam hLam A c J b p,
    q.velocity 0 ∈ closure c.active
  unfold enlargedActiveTerminalFamily
  split
  · rename_i hp
    apply (ae_dirac_iff (isClosed_closure.measurableSet.preimage
      ((continuous_apply 0).comp continuous_velocity).measurable)).mpr
    exact subset_closure ((visitActiveUnion_carrier c J).le hp.2).1
  · have hs := enlargedActiveExitMixture_ae_velocity
      hH hLE hlam hLam A c J b (Measure.dirac p)
    rw [visitKernel_comp_dirac] at hs
    exact hs.filter_mono (ae_mono Measure.restrict_le_self)

/-- Finite all-time active mixtures retain open active support. -/
theorem positionStartAllTimeMixture_ae_active
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (mu : Measure Point) :
    ∀ᵐ q ∂(coreAllTimeGreenKernel hH hLE hlam hLam A c ∘ₘ mu),
      q.velocity 0 ∈ c.active := by
  apply Measure.ae_comp_of_ae_ae
    (isOpen_Ioo.measurableSet.preimage
      ((continuous_apply 0).comp continuous_velocity).measurable)
  apply Filter.Eventually.of_forall
  intro p
  change ∀ᵐ q ∂(if hp : p.velocity 0 ∈ c.active then
    stripGreen hH hLE hlam hLam A (visitActiveInterval c) ⊤
      (coreAllTimePole c ⟨p, hp⟩) else 0), q.velocity 0 ∈ c.active
  split
  · exact (stripGreen_infinite_ae_future_carrier hH hLE hlam hLam A
      (visitActiveInterval c) _).mono fun _ hq => hq.2
  · simp only [ae_zero, Filter.eventually_bot]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

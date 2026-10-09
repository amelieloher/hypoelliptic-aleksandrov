module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonBorel
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonProbability
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonMonotone
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonOrder
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonCone
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripMeasureExt

/-! # Actual infinite-horizon Green and exit measures and their compact smooth identity -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- The actual infinite-horizon measures satisfy the literal identity for every compact smooth
  test. -/
theorem strip_identity_infinite_compact
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤)
    (f : exitProbeSubmodule) :
    exitProbePhysical f e.1 =
      (∫ p, exitProbePhysical f p ∂stripInfiniteExit hH hLE hlam hLam A H e) -
        ∫ p, forwardScalarOperator A.a (exitProbePhysical f) p
          ∂stripGreen hH hLE hlam hLam A H ⊤ e := by
  have h := stripInfiniteExit_probe_integral hH hLE hlam hLam A H e f
  change (∫ p, exitProbePhysical f p ∂stripInfiniteExit hH hLE hlam hLam A H e) =
    exitProbePhysical f e.1 + ∫ p, forwardScalarOperator A.a (exitProbePhysical f) p
      ∂stripGreen hH hLE hlam hLam A H ⊤ e at h
  linarith

/-- Full compact smooth tests uniquely identify the actual finite infinite-horizon exit measure. -/
theorem stripInfiniteExit_unique
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤)
    (μ : Measure Point) [IsFiniteMeasure μ]
    (hμ : ∀ f : exitProbeSubmodule,
      (∫ p, exitProbePhysical f p ∂μ) = infiniteExitProbeValue hH hLE hlam hLam A H e f) :
    μ = stripInfiniteExit hH hLE hlam hLam A H e := by
  apply nested_physical_measure_eq univ isOpen_univ
    (Filter.Eventually.of_forall (fun _ => mem_univ _))
    (Filter.Eventually.of_forall (fun _ => mem_univ _))
  intro f _ _
  exact (hμ f).trans (stripInfiniteExit_probe_integral hH hLE hlam hLam A H e f).symm

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.NestedStripIntervalRestart

/-! # Actual larger-interval Green decomposition on all compact interior source tests -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- Compact interior tests satisfy the exact Green decomposition with the true restart mixture. -/
theorem nestedIntervalGreen_probe_identity
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H1 H2 : Interval)
    (hsub : H1.carrier ⊆ H2.carrier) (sMinus T : ℝ)
    (e : StripPole H1 (T : WithTop ℝ)) (he : sMinus < e.1.time)
    (f : exitProbeSubmodule) (hfn : ∀ p, 0 ≤ exitProbePhysical f p)
    (hs : tsupport (exitProbePhysical f) ⊆ {p | p.time < T ∧ p.velocity 0 ∈ H2.carrier}) :
    (∫ p, exitProbePhysical f p ∂stripGreen hH hLE hlam hLam A H2 T
      (nestedPoleInclusion H1 H2 hsub T e)) =
      (∫ p, exitProbePhysical f p ∂stripGreen hH hLE hlam hLam A H1 T e) +
      ∫ p, exitProbePhysical f p
        ∂nestedIntervalRestartGreen hH hLE hlam hLam A H1 H2 sMinus T e := by
  let E := stripEvolution hH hLE hlam hLam A H2
  let u := nestedSourcePotential H2 E T f
  let τ := nestedIntervalRestartPoles hH hLE hlam hLam A H1 H2 sMinus T e
  have hid := nestedSourcePotential_restart_identity hH hLE hlam hLam A H1 H2 hsub
    sMinus T e he f hfn hs
  have hmap : (∫ p, u p ∂(stripExit hH hLE hlam hLam A H1 T e).restrict
      (nestedIntervalInternalExit H1 H2 sMinus T)) = ∫ ep, u ep.1 ∂τ := by
    rw [← nestedIntervalRestartPoles_map hH hLE hlam hLam A H1 H2 sMinus T e]
    exact integral_map measurable_subtype_coe.aemeasurable
      (nestedSourcePotential_measurable H2 E T f).aestronglyMeasurable
  have hrep : (fun ep : StripPole H2 (T : WithTop ℝ) => u ep.1) =
      fun ep => ∫ p, exitProbePhysical f p ∂stripGreen hH hLE hlam hLam A H2 T ep := by
    funext ep
    exact nestedSourcePotential_eq_green A H2 E T f ep
  have hb := nested_integral_bind τ (stripGreen hH hLE hlam hLam A H2 T)
    (Measure.measurable_measure.mpr (fun B hB =>
      stripGreen_measurable_apply hH hLE hlam hLam A H2 T B hB))
    (exitProbePhysical f)
    (nestedProbe_integrable A f
      (nestedIntervalRestartGreen hH hLE hlam hLam A H1 H2 sMinus T e))
  change _ = _ + ∫ p, u p ∂(stripExit hH hLE hlam hLam A H1 T e).restrict
    (nestedIntervalInternalExit H1 H2 sMinus T) at hid
  rw [hmap, hrep, ← hb] at hid
  exact hid

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.MassRepresentationMass
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.JointQueryBorelDense
import Mathlib.MeasureTheory.Measure.GiryMonad

/-! # Borel later-exit kernels on the actual valid state fibers -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory SectionTwo Parabolic
open scoped CompactlySupported

/-- The physical pole conversion is continuous on the valid starting-state fiber. -/
theorem continuous_ballStatePoint {d : ℕ} (s : ℝ) (v₀ : PDE.Vec d) (R : ℝ) :
    Continuous (fun w : EvolutionState (PDE.euclideanBall v₀ R) (fun _ => 0) s =>
      (ballStateStart s w).1) :=
  KineticPoint.continuous_mk continuous_const continuous_subtype_val.snd
    continuous_subtype_val.fst

variable (hH : HormanderHypoellipticityStatement)
  (hLE : LiebermanEllipsoidDirichletStatement)
  {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ}
  (hlam : 0 < lam) (hLam : lam ≤ Lam)
  (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
  (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)

/-- The uniquely characterized exit measure depends measurably on its valid fixed-time pole. -/
theorem measurable_ballExitRaw_fixedTime (s T : ℝ) (hsT : s < T) :
    Measurable (fun w : EvolutionState (PDE.euclideanBall v₀ R) (fun _ => 0) s =>
      ballExitRaw hH hLE hd hlam hLam B hB v₀ hR (ballStateStart s w) ⟨T, hsT⟩) := by
  let μ (w : EvolutionState (PDE.euclideanBall v₀ R) (fun _ => 0) s) :=
    ballExitRaw hH hLE hd hlam hLam B hB v₀ hR (ballStateStart s w) ⟨T, hsT⟩
  let H := KineticPoint.homeomorphProd d
  let ν (w : EvolutionState (PDE.euclideanBall v₀ R) (fun _ => 0) s) := (μ w).map H
  have hm (w) : ν w univ ≤ 1 := by
    dsimp only [ν]
    rw [Measure.map_apply H.measurable MeasurableSet.univ, preimage_univ]
    exact (ballExitRaw_mass hH hLE hd hlam hLam B hB v₀ hR _ _).le
  have ht (f : C_c(ℝ × PDE.Vec d × PDE.Vec d, ℝ))
      (hf : ContDiff ℝ (⊤ : ℕ∞) f) : Measurable (fun w => ∫ x, f x ∂ν w) := by
    let F : boundaryProbeSubmodule d := ⟨f, hf, f.hasCompactSupport⟩
    obtain ⟨hφ, _, hc⟩ := boundaryProbePhysical_regular F
    let φ := boundaryProbePhysical F
    have heq : (fun w => ∫ x, f x ∂ν w) = fun w =>
        ballBoundarySolution hH hLE hd hlam hLam B hB v₀ hR s T φ
          (ballStateStart s w).1 := by
      funext w
      dsimp only [ν]
      have hfm : AEStronglyMeasurable (fun x => f x) ((μ w).map H) :=
        f.continuous.measurable.aestronglyMeasurable
      exact (integral_map H.measurable.aemeasurable hfm).trans
        ((ballExitRaw_spec hH hLE hd hlam hLam B hB v₀ hR _ _).2.2 φ hφ hc)
    rw [heq]
    have he := (ballBoundarySolution_smooth_traces hH hLE hd hlam hLam B hB v₀ hR
      s T hsT φ hφ hc).2.2.1
    exact (he.comp_continuous (continuous_ballStatePoint s v₀ R)
      (fun w => ⟨le_rfl, hsT.le, subset_closure (ball_state_velocity_mem s w)⟩)).measurable
  have hν := measurable_measure_family_of_smooth_tests ν hm ht
  have hh := (Measure.measurable_map H.symm H.symm.measurable).comp hν
  have heq : (fun w => (ν w).map H.symm) = μ := by
    funext w
    dsimp only [ν]
    rw [Measure.map_map H.symm.measurable H.measurable]
    have hid : H.symm ∘ H = (id : KineticPoint d → KineticPoint d) :=
      funext H.symm_apply_apply
    rw [hid, Measure.map_id]
  change Measurable (fun w => (ν w).map H.symm) at hh
  rwa [heq] at hh

/-- The later ambient exit measures form a genuine measurable kernel on valid states. -/
def ballBoundaryKernel (s T : ℝ) (hsT : s < T) :
    ProbabilityTheory.Kernel (EvolutionState (PDE.euclideanBall v₀ R) (fun _ => 0) s)
      (KineticPoint d) :=
  ⟨fun w => ballExitRaw hH hLE hd hlam hLam B hB v₀ hR (ballStateStart s w) ⟨T, hsT⟩,
    measurable_ballExitRaw_fixedTime hH hLE hd hlam hLam B hB v₀ hR s T hsT⟩

/-- Every actual later exit kernel is Markov, with mass established by representation. -/
instance ballBoundaryKernel_isMarkov (s T : ℝ) (hsT : s < T) :
    ProbabilityTheory.IsMarkovKernel
      (ballBoundaryKernel hH hLE hd hlam hLam B hB v₀ hR s T hsT) where
  isProbabilityMeasure w :=
    ⟨ballExitRaw_mass hH hLE hd hlam hLam B hB v₀ hR (ballStateStart s w) ⟨T, hsT⟩⟩

end HypoellipticAleksandrov.KineticAleksandrov.LocalA

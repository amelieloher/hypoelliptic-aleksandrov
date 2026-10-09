module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitFunctionalValues
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitFunctionalDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TerminalFunctionalExtension

/-! # The unique positive contraction functional on the closed exit carrier -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set HypoellipticAleksandrov
open scoped CompactlySupported

/-- The actual homogeneous probe value is bounded by its boundary supremum. -/
theorem exitProbeValueLinear_bound
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ))
    (f : exitProbeSubmodule) (c : ℝ) (_hc : 0 ≤ c)
    (hbd : ∀ p, |exitProbeCcLinear H T f p| ≤ c) :
    |exitProbeValueLinear A H E T e f| ≤ c := by
  have hu := exitProbeValue_le_of_boundary hH hlam hLam A H E hE T e f c
    (fun p hp => (le_abs_self _).trans (hbd ⟨p, hp⟩))
  have hn := exitProbeValue_le_of_boundary hH hlam hLam A H E hE T e (-f) c
    (fun p hp => by
      change -exitProbePhysical f p ≤ c
      exact (neg_le_abs _).trans (hbd ⟨p, hp⟩))
  have heq := (exitProbeValueLinear A H E T e).map_neg f
  change exitProbeValue A H E T e (-f) = -exitProbeValue A H E T e f at heq
  rw [heq] at hn
  exact abs_le.mpr ⟨neg_le.mp hn, hu⟩

/-- Nonnegative exit probes have nonnegative actual homogeneous values. -/
theorem exitProbeValueLinear_nonneg
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ))
    (f : exitProbeSubmodule) (hbd : ∀ p, 0 ≤ exitProbeCcLinear H T f p) :
    0 ≤ exitProbeValueLinear A H E T e f := by
  have hn := exitProbeValue_le_of_boundary hH hlam hLam A H E hE T e (-f) 0
    (fun p hp => by
      change -exitProbePhysical f p ≤ 0
      exact neg_nonpos.mpr (hbd ⟨p, hp⟩))
  have heq := (exitProbeValueLinear A H E T e).map_neg f
  change exitProbeValue A H E T e (-f) = -exitProbeValue A H E T e f at heq
  rw [heq] at hn
  exact neg_nonpos.mp hn

/-- The actual homogeneous values extend to exactly one positive contraction functional
on all compactly supported continuous exit data. -/
theorem existsUnique_stripBoundaryFunctional
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ)) :
    ∃! ℓ : C_c(stripClosedExit H T, ℝ) →ₚ[ℝ] ℝ,
      (∀ (f : C_c(stripClosedExit H T, ℝ)) (c : ℝ), 0 ≤ c →
        (∀ p, |f p| ≤ c) → |ℓ f| ≤ c) ∧
      ∀ f : exitProbeSubmodule, ℓ (exitProbeCcLinear H T f) = exitProbeValueLinear A H E T e f := by
  obtain ⟨ℓ, hbd, hagree⟩ := exists_positive_extension_of_dense (exitProbeCcLinear H T)
    (exitProbeValueLinear A H E T e)
    (exitProbeValueLinear_bound hH hlam hLam A H E hE T e)
    (exitProbeValueLinear_nonneg hH hlam hLam A H E hE T e)
    (exitProbeCc_sq H T) (exitProbeCc_dense H T)
  refine ⟨ℓ, ⟨hbd, hagree⟩, fun k hk => ?_⟩
  have hlin : k.toLinearMap = ℓ.toLinearMap :=
    eq_of_bounded_of_dense (exitProbeCcLinear H T) k.toLinearMap ℓ.toLinearMap
      hk.1 hbd (fun f => (hk.2 f).trans (hagree f).symm) (exitProbeCc_dense H T)
  exact PositiveLinearMap.ext (fun f => LinearMap.congr_fun hlin f)

/-- The strip boundary functional is chosen only from its proved unique characterization. -/
def stripBoundaryFunctional
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ)) :
    C_c(stripClosedExit H T, ℝ) →ₚ[ℝ] ℝ :=
  (existsUnique_stripBoundaryFunctional hH hlam hLam A H E hE T e).exists.choose

/-- Full contraction and smooth-probe characterization of the unique boundary functional. -/
theorem stripBoundaryFunctional_spec
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (e : StripPole H (T : WithTop ℝ)) :
    (∀ (f : C_c(stripClosedExit H T, ℝ)) (c : ℝ), 0 ≤ c → (∀ p, |f p| ≤ c) →
      |stripBoundaryFunctional hH hlam hLam A H E hE T e f| ≤ c) ∧
    ∀ f : exitProbeSubmodule, stripBoundaryFunctional hH hlam hLam A H E hE T e
      (exitProbeCcLinear H T f) = exitProbeValueLinear A H E T e f :=
  (existsUnique_stripBoundaryFunctional hH hlam hLam A H E hE T e).exists.choose_spec

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

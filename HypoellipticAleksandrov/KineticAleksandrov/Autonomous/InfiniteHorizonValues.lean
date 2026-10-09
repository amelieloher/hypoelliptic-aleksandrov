module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonProbes
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitFunctional
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonLinear

/-! # Actual infinite Green probe values and their positive contraction bounds -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Parabolic
open SectionTwo TheoremA Evolution
open scoped CompactlySupported Topology

private theorem infinite_probe_operator_add {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (f g : exitProbeSubmodule) :
    forwardScalarOperator A.a (exitProbePhysical (f + g)) =
      fun p => forwardScalarOperator A.a (exitProbePhysical f) p +
        forwardScalarOperator A.a (exitProbePhysical g) p := by
  funext p
  have h := comparison_forwardOperator_add
    (exitProbePhysical_isKineticC112On f univ isOpen_univ)
    (exitProbePhysical_isKineticC112On g univ isOpen_univ) (autonomousCoefficient A.a) (mem_univ p)
  simp only [forwardOperator_autonomous] at h
  exact h

private theorem infinite_probe_operator_smul {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (c : ℝ) (f : exitProbeSubmodule) :
    forwardScalarOperator A.a (exitProbePhysical (c • f)) =
      fun p => c * forwardScalarOperator A.a (exitProbePhysical f) p := by
  funext p
  have h := comparison_forwardOperator_const_mul
    (exitProbePhysical_isKineticC112On f univ isOpen_univ) c (autonomousCoefficient A.a)
      (mem_univ p)
  simp only [forwardOperator_autonomous] at h
  exact h

/-- The infinite Green measure determines the actual exit value of each ambient probe. -/
def infiniteExitProbeValue
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤)
    (f : exitProbeSubmodule) : ℝ :=
  exitProbePhysical f e.1 + ∫ p, forwardScalarOperator A.a (exitProbePhysical f) p
    ∂stripGreen hH hLE hlam hLam A H ⊤ e

/-- Actual infinite Green probe values are a linear functional. -/
def infiniteExitProbeValueLinear
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤) :
    exitProbeSubmodule →ₗ[ℝ] ℝ where
  toFun := infiniteExitProbeValue hH hLE hlam hLam A H e
  map_add' f g := by
    unfold infiniteExitProbeValue
    rw [infinite_probe_operator_add]
    have hf : Integrable (forwardScalarOperator A.a (exitProbePhysical f))
        (stripGreen hH hLE hlam hLam A H ⊤ e) :=
      stripGreen_integrable hH hLE hlam hLam A H ⊤ e (exitProbeOperatorDatum A f)
    have hg : Integrable (forwardScalarOperator A.a (exitProbePhysical g))
        (stripGreen hH hLE hlam hLam A H ⊤ e) :=
      stripGreen_integrable hH hLE hlam hLam A H ⊤ e (exitProbeOperatorDatum A g)
    rw [integral_add hf hg]
    change exitProbePhysical f e.1 + exitProbePhysical g e.1 + _ = _
    ring
  map_smul' c f := by
    unfold infiniteExitProbeValue
    rw [infinite_probe_operator_smul, integral_const_mul]
    change c * exitProbePhysical f e.1 + _ = c * _
    ring

/-- Every compact ambient probe vanishes beyond some horizon later than the pole. -/
theorem infinite_probe_later_horizon (e : Point) (f : exitProbeSubmodule) :
    ∃ T : ℝ, e.time < T ∧ tsupport f.1 ⊆ {x | Evolution.timeCoord 1 x < T} := by
  obtain ⟨M, hM⟩ := f.2.2.isCompact.bddAbove_image (Evolution.timeCoord 1).continuous.continuousOn
  refine ⟨max M e.time + 1, by linarith [le_max_right M e.time], ?_⟩
  intro x hx
  have hh : Evolution.timeCoord 1 x ≤ M := hM ⟨x, hx, rfl⟩
  exact lt_of_le_of_lt hh (by linarith [le_max_left M e.time])

/-- The infinite probe value is exactly the finite value at any later supporting horizon. -/
theorem infiniteExitProbeValue_eq_finite
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤)
    (f : exitProbeSubmodule) (T : ℝ) (ht : e.1.time < T)
    (hs : tsupport f.1 ⊆ {x | Evolution.timeCoord 1 x < T}) :
    infiniteExitProbeValueLinear hH hLE hlam hLam A H e f =
      exitProbeValueLinear A H (stripEvolution hH hLE hlam hLam A H) T
        (stripPoleFinite H e T ht) f := by
  change exitProbePhysical f e.1 + _ = exitProbePhysical f e.1 + _
  exact congrArg (fun z => exitProbePhysical f e.1 + z)
    (infinite_probe_source_integral hH hLE hlam hLam A H e T ht T le_rfl f hs).symm

/-- A compact early probe is zero on its later terminal plane. -/
theorem infinite_probe_zero_terminal (f : exitProbeSubmodule) (T : ℝ)
    (hs : tsupport f.1 ⊆ {x | Evolution.timeCoord 1 x < T}) (p : Point) (ht : p.time = T) :
    exitProbePhysical f p = 0 := by
  change f.1 (reconstructionPhysicalHomeomorph.symm p) = 0
  apply image_eq_zero_of_notMem_tsupport
  intro hx
  have hp := hs hx
  change p.time < T at hp
  exact (ne_of_lt hp) ht

/-- Face bounds control the actual infinite Green probe value by contraction one. -/
theorem infiniteExitProbeValueLinear_bound
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤)
    (f : exitProbeSubmodule) (c : ℝ) (hc : 0 ≤ c)
    (hbd : ∀ p, |infiniteExitProbeCcLinear H f p| ≤ c) :
    |infiniteExitProbeValueLinear hH hLE hlam hLam A H e f| ≤ c := by
  obtain ⟨T, ht, hs⟩ := infinite_probe_later_horizon e.1 f
  rw [infiniteExitProbeValue_eq_finite hH hLE hlam hLam A H e f T ht hs]
  apply exitProbeValueLinear_bound hH hlam hLam A H _
    (stripEvolution_spec hH hLE hlam hLam A H) T _ f c hc
  intro p
  rcases p.2 with hp | hp
  · change |exitProbePhysical f p.1| ≤ c
    rw [infinite_probe_zero_terminal f T hs p.1 hp.1, abs_zero]
    exact hc
  · exact hbd ⟨p.1, hp.2⟩

/-- Nonnegative compact face data have nonnegative actual infinite Green probe values. -/
theorem infiniteExitProbeValueLinear_nonneg
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤)
    (f : exitProbeSubmodule) (hbd : ∀ p, 0 ≤ infiniteExitProbeCcLinear H f p) :
    0 ≤ infiniteExitProbeValueLinear hH hLE hlam hLam A H e f := by
  obtain ⟨T, ht, hs⟩ := infinite_probe_later_horizon e.1 f
  rw [infiniteExitProbeValue_eq_finite hH hLE hlam hLam A H e f T ht hs]
  apply exitProbeValueLinear_nonneg hH hlam hLam A H _
    (stripEvolution_spec hH hLE hlam hLam A H) T _ f
  intro p
  rcases p.2 with hp | hp
  · exact le_of_eq (infinite_probe_zero_terminal f T hs p.1 hp.1).symm
  · exact hbd ⟨p.1, hp.2⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

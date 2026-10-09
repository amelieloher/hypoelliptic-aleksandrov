module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonFunctional
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitMeasureRiesz

/-! # Unique infinite-horizon Riesz exit measure with its full compact-test characterization -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution
open scoped CompactlySupported

/-- There is exactly one subprobability measure with the full boundary-functional action. -/
theorem existsUnique_infinite_exit
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤) :
    ∃! μ : Measure (stripInfiniteFace H), μ univ ≤ 1 ∧
      ∀ f : C_c(stripInfiniteFace H, ℝ), ∫ p, f p ∂μ =
        infiniteBoundaryFunctional hH hLE hlam hLam A H e f :=
  existsUnique_boundaryFunctional_measure (infiniteBoundaryFunctional hH hLE hlam hLam A H e)
    (infiniteBoundaryFunctional_spec hH hLE hlam hLam A H e).1

/-- The exit measure is chosen only from the proved unique full compact-test characterization. -/
def infiniteExitMeasureOnFace
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤) :
    Measure (stripInfiniteFace H) :=
  (existsUnique_infinite_exit hH hLE hlam hLam A H e).exists.choose

/-- Full characterization of the unique exit measure on its closed boundary carrier. -/
theorem infiniteExitMeasureOnFace_spec
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤) :
    infiniteExitMeasureOnFace hH hLE hlam hLam A H e univ ≤ 1 ∧
      ∀ f : C_c(stripInfiniteFace H, ℝ),
        ∫ p, f p ∂infiniteExitMeasureOnFace hH hLE hlam hLam A H e =
          infiniteBoundaryFunctional hH hLE hlam hLam A H e f :=
  (existsUnique_infinite_exit hH hLE hlam hLam A H e).exists.choose_spec

/-- Each uniquely characterized exit measure is finite. -/
instance infiniteExitMeasureOnFace_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤) :
    IsFiniteMeasure (infiniteExitMeasureOnFace hH hLE hlam hLam A H e) :=
  ⟨lt_of_le_of_lt (infiniteExitMeasureOnFace_spec hH hLE hlam hLam A H e).1 (by simp)⟩

/-- The physical exit measure is the image of that unique boundary measure. -/
def stripInfiniteExit
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤) : Measure Point :=
  (infiniteExitMeasureOnFace hH hLE hlam hLam A H e).map Subtype.val

/-- The physical exit measure is finite. -/
instance stripInfiniteExit_isFiniteMeasure
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤) :
    IsFiniteMeasure (stripInfiniteExit hH hLE hlam hLam A H e) := by
  unfold stripInfiniteExit
  infer_instance

/-- The physical exit measure has mass at most one. -/
theorem stripInfiniteExit_mass_le_one
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤) :
    stripInfiniteExit hH hLE hlam hLam A H e univ ≤ 1 := by
  unfold stripInfiniteExit
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ,
    preimage_univ]
  exact (infiniteExitMeasureOnFace_spec hH hLE hlam hLam A H e).1

/-- The physical measure is supported on the full closed infinite velocity-face carrier. -/
theorem stripInfiniteExit_compl_face
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤) :
    stripInfiniteExit hH hLE hlam hLam A H e (stripInfiniteFace H)ᶜ = 0 := by
  unfold stripInfiniteExit
  rw [Measure.map_apply measurable_subtype_coe
    (isClosed_stripInfiniteFace H).measurableSet.compl]
  have heq : (Subtype.val : stripInfiniteFace H → Point) ⁻¹' (stripInfiniteFace H)ᶜ = ∅ := by
    ext p
    simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false]
    exact not_not.mpr p.2
  rw [heq, measure_empty]

/-- Actual homogeneous probe values are exactly the physical exit integrals. -/
theorem stripInfiniteExit_probe_integral
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (e : StripPole H ⊤)
    (f : exitProbeSubmodule) :
    ∫ p, exitProbePhysical f p ∂stripInfiniteExit hH hLE hlam hLam A H e =
      infiniteExitProbeValue hH hLE hlam hLam A H e f := by
  unfold stripInfiniteExit
  rw [integral_map measurable_subtype_coe.aemeasurable
    (exitProbePhysical_continuous_compact f).1.measurable.aestronglyMeasurable]
  change (∫ p, infiniteExitProbeCcLinear H f p
    ∂infiniteExitMeasureOnFace hH hLE hlam hLam A H e) = _
  rw [(infiniteExitMeasureOnFace_spec hH hLE hlam hLam A H e).2,
    (infiniteBoundaryFunctional_spec hH hLE hlam hLam A H e).2]
  rfl

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

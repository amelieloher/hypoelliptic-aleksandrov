module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceClosedGraph
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelSmooth
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # The closed L2 space of homogeneous kinetic solutions

Compact smooth tests give continuous linear functionals on L2. Their common kernel is
closed, and the Hörmander theorem supplies its continuous representatives.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set Evolution Occupation
open scoped Topology
variable {d : ℕ}

/-- A genuine smooth compact test supported in the chosen open domain. -/
structure BoundedSourceSmoothTest (U : Set (EvolutionVec d)) where
  /-- The ambient smooth test function. -/
  toFun : EvolutionVec d → ℝ
  /-- Full smoothness of the test. -/
  smooth : ContDiff ℝ (⊤ : ℕ∞) toFun
  /-- Compactness of the closed support. -/
  compact : HasCompactSupport toFun
  /-- The closed support lies inside the testing domain. -/
  support : tsupport toFun ⊆ U

/-- The literal adjoint of a compact smooth test is in restricted L2. -/
theorem boundedSource_testAdjoint_memLp (B : FullKineticCoefficient d)
    (b : PDE.Vec d → PDE.Vec d) (hB : IsSmoothFullKineticCoefficient B)
    (hb : IsSmoothDrift b) (U : Set (EvolutionVec d)) (φ : BoundedSourceSmoothTest U) :
    MemLp (transportedAdjoint B b φ.toFun) 2 (volume.restrict U) :=
  (contDiff_transportedAdjoint hB hb φ.smooth).continuous.memLp_of_hasCompactSupport
    (hasCompactSupport_transportedAdjoint φ.compact)

/-- Pairing a restricted L2 function with the actual kinetic adjoint test. -/
def boundedSource_testFunctional (B : FullKineticCoefficient d)
    (b : PDE.Vec d → PDE.Vec d) (hB : IsSmoothFullKineticCoefficient B)
    (hb : IsSmoothDrift b) (U : Set (EvolutionVec d)) (φ : BoundedSourceSmoothTest U) :
    Lp ℝ 2 (volume.restrict U) →L[ℝ] ℝ :=
  innerSL ℝ ((boundedSource_testAdjoint_memLp B b hB hb U φ).toLp
    (transportedAdjoint B b φ.toFun))

/-- This continuous functional is exactly the distributional test integral. -/
theorem boundedSource_testFunctional_apply (B : FullKineticCoefficient d)
    (b : PDE.Vec d → PDE.Vec d) (hB : IsSmoothFullKineticCoefficient B)
    (hb : IsSmoothDrift b) (U : Set (EvolutionVec d)) (φ : BoundedSourceSmoothTest U)
    (u : Lp ℝ 2 (volume.restrict U)) :
    boundedSource_testFunctional B b hB hb U φ u =
      ∫ z in U, u z * transportedAdjoint B b φ.toFun z := by
  rw [boundedSource_testFunctional, innerSL_apply_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(boundedSource_testAdjoint_memLp B b hB hb U φ).coeFn_toLp] with z hz
  simp only [RCLike.inner_apply, conj_trivial, hz]

/-- The common kernel of all actual distributional adjoint tests. -/
def boundedSourceHomogeneousL2Space (B : FullKineticCoefficient d)
    (b : PDE.Vec d → PDE.Vec d) (hB : IsSmoothFullKineticCoefficient B)
    (hb : IsSmoothDrift b) (U : Set (EvolutionVec d)) :
    Submodule ℝ (Lp ℝ 2 (volume.restrict U)) :=
  ⨅ φ : BoundedSourceSmoothTest U, (boundedSource_testFunctional B b hB hb U φ).ker

/-- The homogeneous weak-solution space is a closed L2 subspace. -/
theorem isClosed_boundedSourceHomogeneousL2Space (B : FullKineticCoefficient d)
    (b : PDE.Vec d → PDE.Vec d) (hB : IsSmoothFullKineticCoefficient B)
    (hb : IsSmoothDrift b) (U : Set (EvolutionVec d)) :
    IsClosed (boundedSourceHomogeneousL2Space B b hB hb U :
      Set (Lp ℝ 2 (volume.restrict U))) := by
  change IsClosed (↑(⨅ φ : BoundedSourceSmoothTest U,
    (boundedSource_testFunctional B b hB hb U φ).ker) : Set (Lp ℝ 2 (volume.restrict U)))
  rw [Submodule.coe_iInf]
  exact isClosed_iInter fun φ => (boundedSource_testFunctional B b hB hb U φ).isClosed_ker

/-- Members of the closed space satisfy the actual homogeneous weak equation. -/
theorem boundedSourceHomogeneousL2Space_isWeak (B : FullKineticCoefficient d)
    (b : PDE.Vec d → PDE.Vec d) (hB : IsSmoothFullKineticCoefficient B)
    (hb : IsSmoothDrift b) (U : Set (EvolutionVec d))
    [IsFiniteMeasure (volume.restrict U)]
    (u : boundedSourceHomogeneousL2Space B b hB hb U) :
    IsWeakTransportedSolution B b U (u.1 : EvolutionVec d → ℝ) (fun _ => 0) := by
  have hi : IntegrableOn (u.1 : EvolutionVec d → ℝ) U :=
    MemLp.integrable (by norm_num) (Lp.memLp u.1)
  refine ⟨hi.locallyIntegrableOn, fun φ hφ hc hs => ?_⟩
  have hm := u.2
  change u.1 ∈ ⨅ ψ : BoundedSourceSmoothTest U,
    (boundedSource_testFunctional B b hB hb U ψ).ker at hm
  simp only [Submodule.mem_iInf] at hm
  have hz := hm (⟨φ, hφ, hc, hs⟩ : BoundedSourceSmoothTest U)
  change boundedSource_testFunctional B b hB hb U ⟨φ, hφ, hc, hs⟩ u.1 = 0 at hz
  rw [boundedSource_testFunctional_apply] at hz
  simpa only [zero_mul, integral_zero] using hz

/-- An actual homogeneous L2 function belongs to the closed weak-solution space. -/
theorem mem_boundedSourceHomogeneousL2Space_of_isWeak
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (hB : IsSmoothFullKineticCoefficient B) (hb : IsSmoothDrift b)
    (U : Set (EvolutionVec d)) (u : EvolutionVec d → ℝ)
    (hu : MemLp u 2 (volume.restrict U))
    (hw : IsWeakTransportedSolution B b U u (fun _ => 0)) :
    hu.toLp u ∈ boundedSourceHomogeneousL2Space B b hB hb U := by
  change hu.toLp u ∈ ⨅ φ : BoundedSourceSmoothTest U,
    (boundedSource_testFunctional B b hB hb U φ).ker
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  intro φ
  change boundedSource_testFunctional B b hB hb U φ (hu.toLp u) = 0
  rw [boundedSource_testFunctional_apply]
  have he : (∫ z in U, (hu.toLp u) z * transportedAdjoint B b φ.toFun z) =
      ∫ z in U, u z * transportedAdjoint B b φ.toFun z := by
    apply integral_congr_ae
    filter_upwards [hu.coeFn_toLp] with z hz
    rw [hz]
  rw [he]
  have hh := hw.2 φ.toFun φ.smooth φ.compact φ.support
  simpa only [zero_mul, integral_zero] using hh

/-- Hörmander gives continuous representatives for every member of the closed space. -/
theorem boundedSourceHomogeneousL2Space_hasContinuousRepresentative
    (hH : HormanderHypoellipticityStatement)
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (hB : IsSmoothFullKineticCoefficient B) (hb : IsSmoothDrift b)
    (lam Lam m : ℝ) (hlam : 0 < lam) (hm : 0 < m)
    (hell : HasEverywhereLoewnerBounds lam Lam B)
    (hcoerc : HasUnitDirectionDriftCoercivity m b)
    (U : Set (EvolutionVec d)) (hU : IsOpen U) [IsFiniteMeasure (volume.restrict U)]
    (u : boundedSourceHomogeneousL2Space B b hB hb U) :
    ∃ f : EvolutionVec d → ℝ, ContinuousOn f U ∧
      (u.1 : EvolutionVec d → ℝ) =ᵐ[volume.restrict U] f := by
  obtain ⟨f, hf, he⟩ := exists_smooth_representative_transported_source hH hlam hB hell hb
    hm hcoerc hU (boundedSourceHomogeneousL2Space_isWeak B b hB hb U u) contDiffOn_const
  exact ⟨f, hf.continuousOn, he⟩

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

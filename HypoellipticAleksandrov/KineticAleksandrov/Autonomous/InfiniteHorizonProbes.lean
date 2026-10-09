module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonConsistency
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitFunctionalDensity
import Mathlib.Topology.TietzeExtension
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.JointQueryBorelDense

/-! # Compact tests on the closed infinite-horizon velocity-face carrier -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Topology
open SectionTwo TheoremA Evolution
open scoped CompactlySupported Topology

/-- The infinite exit carrier consists of the two genuine physical velocity faces. -/
def stripInfiniteFace (H : Interval) : Set Point :=
  {p | p.velocity 0 = H.lo ∨ p.velocity 0 = H.hi}

/-- The infinite velocity-face carrier is closed in the physical point topology. -/
theorem isClosed_stripInfiniteFace (H : Interval) : IsClosed (stripInfiniteFace H) :=
  (isClosed_eq ((continuous_apply 0).comp continuous_velocity) continuous_const).union
    (isClosed_eq ((continuous_apply 0).comp continuous_velocity) continuous_const)

/-- The face carrier inherits local compactness from physical Euclidean coordinates. -/
instance stripInfiniteFace_locallyCompactSpace (H : Interval) :
    LocallyCompactSpace (stripInfiniteFace H) := by
  let : LocallyCompactSpace Point :=
    (KineticPoint.homeomorphProd 1).isClosedEmbedding.locallyCompactSpace
  exact (isClosed_stripInfiniteFace H).locallyCompactSpace

/-- The face carrier inherits a countable topological basis. -/
instance stripInfiniteFace_secondCountableTopology (H : Interval) :
    SecondCountableTopology (stripInfiniteFace H) := by
  let : SecondCountableTopology Point := (KineticPoint.homeomorphProd 1).secondCountableTopology
  infer_instance

/-- Restriction of an ambient smooth probe to the closed physical exit carrier. -/
def infiniteExitProbeCc (H : Interval) (f : exitProbeSubmodule) :
    C_c(stripInfiniteFace H, ℝ) where
  toFun p := exitProbePhysical f p.1
  continuous_toFun := (exitProbePhysical_continuous_compact f).1.comp continuous_subtype_val
  hasCompactSupport' := (exitProbePhysical_continuous_compact f).2.comp_isClosedEmbedding
    (isClosed_stripInfiniteFace H).isClosedEmbedding_subtypeVal

/-- Exit restriction is a linear map on the ambient probe vector space. -/
def infiniteExitProbeCcLinear (H : Interval) :
    exitProbeSubmodule →ₗ[ℝ] C_c(stripInfiniteFace H, ℝ) where
  toFun := infiniteExitProbeCc H
  map_add' f g := by ext p; rfl
  map_smul' c f := by ext p; rfl

/-- The dense restriction family is closed under squaring. -/
theorem infiniteExitProbeCc_sq (H : Interval) (f : exitProbeSubmodule) :
    ∃ g : exitProbeSubmodule,
      infiniteExitProbeCcLinear H g = infiniteExitProbeCcLinear H f * infiniteExitProbeCcLinear H
        f := by
  refine ⟨⟨fun x => f.1 x * f.1 x, f.2.1.mul f.2.1, f.2.2.mul_left⟩, ?_⟩
  ext p
  rfl

/-- Smooth compact ambient restrictions uniformly approximate every compact exit datum. -/
theorem infiniteExitProbeCc_dense (H : Interval) (g : C_c(stripInfiniteFace H, ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ f : exitProbeSubmodule, ∀ p, |infiniteExitProbeCcLinear H f p - g p| ≤ ε := by
  let j : stripInfiniteFace H → EvolutionVec 1 :=
    fun p => reconstructionPhysicalHomeomorph.symm p.1
  have hj : IsClosedEmbedding j := reconstructionPhysicalHomeomorph.symm.isClosedEmbedding.comp
    (isClosed_stripInfiniteFace H).isClosedEmbedding_subtypeVal
  obtain ⟨G, -, hG⟩ := BoundedContinuousFunction.exists_extension_norm_eq_of_isClosedEmbedding
    g.toBoundedContinuousFunction hj
  have hK : IsCompact (j '' tsupport (g : stripInfiniteFace H → ℝ)) :=
    g.hasCompactSupport.isCompact.image hj.continuous
  obtain ⟨χ, hχ, hc, -, -, hone⟩ :=
    exists_smooth_bump_of_isCompact_subset_isOpen hK isOpen_univ (subset_univ _)
  let F : C_c(EvolutionVec 1, ℝ) :=
    ⟨⟨fun x => χ x * G x, hχ.continuous.mul G.continuous⟩, hc.mul_right⟩
  have hFg (p : stripInfiniteFace H) : F (j p) = g p := by
    have hh : G (j p) = g p := congrFun hG p
    by_cases hp : g p = 0
    · change χ (j p) * G (j p) = g p
      rw [hh, hp, mul_zero]
    · change χ (j p) * G (j p) = g p
      rw [hone _ ⟨p, subset_tsupport _ hp, rfl⟩, one_mul, hh]
  obtain ⟨f, hf, hclose⟩ := exists_smooth_compact_probe_close F ε hε
  refine ⟨⟨f, hf, f.hasCompactSupport⟩, fun p => ?_⟩
  have hh := hclose (j p)
  rw [hFg p] at hh
  exact hh

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

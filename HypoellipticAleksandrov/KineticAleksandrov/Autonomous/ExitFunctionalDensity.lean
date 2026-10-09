module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitFunctionalProbes
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.JointQueryBorelDense
import Mathlib.Topology.TietzeExtension

/-! # Uniform density of smooth ambient restrictions on the closed exit carrier -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Topology
open SectionTwo TheoremA Evolution
open scoped CompactlySupported Topology

/-- Restriction of an ambient smooth probe to the closed physical exit carrier. -/
def exitProbeCc (H : Interval) (T : ℝ) (f : exitProbeSubmodule) :
    C_c(stripClosedExit H T, ℝ) where
  toFun p := exitProbePhysical f p.1
  continuous_toFun := (exitProbePhysical_continuous_compact f).1.comp continuous_subtype_val
  hasCompactSupport' := (exitProbePhysical_continuous_compact f).2.comp_isClosedEmbedding
    (isClosed_stripClosedExit H T).isClosedEmbedding_subtypeVal

/-- Exit restriction is a linear map on the ambient probe vector space. -/
def exitProbeCcLinear (H : Interval) (T : ℝ) :
    exitProbeSubmodule →ₗ[ℝ] C_c(stripClosedExit H T, ℝ) where
  toFun := exitProbeCc H T
  map_add' f g := by ext p; rfl
  map_smul' c f := by ext p; rfl

/-- The dense restriction family is closed under squaring. -/
theorem exitProbeCc_sq (H : Interval) (T : ℝ) (f : exitProbeSubmodule) :
    ∃ g : exitProbeSubmodule,
      exitProbeCcLinear H T g = exitProbeCcLinear H T f * exitProbeCcLinear H T f := by
  refine ⟨⟨fun x => f.1 x * f.1 x, f.2.1.mul f.2.1, f.2.2.mul_left⟩, ?_⟩
  ext p
  rfl

/-- Smooth compact ambient restrictions uniformly approximate every compact exit datum. -/
theorem exitProbeCc_dense (H : Interval) (T : ℝ) (g : C_c(stripClosedExit H T, ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ f : exitProbeSubmodule, ∀ p, |exitProbeCcLinear H T f p - g p| ≤ ε := by
  let j : stripClosedExit H T → EvolutionVec 1 :=
    fun p => reconstructionPhysicalHomeomorph.symm p.1
  have hj : IsClosedEmbedding j := reconstructionPhysicalHomeomorph.symm.isClosedEmbedding.comp
    (isClosed_stripClosedExit H T).isClosedEmbedding_subtypeVal
  obtain ⟨G, -, hG⟩ := BoundedContinuousFunction.exists_extension_norm_eq_of_isClosedEmbedding
    g.toBoundedContinuousFunction hj
  have hK : IsCompact (j '' tsupport (g : stripClosedExit H T → ℝ)) :=
    g.hasCompactSupport.isCompact.image hj.continuous
  obtain ⟨χ, hχ, hc, -, -, hone⟩ :=
    exists_smooth_bump_of_isCompact_subset_isOpen hK isOpen_univ (subset_univ _)
  let F : C_c(EvolutionVec 1, ℝ) :=
    ⟨⟨fun x => χ x * G x, hχ.continuous.mul G.continuous⟩, hc.mul_right⟩
  have hFg (p : stripClosedExit H T) : F (j p) = g p := by
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

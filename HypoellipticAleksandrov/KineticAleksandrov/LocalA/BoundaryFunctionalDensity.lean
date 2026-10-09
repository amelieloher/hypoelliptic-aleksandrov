module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundaryFunctionalProbes
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.JointQueryBorelDense
import Mathlib.Topology.TietzeExtension
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.DomainDominationMeasure

/-! # Uniform density of ambient smooth traces on the actual closed boundary -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Evolution Topology
open scoped CompactlySupported Topology

/-- Every compact continuous datum on the closed trace is uniformly approximated by probes. -/
theorem boundaryProbeCc_dense {d : ℕ} (a T : ℝ) (v₀ : PDE.Vec d) (R : ℝ)
    (g : C_c(localTrace a T v₀ R, ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ f : boundaryProbeSubmodule d,
      ∀ P, |boundaryProbeCcLinear a T v₀ R f P - g P| ≤ ε := by
  let j : localTrace a T v₀ R → ℝ × PDE.Vec d × PDE.Vec d :=
    fun P => (KineticPoint.homeomorphProd d) P.1
  have hj : IsClosedEmbedding j := (KineticPoint.homeomorphProd d).isClosedEmbedding.comp
    (isClosed_localTrace a T v₀ R).isClosedEmbedding_subtypeVal
  obtain ⟨G, -, hG⟩ := BoundedContinuousFunction.exists_extension_norm_eq_of_isClosedEmbedding
    g.toBoundedContinuousFunction hj
  have hK : IsCompact (j '' tsupport (g : localTrace a T v₀ R → ℝ)) :=
    g.hasCompactSupport.isCompact.image hj.continuous
  obtain ⟨χ, hχ, hc, -, -, hone⟩ :=
    exists_smooth_bump_of_isCompact_subset_isOpen hK isOpen_univ (subset_univ _)
  let F : C_c(ℝ × PDE.Vec d × PDE.Vec d, ℝ) :=
    ⟨⟨fun q => χ q * G q, hχ.continuous.mul G.continuous⟩, hc.mul_right⟩
  have hFg (P : localTrace a T v₀ R) : F (j P) = g P := by
    have heq : G (j P) = g P := congrFun hG P
    by_cases hP : g P = 0
    · change χ (j P) * G (j P) = g P
      rw [heq, hP, mul_zero]
    · change χ (j P) * G (j P) = g P
      rw [hone _ ⟨P, subset_tsupport _ hP, rfl⟩, one_mul, heq]
  obtain ⟨f, hf, hclose⟩ := exists_smooth_compact_probe_close F ε hε
  refine ⟨⟨f, hf, f.hasCompactSupport⟩, ?_⟩
  intro P
  have h := hclose (j P)
  rw [hFg] at h
  exact h

end HypoellipticAleksandrov.KineticAleksandrov.LocalA

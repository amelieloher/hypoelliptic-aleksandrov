module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundaryFunctionalProbes
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.MassRepresentationGrowth
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.DomainDominationMeasure
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.JointQueryBorelDense
import Mathlib.Topology.TietzeExtension

/-! # Uniformly bounded smooth approximation on compact position portions of the trace -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic Topology
open scoped CompactlySupported

/-- Bounded continuous closed-strip data have smooth compact trace approximations. -/
theorem exists_mass_trace_probe {d : ℕ} (a T : ℝ) (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)
    (u : KineticPoint d → ℝ) (hc : ContinuousOn u (localClosedStrip a T v₀ R))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ P ∈ localClosedStrip a T v₀ R, |u P| ≤ M)
    (L ε : ℝ) (hε : 0 < ε) :
    ∃ F : boundaryProbeSubmodule d,
      (∀ P, |boundaryProbePhysical F P| ≤ M + ε) ∧
      ∀ P ∈ localClosedStrip a T v₀ R, ‖P.position‖ ≤ L →
        |boundaryProbePhysical F P - u P| ≤ ε := by
  let D := localClosedStrip a T v₀ R
  let f : BoundedContinuousFunction D ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun P => u P.1) (continuousOn_iff_continuous_domRestrict.mp hc) M
      (fun P => by rw [Real.norm_eq_abs]; exact hb P.1 P.2)
  let H := KineticPoint.homeomorphProd d
  let j : D → ℝ × PDE.Vec d × PDE.Vec d := fun P => H P.1
  have hj : IsClosedEmbedding j := H.isClosedEmbedding.comp
    (isClosed_localClosedStrip a T v₀ R).isClosedEmbedding_subtypeVal
  obtain ⟨G, hGb, hG⟩ :=
    BoundedContinuousFunction.exists_extension_forall_mem_Icc_of_isClosedEmbedding f
      (fun P => abs_le.mp (hb P.1 P.2)) (by linarith only [hM]) hj
  let K := Icc a T ×ˢ (Metric.closedBall (0 : PDE.Vec d) L ×ˢ PDE.euclideanClosedBall v₀ R)
  have hK : IsCompact K := isCompact_Icc.prod
    ((ProperSpace.isCompact_closedBall 0 L).prod (PDE.isCompact_euclideanClosedBall v₀ hR.le))
  obtain ⟨χ, hχ, hcc, _, hcb, hone⟩ :=
    exists_smooth_bump_of_isCompact_subset_isOpen hK isOpen_univ (subset_univ _)
  let g : C_c(ℝ × PDE.Vec d × PDE.Vec d, ℝ) :=
    ⟨⟨fun x => χ x * G x, hχ.continuous.mul G.continuous⟩, hcc.mul_right⟩
  obtain ⟨s, hs, hclose⟩ := exists_smooth_compact_probe_close g ε hε
  let F : boundaryProbeSubmodule d := ⟨s, hs, s.hasCompactSupport⟩
  have hg (x) : |g x| ≤ M := by
    change |χ x * G x| ≤ M
    rw [abs_mul, abs_of_nonneg (hcb x).1]
    exact (mul_le_of_le_one_left (abs_nonneg _) (hcb x).2).trans (abs_le.mpr (hGb x))
  refine ⟨F, ?_, ?_⟩
  · intro P
    have hh := (abs_add_le (s (H P) - g (H P)) (g (H P))).trans
      (add_le_add (hclose _) (hg _))
    rw [sub_add_cancel] at hh
    exact hh.trans_eq (add_comm ε M)
  · intro P hP hL
    have hv : P.velocity ∈ PDE.euclideanClosedBall v₀ R :=
      (closure_minimal (PDE.euclideanBall_subset_euclideanClosedBall v₀ R)
        (PDE.isClosed_euclideanClosedBall v₀ R)) hP.2.2
    have hpK : H P ∈ K := ⟨⟨hP.1, hP.2.1⟩,
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using! hL), hv⟩
    have hGj : G (H P) = u P := congrFun hG ⟨P, hP⟩
    have hgp : g (H P) = u P := by
      change χ (H P) * G (H P) = u P
      rw [hone _ hpK, one_mul, hGj]
    have hh := hclose (H P)
    rw [hgp] at hh
    exact hh

end HypoellipticAleksandrov.KineticAleksandrov.LocalA

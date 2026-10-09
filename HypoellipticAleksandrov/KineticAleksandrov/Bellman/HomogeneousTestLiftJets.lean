module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftDerivative
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic

/-! # Directional jets of the radial test lift -/

@[expose] public section
noncomputable section
open Set MeasureTheory Filter Topology
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- The first position derivative is the lift of the first test jet with its shifted weight. -/
theorem bellman_lift_dx (alpha : ℝ) (zeta : (ℝ × ℝ) → ℝ)
    (hz : ContDiffOn ℝ 1 zeta bellmanPuncturedSet) (hc : HasCompactSupport zeta)
    (hs : tsupport zeta ⊆ bellmanPuncturedSet) (q : ℝ × ℝ)
    (hq : q ∈ bellmanPuncturedSet) :
    bellmanDx (lift alpha zeta) q = lift (alpha - 3) (bellmanDx zeta) q := by
  rw [bellmanDx, bellman_lift_fderiv alpha zeta hz hc hs q hq, lift]
  apply integral_congr_ae
  apply ae_of_all
  intro r
  dsimp only
  have hv : bellmanDilationLinear r.val ((1 : ℝ), 0) = r.val ^ 3 • ((1 : ℝ), 0) := by
    simp [bellmanDilationLinear, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  rw [hv, map_smul, smul_eq_mul, ← mul_assoc]
  have hp : r.val ^ (-1 - alpha) * r.val ^ 3 = r.val ^ (-1 - (alpha - 3)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add r.property]
    congr 1
    ring
  rw [hp]
  rfl

/-- The first velocity derivative is the lift of the first test jet with its shifted weight. -/
theorem bellman_lift_dv (alpha : ℝ) (zeta : (ℝ × ℝ) → ℝ)
    (hz : ContDiffOn ℝ 1 zeta bellmanPuncturedSet) (hc : HasCompactSupport zeta)
    (hs : tsupport zeta ⊆ bellmanPuncturedSet) (q : ℝ × ℝ)
    (hq : q ∈ bellmanPuncturedSet) :
    bellmanDv (lift alpha zeta) q = lift (alpha - 1) (bellmanDv zeta) q := by
  rw [bellmanDv, bellman_lift_fderiv alpha zeta hz hc hs q hq, lift]
  apply integral_congr_ae
  apply ae_of_all
  intro r
  dsimp only
  have hv : bellmanDilationLinear r.val ((0 : ℝ), 1) = r.val • ((0 : ℝ), 1) := by
    simp [bellmanDilationLinear, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  rw [hv, map_smul, smul_eq_mul, ← mul_assoc]
  have hp : r.val ^ (-1 - alpha) * r.val = r.val ^ (-1 - (alpha - 1)) := by
    nth_rw 2 [← Real.rpow_one r.val]
    rw [← Real.rpow_add r.property]
    congr 1
    ring
  rw [hp]
  rfl

/-- The second velocity derivative is the lift of the second test jet with its shifted weight. -/
theorem bellman_lift_dvv (alpha : ℝ) (zeta : (ℝ × ℝ) → ℝ)
    (hz : ContDiffOn ℝ 2 zeta bellmanPuncturedSet) (hc : HasCompactSupport zeta)
    (hs : tsupport zeta ⊆ bellmanPuncturedSet) (q : ℝ × ℝ)
    (hq : q ∈ bellmanPuncturedSet) :
    bellmanDvv (lift alpha zeta) q = lift (alpha - 2) (bellmanDvv zeta) q := by
  have hv : ContDiffOn ℝ 1 (bellmanDv zeta) bellmanPuncturedSet :=
    (hz.fderiv_of_isOpen bellmanPuncturedSet_isOpen (m := 1) (by norm_num)).clm_apply
      contDiffOn_const
  have he : bellmanDv (lift alpha zeta) =ᶠ[𝓝 q] lift (alpha - 1) (bellmanDv zeta) := by
    filter_upwards [bellmanPuncturedSet_isOpen.mem_nhds hq] with x hx
    exact bellman_lift_dv alpha zeta (hz.of_le (by norm_num)) hc hs x hx
  change fderiv ℝ (bellmanDv (lift alpha zeta)) q (0, 1) = _
  rw [he.fderiv_eq]
  change bellmanDv (lift (alpha - 1) (bellmanDv zeta)) q = _
  rw [bellman_lift_dv (alpha - 1) (bellmanDv zeta) hv (hc.fderiv_apply ℝ (0, 1))
    ((tsupport_fderiv_apply_subset ℝ (0, 1)).trans hs) q hq]
  have heq : alpha - 1 - 1 = alpha - 2 := by ring
  rw [heq]
  rfl

end HypoellipticAleksandrov.KineticAleksandrov

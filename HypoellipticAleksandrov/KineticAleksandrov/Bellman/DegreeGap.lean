module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.Exponent
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.VagueAdjointLimit
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HighDegreeExclusion
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureStationary
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! # Strict upper gap for the homogeneous adjoint exponent -/

@[expose] public section
noncomputable section
open Set MeasureTheory Filter Topology
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- Degree two provides the lower bound for the chosen exponent. -/
theorem bellmanAdjointExponent_two_le (R : ℝ) (hR : 1 ≤ R) :
    2 ≤ bellmanAdjointExponent R hR :=
  (bellmanAdjointExponent_characterization R hR).1.1
    (two_mem_bellmanAdmissibleDegrees R hR)

/-- The excluded endpoint remains excluded after taking the supremum of admissible degrees. -/
theorem bellmanAdjointExponent_lt_three (R : ℝ) (hR : 1 ≤ R) :
    bellmanAdjointExponent R hR < 3 := by
  have hlu := (bellmanAdjointExponent_characterization R hR).1
  have hle : bellmanAdjointExponent R hR ≤ 3 :=
    hlu.2 (fun b hb => (admissible_degree_lt_three R hR b hb).le)
  by_contra hlt
  have heq : bellmanAdjointExponent R hR = 3 := le_antisymm hle (le_of_not_gt hlt)
  have hex (n : ℕ) : ∃ b ∈ bellmanAdmissibleDegrees R,
      3 - 1 / ((n : ℝ) + 1) < b ∧ b ≤ 3 := by
    have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
    simpa only [heq] using hlu.exists_between (by rw [heq]; linarith)
  choose beta hb hlo hhi using hex
  have hpairs (n : ℕ) : ∃ mu eta : Measure BellmanPuncturedPlane,
      IsBellmanAdjointPair 1 R (beta n) mu eta :=
    (mem_bellmanAdmissibleDegrees_iff R (beta n)).mp (hb n)
  choose mu eta hp using hpairs
  have hbeta : Tendsto beta atTop (𝓝 (3 : ℝ)) := by
    have ht : Tendsto (fun n : ℕ => 3 - 1 / ((n : ℝ) + 1)) atTop (𝓝 3) := by
      simpa using (tendsto_const_nhds (x := (3 : ℝ))).sub
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le ht tendsto_const_nhds
      (fun n => (hlo n).le) hhi
  have hbounded : ∃ a b : ℝ, ∀ n, a ≤ beta n ∧ beta n ≤ b := by
    refine ⟨2, 3, fun n => ⟨?_, hhi n⟩⟩
    have hd : 1 ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    have hi : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr hd
    linarith [hlo n]
  obtain ⟨chi, hchi, hc, hs, _, _, _, c, hcp, hcn, k, hk,
    muInf, etaInf, hmInf, heInf, hmv, hev⟩ :=
    homogeneous_pairs_subsequence R hR beta mu eta hp hbounded
  have hs0 : tsupport chi ⊆ {q | q ≠ (0, 0)} := by
    intro q hq hz
    have hg := (hs hq).1
    rw [hz] at hg
    norm_num [bellmanGauge, bellmanGaugePower] at hg
  have hlim := bellman_vague_limit_pair R 3 hR (fun n => beta (k n))
    (fun n => ENNReal.ofReal (c (k n)) • mu (k n))
    (fun n => ENNReal.ofReal (c (k n)) • eta (k n)) muInf etaInf
    (hbeta.comp hk.tendsto_atTop)
    (fun n => (hp (k n)).smul (c (k n)) (hcp (k n)))
    hmInf heInf hmv hev chi hchi.continuous hc hs0 (fun n => hcn (k n))
  have hmem : 3 ∈ bellmanAdmissibleDegrees R :=
    (mem_bellmanAdmissibleDegrees_iff R 3).mpr ⟨muInf, etaInf, hlim.1⟩
  exact (lt_irrefl (3 : ℝ)) (admissible_degree_lt_three R hR 3 hmem)

/-- The normalized homogeneous adjoint exponent lies in the source's half-open interval. -/
theorem bellmanAdjointExponent_range (R : ℝ) (hR : 1 ≤ R) :
    2 ≤ bellmanAdjointExponent R hR ∧ bellmanAdjointExponent R hR < 3 :=
  ⟨bellmanAdjointExponent_two_le R hR, bellmanAdjointExponent_lt_three R hR⟩

end HypoellipticAleksandrov.KineticAleksandrov

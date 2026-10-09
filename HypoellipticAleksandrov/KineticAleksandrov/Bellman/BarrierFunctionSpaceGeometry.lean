module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.Geometry
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-! # The literal anisotropic sphere and diffusion interval -/

@[expose] public section
noncomputable section
open Set
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- The unit sphere of the source gauge. -/
abbrev BellmanSphere := {q : ℝ × ℝ // bellmanGauge q = 1}

/-- The closed source diffusion interval. -/
abbrev BellmanCoefficient (lam Lam : ℝ) := {b : ℝ // b ∈ Icc lam Lam}

/-- The gauge polynomial is continuous. -/
theorem bellmanGaugePower_continuous : Continuous bellmanGaugePower := by
  exact (continuous_fst.pow 2).add (continuous_snd.pow 6)

/-- The source gauge is continuous, including at the origin. -/
theorem bellmanGauge_continuous : Continuous bellmanGauge := by
  exact (Real.continuous_rpow_const (by norm_num : 0 ≤ (1 / 6 : ℝ))).comp
    bellmanGaugePower_continuous

/-- Raising the gauge to the sixth power recovers its polynomial. -/
theorem bellmanGauge_pow_six (q : ℝ × ℝ) :
    bellmanGauge q ^ 6 = bellmanGaugePower q := by
  simpa only [bellmanGauge, one_div, Nat.cast_ofNat] using
    Real.rpow_inv_natCast_pow (bellmanGaugePower_nonneg q) (by decide : (6 : ℕ) ≠ 0)

/-- A point on the anisotropic sphere is away from the origin. -/
theorem BellmanSphere.ne_zero (z : BellmanSphere) : z.val ≠ (0, 0) := by
  intro hz
  have h := z.property
  rw [hz] at h
  norm_num [bellmanGauge, bellmanGaugePower] at h

/-- The source sphere is a compact subset of the literal product plane. -/
theorem bellmanSphere_isCompact : IsCompact {q : ℝ × ℝ | bellmanGauge q = 1} := by
  have hc : IsClosed {q : ℝ × ℝ | bellmanGauge q = 1} :=
    isClosed_eq bellmanGauge_continuous continuous_const
  apply ((isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)).prod
    (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1))).of_isClosed_subset hc
  intro q hq
  have hp : q.1 ^ 2 + q.2 ^ 6 = 1 := by
    have h := bellmanGauge_pow_six q
    rw [hq] at h
    simpa only [one_pow, bellmanGaugePower] using h.symm
  have hx : q.1 ^ 2 ≤ 1 := by
    nlinarith only [hp, Even.pow_nonneg (by decide : Even 6) q.2]
  have hv : q.2 ^ 6 ≤ 1 := by nlinarith only [hp, sq_nonneg q.1]
  have hv2 : q.2 ^ 2 ≤ 1 := by
    by_contra h
    have hs : 1 < q.2 ^ 2 := lt_of_not_ge h
    have ht : 1 < (q.2 ^ 2) ^ 3 := one_lt_pow₀ hs (by decide)
    nlinarith only [hv, ht]
  exact ⟨⟨by nlinarith only [hx], by nlinarith only [hx]⟩,
    ⟨by nlinarith only [hv2], by nlinarith only [hv2]⟩⟩

/-- The anisotropic unit sphere carries its proved compact topology. -/
instance : CompactSpace BellmanSphere :=
  isCompact_iff_compactSpace.mp bellmanSphere_isCompact

/-- The source coefficient interval is a compact carrier. -/
instance (lam Lam : ℝ) : CompactSpace (BellmanCoefficient lam Lam) :=
  isCompact_iff_compactSpace.mp isCompact_Icc

/-- The source sphere is nonempty, independently of the coefficient interval. -/
instance : Nonempty BellmanSphere := by
  refine ⟨⟨(1, 0), ?_⟩⟩
  norm_num [bellmanGauge, bellmanGaugePower]

/-- An ordered coefficient interval contains its left endpoint. -/
theorem bellmanCoefficient_nonempty (lam Lam : ℝ) (h : lam ≤ Lam) :
    Nonempty (BellmanCoefficient lam Lam) := ⟨⟨lam, le_rfl, h⟩⟩

end HypoellipticAleksandrov.KineticAleksandrov

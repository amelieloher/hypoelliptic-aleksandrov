module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ExtensionContinuity
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoffGlobalJets
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.Order.Compact

/-! # A smooth velocity cutoff realizes the literal zero extension -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Set

/-- The compact profile domain has a uniform strict squared-velocity margin. -/
theorem construction_exists_velocity_margin {d : ℕ} {alpha : ℝ}
    (ha : 0 < alpha) (h : CounterProfileStatement d alpha) (R : ℝ)
    (hvel : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < R ^ 2) :
    ∃ m : ℝ, m < R ^ 2 ∧ ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 ≤ m := by
  have hK := isCompact_profile_unit_sublevel ha h
  have hzero := (selectedProfile_spec h).2.2.2.2.2.2.2.1
  have hne : ({q : XV d | profileFunction h q ≤ 1} : Set (XV d)).Nonempty :=
    ⟨0, by change profileFunction h 0 ≤ 1; rw [hzero]; norm_num⟩
  have hc : Continuous (fun q : XV d => PDE.vecNormSq q.2) :=
    PDE.contDiff_vecNormSq.continuous.comp continuous_snd
  obtain ⟨q, hq, hmax⟩ := hK.exists_isMaxOn hne hc.continuousOn
  exact ⟨PDE.vecNormSq q.2, hvel q hq, fun z hz => hmax hz⟩

/-- The velocity cutoff is one on the profile domain and zero beyond the barrier radius. -/
def constructionVelocityCutoff {d : ℕ} (m R : ℝ) (q : XV d) : ℝ :=
  1 - Real.smoothTransition ((PDE.vecNormSq q.2 - m) / (R ^ 2 - m))

/-- The cutoff uses a smooth polynomial Euclidean squared norm. -/
theorem contDiff_providerVelocityCutoff (d : ℕ) (m R : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (constructionVelocityCutoff (d := d) m R) := by
  exact contDiff_const.sub (Real.smoothTransition.contDiff.comp
    (((PDE.contDiff_vecNormSq.comp contDiff_snd).sub contDiff_const).div_const _))

/-- The cutoff equals one below the inner squared-velocity threshold. -/
theorem constructionVelocityCutoff_eq_one {d : ℕ} (m R : ℝ) (hm : m < R ^ 2)
    (q : XV d) (hq : PDE.vecNormSq q.2 ≤ m) : constructionVelocityCutoff m R q = 1 := by
  unfold constructionVelocityCutoff
  rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr hq) (sub_pos.mpr hm).le), sub_zero]

/-- The cutoff is zero at and beyond the barrier radius. -/
theorem constructionVelocityCutoff_eq_zero {d : ℕ} (m R : ℝ) (hm : m < R ^ 2)
    (q : XV d) (hq : R ^ 2 ≤ PDE.vecNormSq q.2) : constructionVelocityCutoff m R q = 0 := by
  unfold constructionVelocityCutoff
  rw [Real.smoothTransition.one_of_one_le
    ((le_div_iff₀ (sub_pos.mpr hm)).mpr (by simpa only [one_mul] using sub_le_sub_right hq m)),
    sub_self]

/-- Multiplying the raw cutoff by the smooth velocity cutoff is exactly the zero extension.
This equality holds at every time, including the initial zero interval. -/
theorem construction_zero_extension_eq_cutoff {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R m : ℝ)
    (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R) (hm : m < R ^ 2)
    (hscale : 2 * Real.rpow r alpha ≤ 1)
    (hmargin : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 ≤ m)
    (P : KineticPoint d) :
    zeroExtendedProfile (profileFunction h) alpha r mu R P =
      constructionVelocityCutoff m R (P.position, P.velocity) *
        timeCutoffProfile (profileFunction h) alpha r mu R P := by
  have hvel : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < R ^ 2 :=
    fun q hq => (hmargin q hq).trans_lt hm
  by_cases hq : profileFunction h (P.position, P.velocity) < 1
  · rw [constructionVelocityCutoff_eq_one m R hm _ (hmargin _ hq.le), one_mul]
    exact zeroExtendedProfile_eq_raw_on_profile _ alpha r mu R hr hmu hR hvel P hq
  · rw [zeroExtendedProfile_eq_zero_of_profile _ alpha r mu R P (not_lt.mp hq)]
    by_cases hc : constructionVelocityCutoff m R (P.position, P.velocity) = 0
    · rw [hc, zero_mul]
    · have hv : PDE.vecNormSq P.velocity < R ^ 2 := by
        by_contra hn
        exact hc (constructionVelocityCutoff_eq_zero m R hm _ (not_lt.mp hn))
      have hf := flatProfile_eq_one_sub (profileFunction h) alpha r hr
        (P.position, P.velocity) (hscale.trans (not_lt.mp hq))
      have hb : 0 < barrier mu R P := by
        unfold barrier
        exact mul_pos (Real.exp_pos _) (by
          have hh := (div_lt_one (sq_pos_of_pos hR)).mpr hv
          linarith)
      have hu : timeCutoffProfile (profileFunction h) alpha r mu R P = 0 := by
        unfold timeCutoffProfile
        rw [hf]
        apply timeCutoffTheta_eq_zero
        linarith [not_lt.mp hq]
      rw [hu, mul_zero]

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningWeakConvergence
import Mathlib.Tactic.GCongr

/-! # Uniform bounds for flattened smooth approximations on punctured compact sets -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Filter Set Metric

/-- Multiplication by the negative flattening slope preserves an absolute bound. -/
theorem abs_flatSlope_mul_le (s g M : ℝ) (hg : |g| ≤ M) :
    |(-deriv flatteningPsi s) * g| ≤ M := by
  rw [abs_mul, abs_neg]
  have hs : |deriv flatteningPsi s| ≤ 1 := by
    rw [abs_of_nonneg (flatteningPsi_deriv_bounds s).1]
    exact (flatteningPsi_deriv_bounds s).2
  calc
    _ ≤ 1 * M := mul_le_mul hs hg (abs_nonneg _) (by norm_num)
    _ = M := one_mul _

/-- The nonlinear Hessian correction is uniformly bounded on bounded first and second jets. -/
theorem abs_flatSecond_le (s gi gk hij alpha r M P : ℝ) (hr : 0 < r) (hM : 0 ≤ M)
    (hi : |gi| ≤ M) (hk : |gk| ≤ M) (hh : |hij| ≤ M)
    (hP : 0 ≤ P) (hp : deriv (deriv flatteningPsi) s ≤ P) :
    |-deriv flatteningPsi s * hij - Real.rpow r (-alpha) *
        deriv (deriv flatteningPsi) s * gi * gk| ≤ M + Real.rpow r (-alpha) * P * M ^ 2 := by
  simp only [Real.rpow_eq_pow]
  have hpow : 0 ≤ r ^ (-alpha) := (Real.rpow_pos_of_pos hr (-alpha)).le
  have hpabs : |deriv (deriv flatteningPsi) s| ≤ P := by
    rw [abs_of_nonneg (flatteningPsi_deriv2_nonneg s)]
    exact hp
  calc
    _ ≤ |(-deriv flatteningPsi s) * hij| +
        |r ^ (-alpha) * deriv (deriv flatteningPsi) s * gi * gk| := abs_sub _ _
    _ ≤ M + r ^ (-alpha) * P * M ^ 2 := by
      apply add_le_add (abs_flatSlope_mul_le s hij M hh)
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hpow, pow_two]
      calc
        _ ≤ r ^ (-alpha) * P * M * M := by gcongr
        _ = _ := by ring

/-- The unflattened approximations and all their classical jets have one eventual compact bound. -/
theorem mollifiedProfile_eventually_bounded {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (K : Set (XV d)) (hK : IsCompact K) (hz : 0 ∉ K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ n in atTop, ∀ q ∈ K,
      ‖mollifiedProfile h n q‖ ≤ M ∧
      (∀ i, |dx (mollifiedProfile h n) q i| ≤ M) ∧
      (∀ i, |dv (mollifiedProfile h n) q i| ≤ M) ∧
      (∀ i k, |dvv (mollifiedProfile h n) q i k| ≤ M) := by
  have hH := (selectedProfile_spec h).2.2.2.2.2.2.1
  have hmx := (selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.1
  have hmv := (selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.1
  have hmh := (selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.1
  have hb := (selectedProfile_spec h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hsub : K ⊆ ({0}ᶜ : Set (XV d)) := by
    intro q hq
    change q ≠ 0
    intro he
    exact hz (he ▸ hq)
  obtain ⟨delta, hd, hdelta⟩ := hK.exists_cthickening_subset_open isOpen_compl_singleton hsub
  let L := cthickening delta K
  have hL : IsCompact L := hK.cthickening
  obtain ⟨MH, hMH⟩ := hL.exists_bound_of_continuousOn hH.continuousOn
  obtain ⟨MG, hMG⟩ := hb L hL (fun hmem => by simpa using hdelta hmem)
  let M := max 0 (max MH MG)
  have hM : 0 ≤ M := le_max_left _ _
  have hHM : MH ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hGM : MG ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨M, hM, ?_⟩
  have he : ∀ᶠ n in atTop, (standardMollifierSequence (G := XV d) n).rOut < delta :=
    standardMollifierSequence_rOut_tendsto.eventually (gt_mem_nhds hd)
  filter_upwards [he] with n hn
  intro q hq
  have hyL (y : XV d) (hy : y ∈ ball q (standardMollifierSequence n).rOut) : y ∈ L :=
    mem_cthickening_of_dist_le y q delta K hq ((mem_ball.mp hy).le.trans hn.le)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact spatialMollify_norm_le_on_ball _ _ hH.aestronglyMeasurable M hM q
      (fun y hy => (hMH y (hyL y hy)).trans hHM)
  · intro i
    rw [dx_mollifiedProfile, ← Real.norm_eq_abs]
    apply spatialMollify_norm_le_on_ball _ _
      (((measurable_pi_apply i).comp hmx).aestronglyMeasurable) M hM q
    intro y hy
    exact (norm_le_pi_norm (profilePositionJet h y) i).trans ((hMG y (hyL y hy)).1.trans hGM)
  · intro i
    rw [dv_mollifiedProfile, ← Real.norm_eq_abs]
    apply spatialMollify_norm_le_on_ball _ _
      (((measurable_pi_apply i).comp hmv).aestronglyMeasurable) M hM q
    intro y hy
    exact (norm_le_pi_norm (profileVelocityJet h y) i).trans ((hMG y (hyL y hy)).2.1.trans hGM)
  · intro i k
    rw [dvv_mollifiedProfile, ← Real.norm_eq_abs]
    apply spatialMollify_norm_le_on_ball _ _ (hmh i k).aestronglyMeasurable M hM q
    intro y hy
    simpa only [Real.norm_eq_abs] using ((hMG y (hyL y hy)).2.2 i k).trans hGM

/-- The flattened values and all jets have one eventual bound on each punctured compact set. -/
theorem mollifiedFlatProfile_eventually_bounded {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r)
    (K : Set (XV d)) (hK : IsCompact K) (hz : 0 ∉ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ q ∈ K,
      ‖mollifiedFlatProfile h r n q‖ ≤ C ∧
      (∀ i, |dx (mollifiedFlatProfile h r n) q i| ≤ C) ∧
      (∀ i, |dv (mollifiedFlatProfile h r n) q i| ≤ C) ∧
      (∀ i k, |dvv (mollifiedFlatProfile h r n) q i k| ≤ C) := by
  obtain ⟨M, hM, he⟩ := mollifiedProfile_eventually_bounded h K hK hz
  obtain ⟨P, hP, hp⟩ := flatteningPsi_deriv2_bound
  let B := 1 + |flatteningOffset| * Real.rpow r alpha + M
  let D := M + Real.rpow r (-alpha) * P * M ^ 2
  let C := max B D
  have hR : 0 ≤ Real.rpow r (-alpha) := (Real.rpow_pos_of_pos hr (-alpha)).le
  have hD : M ≤ D := le_add_of_nonneg_right
    (mul_nonneg (mul_nonneg hR hP.le) (sq_nonneg M))
  have hDC : D ≤ C := le_max_right _ _
  have hBC : B ≤ C := le_max_left _ _
  refine ⟨C, hM.trans (hD.trans hDC), ?_⟩
  filter_upwards [he] with n hn
  intro q hq
  obtain ⟨hH, hx, hv, hh⟩ := hn q hq
  have hdiff := (contDiff_mollifiedProfile h n).differentiable (by simp) q
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hHabs : |mollifiedProfile h n q| ≤ M := by
      simpa only [Real.norm_eq_abs] using hH
    have hv : |mollifiedFlatProfile h r n q| ≤ B :=
      (abs_flatProfile_le (mollifiedProfile h n) alpha r hr q).trans
        (add_le_add_right hHabs _)
    simpa only [Real.norm_eq_abs] using hv.trans hBC
  · intro i
    unfold dx mollifiedFlatProfile
    rw [fderiv_flatProfile _ _ _ hr q hdiff]
    change |-deriv flatteningPsi (mollifiedProfile h n q / Real.rpow r alpha) *
      dx (mollifiedProfile h n) q i| ≤ C
    exact (abs_flatSlope_mul_le _ _ M (hx i)).trans (hD.trans hDC)
  · intro i
    unfold dv mollifiedFlatProfile
    rw [fderiv_flatProfile _ _ _ hr q hdiff]
    change |-deriv flatteningPsi (mollifiedProfile h n q / Real.rpow r alpha) *
      dv (mollifiedProfile h n) q i| ≤ C
    exact (abs_flatSlope_mul_le _ _ M (hv i)).trans (hD.trans hDC)
  · intro i k
    rw [mollifiedFlatProfile, dvv_flatProfile_of_contDiffAt _ _ _ hr q
      ((contDiff_mollifiedProfile h n).contDiffAt.of_le (by simp)) i k]
    exact (abs_flatSecond_le _ _ _ _ alpha r M P hr hM (hv i) (hv k) (hh i k)
      hP.le (hp _)).trans hDC

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

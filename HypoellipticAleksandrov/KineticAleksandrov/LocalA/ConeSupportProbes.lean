module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ConeSupportOrder
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # Compact smooth exhaustion of the bounded directional cone probes -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set Filter MeasureTheory Parabolic SectionTwo
open scoped Topology

/-- Compact ambient cutoffs expanding to every physical point. -/
def coneAmbientBump (d n : ℕ) : ContDiffBump (0 : ℝ × PDE.Vec d × PDE.Vec d) :=
  ⟨(n : ℝ) + 1, 2 * ((n : ℝ) + 1), by positivity, by
    have hn : 0 < (n : ℝ) + 1 := by positivity
    linarith only [hn]⟩

/-- The ambient cutoff is eventually one at every fixed point. -/
theorem coneAmbientBump_tendsto (d : ℕ) (P : KineticPoint d) :
    Tendsto (fun n => coneAmbientBump d n ((KineticPoint.equivProd d) P)) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop
    (‖(KineticPoint.equivProd d) P‖ : ℝ)] with n hn
  symm
  apply (coneAmbientBump d n).one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hn.trans (le_add_of_nonneg_right zero_le_one)

/-- A genuine smooth compact physical probe detecting the positive affine half-space. -/
def coneCompactProbe {d : ℕ} (α : ℝ) (e : PDE.Vec d) (γ : ℝ) (n : ℕ)
    (P : KineticPoint d) : ℝ :=
  expNegInvGlue (coneCoordinate α e γ P) *
    coneAmbientBump d n ((KineticPoint.equivProd d) P)

/-- The cutoff probe retains exactly the prescribed ambient smoothness. -/
theorem coneCompactProbe_smooth {d : ℕ} (α : ℝ) (e : PDE.Vec d) (γ : ℝ) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (coneCompactProbe α e γ n ∘ (KineticPoint.equivProd d).symm) := by
  have hs := (coneProbe_smooth α e γ).mul (coneAmbientBump d n).contDiff
  simpa only [coneCompactProbe, Function.comp_apply, Equiv.apply_symm_apply] using! hs

/-- Its support is compact in the actual physical carrier. -/
theorem coneCompactProbe_compact {d : ℕ} (α : ℝ) (e : PDE.Vec d) (γ : ℝ) (n : ℕ) :
    HasCompactSupport (coneCompactProbe α e γ n) :=
  ((coneAmbientBump d n).hasCompactSupport.comp_homeomorph
    (KineticPoint.homeomorphProd d)).mul_left

/-- Every compact probe is nonnegative and below the bounded transition. -/
theorem coneCompactProbe_bounds {d : ℕ} (α : ℝ) (e : PDE.Vec d) (γ : ℝ)
    (n : ℕ) (P : KineticPoint d) :
    0 ≤ coneCompactProbe α e γ n P ∧
      coneCompactProbe α e γ n P ≤ expNegInvGlue (coneCoordinate α e γ P) := by
  exact ⟨mul_nonneg (expNegInvGlue.nonneg _) (coneAmbientBump d n).nonneg,
    mul_le_of_le_one_right (expNegInvGlue.nonneg _) (coneAmbientBump d n).le_one⟩

/-- Nonpositive directional speed forces the actual exit measure onto its closed half-space. -/
theorem ballExitRaw_directional_cone
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)
    (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t})
    (α : ℝ) (e : PDE.Vec d) (γ : ℝ)
    (hP : coneCoordinate α e γ P.1 = 0)
    (hdir : ∀ w ∈ PDE.euclideanBall v₀ R, α + PDE.vecDot w e ≤ 0) :
    ∀ᵐ Q ∂ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P T,
      coneCoordinate α e γ Q ≤ 0 := by
  let μ := ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P T
  let χ := expNegInvGlue ∘ coneCoordinate α e γ
  have hχc := boundary_probe_continuous χ (coneProbe_smooth α e γ)
  have hi (n : ℕ) : (∫ Q, coneCompactProbe α e γ n Q ∂μ) = 0 := by
    have hspec := (ballExitRaw_spec hH hLE hd hlam hLam B hB v₀ hR P T).2.2
      _ (coneCompactProbe_smooth α e γ n) (coneCompactProbe_compact α e γ n)
    have hb := cone_boundarySolution_le_supersolution hH hLE hd hlam hLam B hB v₀ hR
      P.1.time T.1 T.2 (coneCompactProbe α e γ n) χ
      (coneCompactProbe_smooth α e γ n) (coneCompactProbe_compact α e γ n)
      (coneProbe_smooth α e γ) ⟨1, fun Q _ => by
        change |expNegInvGlue (coneCoordinate α e γ Q)| ≤ 1
        rw [abs_of_nonneg (expNegInvGlue.nonneg _)]
        exact (coneProbe_transition_bound _).2⟩
      (fun Q hQ => coneProbe_operator_nonpos B α e γ Q (hdir Q.velocity hQ.2.2))
      (fun Q _ => (coneCompactProbe_bounds α e γ n Q).2)
      P.1 ⟨le_rfl, T.2.le, subset_closure P.2⟩
    have hz : χ P.1 = 0 := by
      change expNegInvGlue (coneCoordinate α e γ P.1) = 0
      rw [hP, expNegInvGlue.zero]
    refine le_antisymm ?_ (integral_nonneg (fun Q => (coneCompactProbe_bounds α e γ n Q).1))
    exact hspec.trans_le (hz ▸ hb)
  have ht : Tendsto (fun n => ∫ Q, coneCompactProbe α e γ n Q ∂μ) atTop
      (𝓝 (∫ Q, χ Q ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    · intro n
      exact (boundary_probe_continuous _ (coneCompactProbe_smooth α e γ n)).measurable
        |>.aestronglyMeasurable
    · exact integrable_const _
    · intro n
      apply Eventually.of_forall
      intro Q
      rw [Real.norm_eq_abs, abs_of_nonneg (coneCompactProbe_bounds α e γ n Q).1]
      exact (coneCompactProbe_bounds α e γ n Q).2.trans (coneProbe_transition_bound _).2
    · exact Eventually.of_forall (fun Q => by
        simpa only [coneCompactProbe, χ, Function.comp_apply, mul_one] using
          (coneAmbientBump_tendsto d Q).const_mul
            (expNegInvGlue (coneCoordinate α e γ Q)))
  have hint : Integrable χ μ := Integrable.mono' (integrable_const (1 : ℝ))
    hχc.measurable.aestronglyMeasurable (Eventually.of_forall (fun Q => by
      change |expNegInvGlue (coneCoordinate α e γ Q)| ≤ 1
      rw [abs_of_nonneg (expNegInvGlue.nonneg _)]
      exact (coneProbe_transition_bound _).2))
  have hz : (∫ Q, χ Q ∂μ) = 0 := tendsto_nhds_unique ht
    (by simpa only [hi] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ))
      atTop (𝓝 0)))
  have hae := (integral_eq_zero_iff_of_nonneg (fun Q => expNegInvGlue.nonneg _) hint).mp hz
  filter_upwards [hae] with Q hQ
  by_contra hn
  exact (ne_of_gt (expNegInvGlue.pos_of_pos (not_le.mp hn))) hQ

end HypoellipticAleksandrov.KineticAleksandrov.LocalA

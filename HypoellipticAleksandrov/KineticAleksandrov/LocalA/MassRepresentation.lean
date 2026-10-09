module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ConeSupport
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.MassRepresentationRegularity
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.MassRepresentationApproximationBounds
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.MassRepresentationWeightedComparison

/-! # Representation of the exact bounded classical solution class by the actual exit measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Filter Parabolic SectionTwo
open scoped Topology

variable (hH : HormanderHypoellipticityStatement)
  (hLE : LiebermanEllipsoidDirichletStatement)
  {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ}
  (hlam : 0 < lam) (hLam : lam ≤ Lam)
  (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
  (v₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)

/-- The actual exit measure represents bounded physical C112 homogeneous solutions. -/
theorem ballExit_represents (P : LocalBallStart v₀ R) (T : {t : ℝ // P.1.time < t})
    (u : KineticPoint d → ℝ)
    (hUc : ContinuousOn u (localClosedStrip P.1.time T.1 v₀ R))
    (hUs : IsKineticC112On u (localStrip P.1.time T.1 v₀ R))
    (hUb : ∃ M : ℝ, ∀ Q ∈ localClosedStrip P.1.time T.1 v₀ R, |u Q| ≤ M)
    (hUe : ∀ Q ∈ localStrip P.1.time T.1 v₀ R,
      forwardKineticOperator (ofTimeVelocityCoefficient B) u Q = 0) :
    u P.1 = ∫ Q, u Q ∂ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P T := by
  let μ := ballExitRaw hH hLE hd hlam hLam B hB v₀ hR P T
  have hp : P.1 ∈ localClosedStrip P.1.time T.1 v₀ R :=
    ⟨le_rfl, T.2.le, subset_closure P.2⟩
  obtain ⟨M, hM⟩ := hUb
  have hMn : 0 ≤ M := (abs_nonneg (u P.1)).trans (hM P.1 hp)
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  let L (n : ℕ) : ℝ := (2 * M + 1) * ((n : ℝ) + 1) + 1 + (n : ℝ)
  have hn (n : ℕ) := mass_aperture_size M hMn n
  choose F hFb hFc using fun n => exists_mass_trace_probe P.1.time T.1 v₀ hR u hUc
    M hMn hM (L n) (ε n) (hn n).1
  let φ (n : ℕ) := boundaryProbePhysical (F n)
  let E (n : ℕ) := ballBoundarySolution hH hLE hd hlam hLam B hB v₀ hR P.1.time T.1 (φ n)
  have hφs (n : ℕ) := (boundaryProbePhysical_regular (F n)).1
  have hφc (n : ℕ) := (boundaryProbePhysical_regular (F n)).2.2
  have hEs (n : ℕ) := ballBoundarySolution_smooth_traces hH hLE hd hlam hLam B hB v₀ hR
    P.1.time T.1 T.2 (φ n) (hφs n) (hφc n)
  have hus := mass_classical_homogeneous_smooth hH B hB
    (isOpen_localStrip P.1.time T.1 v₀ R) u hUs hUe
  have hweight (n : ℕ) : ∀ Q ∈ localClosedStrip P.1.time T.1 v₀ R,
      |φ n Q - u Q| ≤ ε n * massGrowthBarrier Lam T.1 Q :=
    mass_trace_probe_weighted Lam P.1.time T.1 v₀ R u (φ n) M (L n) (ε n)
      (hn n).1.le hM (hFb n) (hFc n) (hn n).2.2.1 (hn n).2.2.2.2
  have hval (n : ℕ) : |E n P.1 - u P.1| ≤ ε n * massGrowthBarrier Lam T.1 P.1 := by
    have hm := mass_homogeneous_abs_weighted B hB P.1.time T.1 T.2 v₀ R
      u (E n) hus (hEs n).1 hUe (hEs n).2.1 hUc (hEs n).2.2.1
      ⟨M, hM⟩ (ballBoundarySolution_bounded hH hLE hd hlam hLam B hB v₀ hR
        P.1.time T.1 T.2 (φ n) (hφs n) (hφc n)) (ε n) (hn n).1.le
      (fun Q hQ => by
        dsimp only [E]
        rw [(hEs n).2.2.2 hQ, abs_sub_comm]
        exact hweight n Q (localTrace_subset_closed T.2.le v₀ R hQ)) P.1 hp
    simpa only [abs_sub_comm] using hm
  have he0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hvalLim : Tendsto (fun n => E n P.1) atTop (𝓝 (u P.1)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero_norm (fun n => by simpa only [Real.norm_eq_abs, abs_abs] using hval n)
      (by simpa only [mul_zero, zero_mul] using he0.mul_const (massGrowthBarrier Lam T.1 P.1))
  have hμ := ballExitRaw_ae_trace hH hLE hd hlam hLam B hB v₀ hR P T
  have hintLim : Tendsto (fun n => ∫ Q, φ n Q ∂μ) atTop (𝓝 (∫ Q, u Q ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => M + 1)
    · intro n
      exact (boundaryProbePhysical_regular (F n)).2.1.measurable.aestronglyMeasurable
    · exact integrable_const _
    · intro n
      apply Eventually.of_forall
      intro Q
      rw [Real.norm_eq_abs]
      exact (hFb n Q).trans (add_le_add_right (hn n).2.1 M)
    · filter_upwards [hμ] with Q hQ
      apply tendsto_iff_norm_sub_tendsto_zero.mpr
      apply squeeze_zero_norm' ?_ he0
      filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop ‖Q.position‖] with n hq
      simp only [Real.norm_eq_abs, abs_abs]
      exact hFc n Q (localTrace_subset_closed T.2.le v₀ R hQ)
        (hq.trans (hn n).2.2.2.1)
  have hid (n : ℕ) : (∫ Q, φ n Q ∂μ) = E n P.1 :=
    (ballExitRaw_spec hH hLE hd hlam hLam B hB v₀ hR P T).2.2 _ (hφs n) (hφc n)
  exact tendsto_nhds_unique hvalLim (hintLim.congr (fun n => hid n))

end HypoellipticAleksandrov.KineticAleksandrov.LocalA

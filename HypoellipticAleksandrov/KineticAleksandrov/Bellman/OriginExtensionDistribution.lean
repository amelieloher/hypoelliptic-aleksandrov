module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.OriginExtensionWeak

/-! # The singular Bellman inequality on the whole plane -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set MeasureTheory

/-- The singular right-hand side is locally integrable at the kinetic origin. -/
theorem bellmanGauge_source_locallyIntegrable {alpha : ℝ}
    (ha : 0 < alpha) (ha1 : alpha < 1) :
    LocallyIntegrable (fun q : ℝ × ℝ => bellmanGauge q ^ (alpha - 2)) volume := by
  apply bellman_gauge_bound_locallyIntegrable (alpha - 2) (by linarith) (by linarith)
    _ (bellmanGauge_continuous.continuousOn.rpow_const
      (fun q hq => Or.inl (bellmanGauge_pos q hq).ne')) 1 zero_le_one
  intro q _
  rw [abs_of_nonneg (Real.rpow_nonneg (bellmanGauge_nonneg _) _), one_mul]

/-- Multiplication of a test by velocity has the expected position derivative. -/
theorem bellmanDx_velocity_mul {test : (ℝ × ℝ) → ℝ}
    (ht : Differentiable ℝ test) (q : ℝ × ℝ) :
    bellmanDx (fun z => z.2 * test z) q = q.2 * bellmanDx test q := by
  unfold bellmanDx
  rw [show (fun z : ℝ × ℝ => z.2 * test z) = Prod.snd * test from rfl,
    fderiv_mul differentiableAt_snd (ht q), fderiv_snd]
  simp

/-- Integrating the actual punctured inequality produces the defect-free distributional bound. -/
theorem IsBellmanHomogeneous.origin_distributional_bound {alpha : ℝ}
    {phi : (ℝ × ℝ) → ℝ} (h : IsBellmanHomogeneous alpha phi)
    (ha : 0 < alpha) (ha1 : alpha < 1) (c b : ℝ)
    (hb : ∀ q ∈ bellmanPuncturedSet,
      c * bellmanGauge q ^ (alpha - 2) ≤ bellmanOperator b phi q)
    (test : (ℝ × ℝ) → ℝ) (ht : ContDiff ℝ 2 test) (hs : HasCompactSupport test)
    (hn : ∀ q, 0 ≤ test q) :
    c * (∫ q, bellmanGauge q ^ (alpha - 2) * test q) ≤
      -(∫ q, bellmanOriginExtension phi q * q.2 * bellmanDx test q) +
        b * (∫ q, bellmanOriginExtension phi q * bellmanDvv test q) := by
  obtain ⟨hX, _, hvv⟩ := h.origin_jets_locallyIntegrable ha ha1
  have htestv : ContDiff ℝ 2 (fun q : ℝ × ℝ => q.2 * test q) := contDiff_snd.mul ht
  have hsupportv : HasCompactSupport (fun q : ℝ × ℝ => q.2 * test q) := hs.mul_left
  have hIX := hX.integrable_smul_right_of_hasCompactSupport htestv.continuous hsupportv
  have hIvv := hvv.integrable_smul_right_of_hasCompactSupport ht.continuous hs
  have hIρ := (bellmanGauge_source_locallyIntegrable ha ha1)
    |>.integrable_smul_right_of_hasCompactSupport ht.continuous hs
  simp only [smul_eq_mul] at hIX hIvv hIρ
  have hIleft : Integrable (fun q => (c * bellmanGauge q ^ (alpha - 2)) * test q) volume := by
    simpa only [smul_eq_mul, mul_assoc] using hIρ.const_mul c
  have hIright : Integrable (fun q => bellmanOperator b phi q * test q) volume := by
    apply (hIX.add (hIvv.const_mul b)).congr
    filter_upwards [] with q
    change bellmanDx phi q * (q.2 * test q) + b * (bellmanDvv phi q * test q) = _
    unfold bellmanOperator
    ring
  have hi := integral_mono_ae hIleft hIright (by
    filter_upwards [bellman_coordinates_ne_zero_ae] with q hq
    exact mul_le_mul_of_nonneg_right
      (hb q (fun he => hq.1 (congrArg Prod.fst he))) (hn q))
  have hx := (h.origin_weak_jets ha ha1 _ htestv hsupportv).1
  have hvvweak := (h.origin_weak_jets ha ha1 test ht hs).2.2
  have hx' : (∫ q, bellmanOriginExtension phi q * q.2 * bellmanDx test q) =
      -(∫ q, bellmanDx phi q * (q.2 * test q)) := by
    convert hx using 1
    apply integral_congr_ae
    filter_upwards [] with q
    rw [bellmanDx_velocity_mul (ht.differentiable (by norm_num))]
    ring
  have hir : (∫ q, bellmanOperator b phi q * test q) =
      (∫ q, bellmanDx phi q * (q.2 * test q)) +
        b * (∫ q, bellmanDvv phi q * test q) := by
    convert integral_add hIX (hIvv.const_mul b) using 1
    · apply integral_congr_ae
      filter_upwards [] with q
      unfold bellmanOperator
      ring
    · rw [integral_const_mul]
  have hil : (∫ q, (c * bellmanGauge q ^ (alpha - 2)) * test q) =
      c * (∫ q, bellmanGauge q ^ (alpha - 2) * test q) := by
    simpa only [mul_assoc] using
      (integral_const_mul c (fun q : ℝ × ℝ => bellmanGauge q ^ (alpha - 2) * test q))
  rw [hil, hir, ← hvvweak] at hi
  rw [hx', neg_neg]
  exact hi

end HypoellipticAleksandrov.KineticAleksandrov

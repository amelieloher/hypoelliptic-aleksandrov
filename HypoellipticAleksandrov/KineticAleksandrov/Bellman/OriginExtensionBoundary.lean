module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.OriginExtensionFaces

/-! # Explicit vanishing of the three kinetic inner boundary errors -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set MeasureTheory Filter
open scoped Topology

/-- A compact continuous test has a global absolute bound. -/
theorem bellman_compact_test_bound (test : (ℝ × ℝ) → ℝ)
    (ht : Continuous test) (hs : HasCompactSupport test) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ q, |test q| ≤ M := by
  obtain ⟨M, hM⟩ := hs.exists_bound_of_continuousOn ht.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun q => ?_⟩
  by_cases hq : q ∈ tsupport test
  · exact (hM q hq).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hq, abs_zero]
    exact le_max_right _ _

/-- A face degree with positive degree plus surface weight has zero inner-radius limit. -/
theorem bellmanOriginFaceError_tendsto (beta : ℝ) (f : (ℝ × ℝ) → ℝ)
    (hc : ContinuousOn f bellmanPuncturedSet)
    (hscale : ∀ r : ℝ, 0 < r → ∀ q ∈ bellmanPuncturedSet,
      f (bellmanPlaneDilation r q) = r ^ beta * f q)
    (test : (ℝ × ℝ) → ℝ) (ht : Continuous test) (hs : HasCompactSupport test)
    (k : ℕ) (hdegree : 0 < beta + k) (i : Fin 4) :
    Tendsto (fun delta => bellmanOriginFaceError k delta i f test) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC, hCb⟩ := bellmanOriginFace_bound f hc
  obtain ⟨M, hM, hMb⟩ := bellman_compact_test_bound test ht hs
  have hpow : Tendsto (fun delta : ℝ => 2 * C * M * delta ^ (beta + k))
      (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun delta : ℝ => 2 * C * M * delta ^ (beta + k)) :=
      continuous_const.mul (Real.continuous_rpow_const hdegree.le)
    have hh := hc.continuousAt (x := (0 : ℝ))
    have hh' : Tendsto (fun delta : ℝ => 2 * C * M * delta ^ (beta + k))
        (𝓝[>] 0) (𝓝 (2 * C * M * (0 : ℝ) ^ (beta + k))) :=
      hh.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [Real.zero_rpow hdegree.ne', mul_zero] using hh'
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hpow
  filter_upwards [self_mem_nhdsWithin] with delta hd
  rw [Real.norm_eq_abs]
  exact bellmanOriginFaceError_bound beta f hscale C hC hCb test M hM hMb k delta hd i

/-- The source rates are α+1, α+3, α+2, with a common face constant independent of radius. -/
theorem IsBellmanHomogeneous.origin_boundary_rates {alpha : ℝ} {phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha phi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ test : (ℝ × ℝ) → ℝ, ∀ M : ℝ,
      0 ≤ M → (∀ q, |test q| ≤ M) → ∀ delta : ℝ, 0 < delta → ∀ i : Fin 4,
      |bellmanOriginFaceError 1 delta i phi test| ≤ C * M * delta ^ (alpha + 1) ∧
      |bellmanOriginFaceError 3 delta i phi test| ≤ C * M * delta ^ (alpha + 3) ∧
      |bellmanOriginFaceError 3 delta i (bellmanDv phi) test| ≤
        C * M * delta ^ (alpha + 2) := by
  obtain ⟨C0, hC0, hb0⟩ := bellmanOriginFace_bound phi h.1.continuousOn
  obtain ⟨C1, hC1, hb1⟩ := bellmanOriginFace_bound (bellmanDv phi)
    (h.directional_contDiffOn (0, 1)).continuousOn
  let C := max C0 C1
  have hC : 0 ≤ C := hC0.trans (le_max_left _ _)
  have hb0' i w hw : |phi (bellmanOriginFace i w)| ≤ C :=
    (hb0 i w hw).trans (le_max_left _ _)
  have hb1' i w hw : |bellmanDv phi (bellmanOriginFace i w)| ≤ C :=
    (hb1 i w hw).trans (le_max_right _ _)
  refine ⟨2 * C, mul_nonneg (by norm_num) hC, fun test M hM hMb delta hd i => ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Nat.cast_one] using
      bellmanOriginFaceError_bound alpha phi h.2 C hC hb0' test M hM hMb 1 delta hd i
  · exact bellmanOriginFaceError_bound alpha phi h.2 C hC hb0' test M hM hMb 3 delta hd i
  · have hh := bellmanOriginFaceError_bound (alpha - 1) (bellmanDv phi)
      (fun _ hr _ hq => h.dv_scaling hr hq) C hC hb1' test M hM hMb 3 delta hd i
    convert hh using 1
    congr 2
    norm_num
    ring

/-- All actual face errors vanish, with the position surface order δ and velocity order δ³. -/
theorem IsBellmanHomogeneous.origin_boundary_vanish {alpha : ℝ} {phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha phi) (ha : 0 < alpha)
    (test : (ℝ × ℝ) → ℝ) (ht : Continuous test) (hs : HasCompactSupport test)
    (i : Fin 4) :
    Tendsto (fun delta => bellmanOriginFaceError 1 delta i phi test) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun delta => bellmanOriginFaceError 3 delta i phi test) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun delta => bellmanOriginFaceError 3 delta i (bellmanDv phi) test)
      (𝓝[>] 0) (𝓝 0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact bellmanOriginFaceError_tendsto alpha phi h.1.continuousOn h.2 test ht hs
      1 (by norm_num; linarith) i
  · exact bellmanOriginFaceError_tendsto alpha phi h.1.continuousOn h.2 test ht hs
      3 (by norm_num; linarith) i
  · exact bellmanOriginFaceError_tendsto (alpha - 1) (bellmanDv phi)
      (h.directional_contDiffOn (0, 1)).continuousOn
      (fun _ hr _ hq => h.dv_scaling hr hq) test ht hs 3 (by norm_num; linarith) i

end HypoellipticAleksandrov.KineticAleksandrov

module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.OriginExtensionSlices
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.OriginExtensionContinuous

/-! # Actual whole-plane weak Bellman jets with no origin defect -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set MeasureTheory

/-- The zero extension and the original total function differ only at one null point. -/
theorem bellmanOriginExtension_ae (phi : (ℝ × ℝ) → ℝ) :
    bellmanOriginExtension phi =ᵐ[volume] phi := by
  filter_upwards [bellman_coordinates_ne_zero_ae] with q hq
  exact bellmanOriginExtension_eqOn phi (fun he => hq.1 (congrArg Prod.fst he))

/-- The original total function is locally integrable regardless of its origin value. -/
theorem IsBellmanHomogeneous.origin_locallyIntegrable {alpha : ℝ}
    {phi : (ℝ × ℝ) → ℝ} (h : IsBellmanHomogeneous alpha phi) (ha : 0 < alpha) :
    LocallyIntegrable phi volume :=
  (h.origin_extension_continuous ha).locallyIntegrable.congr (bellmanOriginExtension_ae phi)

/-- A locally integrable punctured C¹ function has its literal weak position derivative. -/
theorem bellman_weak_dx (f : (ℝ × ℝ) → ℝ)
    (hC : ContDiffOn ℝ 1 f bellmanPuncturedSet)
    (hL : LocallyIntegrable f volume) (hD : LocallyIntegrable (bellmanDx f) volume)
    (test : (ℝ × ℝ) → ℝ) (ht : ContDiff ℝ 1 test) (hs : HasCompactSupport test) :
    (∫ q, f q * bellmanDx test q) = -(∫ q, bellmanDx f q * test q) := by
  have htD : Continuous (bellmanDx test) :=
    (ht.continuous_fderiv (by norm_num)).clm_apply continuous_const
  apply bellman_integral_slices_first f (bellmanDx f) test (bellmanDx test)
    (hL.integrable_smul_right_of_hasCompactSupport htD (hs.fderiv_apply ℝ (1, 0)))
    (hD.integrable_smul_right_of_hasCompactSupport ht.continuous hs)
    (hL.integrable_smul_right_of_hasCompactSupport ht.continuous hs)
  · intro v hv X
    have hq : (X, v) ∈ bellmanPuncturedSet := fun he => hv (congrArg Prod.snd he)
    exact bellman_hasDerivAt_first ((hC.contDiffAt
      (bellmanPuncturedSet_isOpen.mem_nhds hq)).differentiableAt (by norm_num))
  · intro X v
    exact bellman_hasDerivAt_first (ht.differentiable (by norm_num) _)

/-- A locally integrable punctured C¹ function has its literal weak velocity derivative. -/
theorem bellman_weak_dv (f : (ℝ × ℝ) → ℝ)
    (hC : ContDiffOn ℝ 1 f bellmanPuncturedSet)
    (hL : LocallyIntegrable f volume) (hD : LocallyIntegrable (bellmanDv f) volume)
    (test : (ℝ × ℝ) → ℝ) (ht : ContDiff ℝ 1 test) (hs : HasCompactSupport test) :
    (∫ q, f q * bellmanDv test q) = -(∫ q, bellmanDv f q * test q) := by
  have htD : Continuous (bellmanDv test) :=
    (ht.continuous_fderiv (by norm_num)).clm_apply continuous_const
  apply bellman_integral_slices_second f (bellmanDv f) test (bellmanDv test)
    (hL.integrable_smul_right_of_hasCompactSupport htD (hs.fderiv_apply ℝ (0, 1)))
    (hD.integrable_smul_right_of_hasCompactSupport ht.continuous hs)
    (hL.integrable_smul_right_of_hasCompactSupport ht.continuous hs)
  · intro X hX v
    have hq : (X, v) ∈ bellmanPuncturedSet := fun he => hX (congrArg Prod.fst he)
    exact bellman_hasDerivAt_second ((hC.contDiffAt
      (bellmanPuncturedSet_isOpen.mem_nhds hq)).differentiableAt (by norm_num))
  · intro X v
    exact bellman_hasDerivAt_second (ht.differentiable (by norm_num) _)

/-- The extended homogeneous function has all three weak jets on the whole plane. -/
theorem IsBellmanHomogeneous.origin_weak_jets {alpha : ℝ} {phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha phi) (ha : 0 < alpha) (ha1 : alpha < 1)
    (test : (ℝ × ℝ) → ℝ) (ht : ContDiff ℝ 2 test) (hs : HasCompactSupport test) :
    (∫ q, bellmanOriginExtension phi q * bellmanDx test q) =
      -(∫ q, bellmanDx phi q * test q) ∧
    (∫ q, bellmanOriginExtension phi q * bellmanDv test q) =
      -(∫ q, bellmanDv phi q * test q) ∧
    (∫ q, bellmanOriginExtension phi q * bellmanDvv test q) =
      (∫ q, bellmanDvv phi q * test q) := by
  obtain ⟨hX, hv, hvv⟩ := h.origin_jets_locallyIntegrable ha ha1
  have hL := h.origin_locallyIntegrable ha
  have he (g : (ℝ × ℝ) → ℝ) :
      (∫ q, bellmanOriginExtension phi q * g q) = (∫ q, phi q * g q) := by
    apply integral_congr_ae
    filter_upwards [bellmanOriginExtension_ae phi] with q hq
    rw [hq]
  have ht1 : ContDiff ℝ 1 test := ht.of_le (by norm_num)
  have h1 : ContDiffOn ℝ 1 phi bellmanPuncturedSet := h.1.of_le (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · rw [he]
    exact bellman_weak_dx phi h1 hL hX test ht1 hs
  · rw [he]
    exact bellman_weak_dv phi h1 hL hv test ht1 hs
  · rw [he]
    have htDv : ContDiff ℝ 1 (bellmanDv test) :=
      (ht.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply contDiff_const
    have hfirst := bellman_weak_dv phi h1 hL hv (bellmanDv test) htDv
      (hs.fderiv_apply ℝ (0, 1))
    have hsecond := bellman_weak_dv (bellmanDv phi) (h.directional_contDiffOn (0, 1))
      hv hvv test ht1 hs
    change (∫ q, phi q * bellmanDvv test q) = -(∫ q, bellmanDv phi q * bellmanDv test q)
      at hfirst
    change (∫ q, bellmanDv phi q * bellmanDv test q) =
      -(∫ q, bellmanDvv phi q * test q) at hsecond
    rw [hfirst, hsecond, neg_neg]

end HypoellipticAleksandrov.KineticAleksandrov

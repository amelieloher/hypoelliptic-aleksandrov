module

public import HypoellipticAleksandrov.Parabolic.WeakPrincipalCoercivityCore

/-!
# Weak principal coercivity

This conditions module assembles the reusable plateau, integrability, and raw
localized-limit results from `WeakPrincipalCoercivityCore` into the final weak
principal-coercivity theorem.
-/

@[expose] public section

noncomputable section

open Function MeasureTheory Set Topology
open scoped ENNReal BigOperators MatrixOrder

namespace HypoellipticAleksandrov.Parabolic

/-- Spacetime principal coercivity for a rough selected spatial weak jet,
obtained from one common localized scalar mollification. -/
theorem weakPrincipalIntegrationByParts_coercive
    {d : ℕ} (lam Lam M K : ℝ)
    (s₀ s₁ : ℝ)
    (O : Set (PDE.Vec d)) (hO : IsOpen O)
    (A : TimeVelocity d → PDE.Mat d)
    (q : TimeVelocity d → ℝ)
    (QG : TimeVelocity d → PDE.Vec d)
    (QH : TimeVelocity d → PDE.Mat d)
    (hAmeas : AEStronglyMeasurable A
      (timeVelocityVolumeOn (Set.Ioo s₀ s₁ ×ˢ O)))
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hA : ∀ r ∈ Set.Ioo s₀ s₁, ∀ i j : Fin d,
      ContDiffOn ℝ 1 (fun y => A (r, y) i j) O)
    (hAlower : ∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O,
      lam • (1 : PDE.Mat d) ≤ A z)
    (hAupper : ∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O,
      A z ≤ Lam • (1 : PDE.Mat d))
    (hAderiv : ∀ z ∈ Set.Ioo s₀ s₁ ×ˢ O,
      ∀ i j k : Fin d,
        |spatialPartial k (fun y => A (z.1, y) i j) z.2| ≤ M)
    (hq_memLp : ParabolicMemLpOn
      (Set.Ioo s₀ s₁ ×ˢ O) 2 q)
    (hQG_memLp : ∀ j : Fin d, ParabolicMemLpOn
      (Set.Ioo s₀ s₁ ×ˢ O) 2 (fun z => QG z j))
    (hQH_memLp : ∀ j i : Fin d, ParabolicMemLpOn
      (Set.Ioo s₀ s₁ ×ˢ O) 2 (fun z => QH z j i))
    (hq_velocity : ∀ j : Fin d,
      HasWeakVelocityPartialDerivOn
        (Set.Ioo s₀ s₁ ×ˢ O) j q (fun z => QG z j))
    (hQG_velocity : ∀ j i : Fin d,
      HasWeakVelocityPartialDerivOn
        (Set.Ioo s₀ s₁ ×ˢ O) i
        (fun z => QG z j) (fun z => QH z j i))
    (η : PDE.Vec d → ℝ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηcompact : HasCompactSupport η)
    (hηsupport : tsupport η ⊆ O)
    (hηnonneg : ∀ y, 0 ≤ η y)
    (hηle : ∀ y, η y ≤ 1)
    (hηderiv : ∀ y ∈ O, ∀ i : Fin d,
      |spatialPartial i η y| ≤ K)
    (ζ : ℝ → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζcompact : HasCompactSupport ζ)
    (hζsupport : tsupport ζ ⊆ Set.Ioo s₀ s₁)
    (hζnonneg : ∀ r, 0 ≤ ζ r) :
    IntegrableOn
        (fun z =>
          ζ z.1 *
            (∑ i : Fin d, ∑ j : Fin d,
              A z i j * QH z j i) *
            WeakGradientTimeEnergy.localizedGradientDivergence η QG QH z)
        (Set.Ioo s₀ s₁ ×ˢ O) volume ∧
      IntegrableOn
        (fun z =>
          ζ z.1 * η z.2 ^ 2 *
            ∑ k : Fin d, ∑ i : Fin d, QH z k i ^ 2)
        (Set.Ioo s₀ s₁ ×ˢ O) volume ∧
      IntegrableOn
        (fun z =>
          ζ z.1 *
            (tsupport η).indicator
              (fun y => ∑ k : Fin d, QG (z.1, y) k ^ 2) z.2)
        (Set.Ioo s₀ s₁ ×ˢ O) volume ∧
      -(∫ z in Set.Ioo s₀ s₁ ×ˢ O,
          ζ z.1 *
            (∑ i : Fin d, ∑ j : Fin d,
              A z i j * QH z j i) *
            WeakGradientTimeEnergy.localizedGradientDivergence η QG QH z
          ∂volume) ≥
        lam / 2 *
          (∫ z in Set.Ioo s₀ s₁ ×ˢ O,
            ζ z.1 * η z.2 ^ 2 *
              ∑ k : Fin d, ∑ i : Fin d, QH z k i ^ 2
            ∂volume) -
        principalCoercivityConstant d lam Lam M K *
          (∫ z in Set.Ioo s₀ s₁ ×ˢ O,
            ζ z.1 *
              (tsupport η).indicator
                (fun y => ∑ k : Fin d, QG (z.1, y) k ^ 2) z.2
            ∂volume) := by
  obtain ⟨δ, hδ, b, hb, hbCompact, hbSub, _hbOne, _hqEq, hQGEq, hQHEq⟩ :=
    WeakPrincipalCoercivityCore.exists_localized_spatial_jet_plateau
      s₀ s₁ O hO q QG QH η hηcompact hηsupport ζ hζcompact hζsupport
  let rG : TimeVelocity d → PDE.Vec d := fun z j =>
    b z * QG z j + q z * velocityGradient b z j
  let rH : TimeVelocity d → PDE.Mat d := fun z j i =>
    b z * QH z j i + velocityGradient b z i * QG z j +
      velocityGradient b z j * QG z i + q z * velocityHessian b z j i
  have hrGEq : ∀ j : Fin d, Set.EqOn (fun z => rG z j) (fun z => QG z j)
      (Metric.thickening δ (tsupport ζ ×ˢ tsupport η)) := by
    intro j z hz
    simpa only [rG, localizedGradient] using hQGEq j hz
  have hrHEq : ∀ j i : Fin d, Set.EqOn (fun z => rH z j i) (fun z => QH z j i)
      (Metric.thickening δ (tsupport ζ ×ˢ tsupport η)) := by
    intro j i z hz
    simpa only [rH, localizedHessian] using hQHEq j i hz
  have hsupport_mem (z : TimeVelocity d)
      (ht : z.1 ∈ tsupport ζ) (hv : z.2 ∈ tsupport η) :
      z ∈ Metric.thickening δ (tsupport ζ ×ˢ tsupport η) :=
    Metric.self_subset_thickening hδ _ ⟨ht, hv⟩
  have hprincipal : ∀ z,
      ζ z.1 *
          (∑ i : Fin d, ∑ j : Fin d,
            A z i j * rH z j i) *
          WeakGradientTimeEnergy.localizedGradientDivergence η
            rG rH z =
        ζ z.1 *
          (∑ i : Fin d, ∑ j : Fin d, A z i j * QH z j i) *
          WeakGradientTimeEnergy.localizedGradientDivergence η QG QH z := by
    intro z
    by_cases ht : z.1 ∈ tsupport ζ
    · by_cases hv : z.2 ∈ tsupport η
      · have hz := hsupport_mem z ht hv
        rw [show (∑ i : Fin d, ∑ j : Fin d,
            A z i j * rH z j i) =
            ∑ i : Fin d, ∑ j : Fin d, A z i j * QH z j i by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          have hij := hrHEq j i hz
          change rH z j i = QH z j i at hij
          rw [hij]]
        unfold WeakGradientTimeEnergy.localizedGradientDivergence
        congr 2
        apply Finset.sum_congr rfl
        intro k hk
        have hgk := hrGEq k hz
        have hhk := hrHEq k k hz
        change rG z k = QG z k at hgk
        change rH z k k = QH z k k at hhk
        rw [hgk, hhk]
      · have hzero : η z.2 = 0 := image_eq_zero_of_notMem_tsupport hv
        simp [WeakGradientTimeEnergy.localizedGradientDivergence, hzero]
    · have hzero : ζ z.1 = 0 := image_eq_zero_of_notMem_tsupport ht
      simp [hzero]
  have henergy : ∀ z,
      ζ z.1 * η z.2 ^ 2 *
          ∑ k : Fin d, ∑ i : Fin d, rH z k i ^ 2 =
        ζ z.1 * η z.2 ^ 2 *
          ∑ k : Fin d, ∑ i : Fin d, QH z k i ^ 2 := by
    intro z
    by_cases ht : z.1 ∈ tsupport ζ
    · by_cases hv : z.2 ∈ tsupport η
      · have hz := hsupport_mem z ht hv
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro i hi
        have hki := hrHEq k i hz
        change rH z k i = QH z k i at hki
        rw [hki]
      · have hzero : η z.2 = 0 := image_eq_zero_of_notMem_tsupport hv
        simp [hzero]
    · have hzero : ζ z.1 = 0 := image_eq_zero_of_notMem_tsupport ht
      simp [hzero]
  have hgradient : ∀ z : TimeVelocity d,
      ζ z.1 * (tsupport η).indicator
          (fun y => ∑ k : Fin d, rG (z.1, y) k ^ 2) z.2 =
        ζ z.1 * (tsupport η).indicator
          (fun y => ∑ k : Fin d, QG (z.1, y) k ^ 2) z.2 := by
    intro z
    by_cases ht : z.1 ∈ tsupport ζ
    · by_cases hv : z.2 ∈ tsupport η
      · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv]
        apply congrArg (fun x : ℝ => ζ z.1 * x)
        apply Finset.sum_congr rfl
        intro k hk
        have hkEq := hrGEq k (hsupport_mem z ht hv)
        change rG z k = QG z k at hkEq
        rw [hkEq]
      · simp [Set.indicator_of_notMem hv]
    · have hzero : ζ z.1 = 0 := image_eq_zero_of_notMem_tsupport ht
      simp [hzero]
  have htargets := WeakPrincipalCoercivityCore.targets_integrableOn
    s₀ s₁ O hO lam Lam A QG QH hAmeas hlam hAlower hAupper hQG_memLp hQH_memLp
      η hη hηcompact ζ hζ hζcompact
  refine ⟨htargets.1, htargets.2.1, htargets.2.2, ?_⟩
  have hlocal := WeakPrincipalCoercivityCore.localized_limit
    lam Lam M K s₀ s₁ O hO A q QG QH hAmeas hlam hlamLam hA hAlower hAupper
      hAderiv hq_memLp hQG_memLp hQH_memLp hq_velocity hQG_velocity
      b hb hbCompact hbSub η hη hηcompact hηsupport hηnonneg hηle hηderiv
      ζ hζ hζcompact hζnonneg
  change -(∫ z in Set.Ioo s₀ s₁ ×ˢ O, ζ z.1 *
      (∑ i : Fin d, ∑ j : Fin d, A z i j * rH z j i) *
      WeakGradientTimeEnergy.localizedGradientDivergence η rG rH z ∂volume) ≥
    lam / 2 * (∫ z in Set.Ioo s₀ s₁ ×ˢ O, ζ z.1 * η z.2 ^ 2 *
      ∑ k : Fin d, ∑ i : Fin d, rH z k i ^ 2 ∂volume) -
    principalCoercivityConstant d lam Lam M K *
      (∫ z in Set.Ioo s₀ s₁ ×ˢ O, ζ z.1 * (tsupport η).indicator
        (fun y => ∑ k : Fin d, rG (z.1, y) k ^ 2) z.2 ∂volume) at hlocal
  rw [show (∫ z in Set.Ioo s₀ s₁ ×ˢ O,
      ζ z.1 *
        (∑ i : Fin d, ∑ j : Fin d,
          A z i j * rH z j i) *
        WeakGradientTimeEnergy.localizedGradientDivergence η
          rG rH z ∂volume) =
      ∫ z in Set.Ioo s₀ s₁ ×ˢ O,
        ζ z.1 * (∑ i : Fin d, ∑ j : Fin d, A z i j * QH z j i) *
          WeakGradientTimeEnergy.localizedGradientDivergence η QG QH z
        ∂volume by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall hprincipal] at hlocal
  rw [show (∫ z in Set.Ioo s₀ s₁ ×ˢ O,
      ζ z.1 * η z.2 ^ 2 *
        ∑ k : Fin d, ∑ i : Fin d, rH z k i ^ 2 ∂volume) =
      ∫ z in Set.Ioo s₀ s₁ ×ˢ O,
        ζ z.1 * η z.2 ^ 2 * ∑ k : Fin d, ∑ i : Fin d, QH z k i ^ 2
        ∂volume by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall henergy] at hlocal
  rw [show (∫ z in Set.Ioo s₀ s₁ ×ˢ O,
      ζ z.1 * (tsupport η).indicator
        (fun y => ∑ k : Fin d, rG (z.1, y) k ^ 2) z.2
      ∂volume) =
      ∫ z in Set.Ioo s₀ s₁ ×ˢ O,
        ζ z.1 * (tsupport η).indicator
          (fun y => ∑ k : Fin d, QG (z.1, y) k ^ 2) z.2
        ∂volume by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall hgradient] at hlocal
  exact hlocal

end HypoellipticAleksandrov.Parabolic

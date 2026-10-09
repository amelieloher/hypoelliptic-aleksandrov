module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.OriginExtensionDistribution
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.OriginExtensionBoundary

/-! # B9: the whole-plane distributional extension of an actual homogeneous barrier -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set MeasureTheory

/-- The general B9 conditions: actual C² homogeneity and the punctured barrier inequality
supply the continuous extension, locally integrable jets and defect-free weak inequality. -/
theorem bellman_barrier_distributional_extension
    (lam Lam alpha c : ℝ) (_hlam : 0 < lam) (_hLam : lam ≤ Lam)
    (ha : 0 < alpha) (ha1 : alpha < 1) (phi : (ℝ × ℝ) → ℝ)
    (hhom : IsBellmanHomogeneous alpha phi)
    (hbound : ∀ q ∈ bellmanPuncturedSet, ∀ b ∈ Icc lam Lam,
      c * bellmanGauge q ^ (alpha - 2) ≤ bellmanOperator b phi q) :
    ∃ psi : (ℝ × ℝ) → ℝ, Continuous psi ∧ psi (0, 0) = 0 ∧
      EqOn psi phi bellmanPuncturedSet ∧
      LocallyIntegrable psi volume ∧ LocallyIntegrable (bellmanDx phi) volume ∧
      LocallyIntegrable (bellmanDv phi) volume ∧ LocallyIntegrable (bellmanDvv phi) volume ∧
      (∀ test : (ℝ × ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) test → HasCompactSupport test →
        (∫ q, psi q * bellmanDx test q) = -(∫ q, bellmanDx phi q * test q)) ∧
      (∀ test : (ℝ × ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) test → HasCompactSupport test →
        (∫ q, psi q * bellmanDv test q) = -(∫ q, bellmanDv phi q * test q)) ∧
      (∀ test : (ℝ × ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) test → HasCompactSupport test →
        (∫ q, psi q * bellmanDvv test q) = (∫ q, bellmanDvv phi q * test q)) ∧
      ∀ b ∈ Icc lam Lam, ∀ test : (ℝ × ℝ) → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) test → HasCompactSupport test → (∀ q, 0 ≤ test q) →
        c * (∫ q, bellmanGauge q ^ (alpha - 2) * test q) ≤
          -(∫ q, psi q * q.2 * bellmanDx test q) +
            b * (∫ q, psi q * bellmanDvv test q) := by
  obtain ⟨hX, hv, hvv⟩ := hhom.origin_jets_locallyIntegrable ha ha1
  refine ⟨bellmanOriginExtension phi, hhom.origin_extension_continuous ha,
    bellmanOriginExtension_zero phi, bellmanOriginExtension_eqOn phi,
    (hhom.origin_extension_continuous ha).locallyIntegrable, hX, hv, hvv, ?_, ?_, ?_, ?_⟩
  · intro test ht hs
    exact (hhom.origin_weak_jets ha ha1 test (ht.of_le (by norm_cast)) hs).1
  · intro test ht hs
    exact (hhom.origin_weak_jets ha ha1 test (ht.of_le (by norm_cast)) hs).2.1
  · intro test ht hs
    exact (hhom.origin_weak_jets ha ha1 test (ht.of_le (by norm_cast)) hs).2.2
  · intro b hb test ht hs hn
    exact hhom.origin_distributional_bound ha ha1 c b (fun q hq => hbound q hq b hb)
      test (ht.of_le (by norm_cast)) hs hn

end HypoellipticAleksandrov.KineticAleksandrov

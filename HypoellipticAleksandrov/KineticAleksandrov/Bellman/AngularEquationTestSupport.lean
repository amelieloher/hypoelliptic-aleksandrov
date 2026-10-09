module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularEquationTest
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic

/-! # Compact support of the zero-extended source angular tests -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set

/-- A compact positive radial support times a compact angular support stays away from the
origin. -/
theorem bellmanAngularTest_support_data (ζ φ : ℝ → ℝ)
    (hcζ : HasCompactSupport ζ) (hcφ : HasCompactSupport φ)
    (hs : tsupport ζ ⊆ Ioi (0 : ℝ)) :
    HasCompactSupport (bellmanAngularTest ζ φ) ∧
      tsupport (bellmanAngularTest ζ φ) ⊆ {q : ℝ × ℝ | 0 < q.1} := by
  let K : Set (BellmanPositiveTime × ℝ) :=
    (Subtype.val ⁻¹' tsupport ζ) ×ˢ tsupport φ
  let P : BellmanPositiveTime × ℝ → ℝ × ℝ := fun w => (bellmanAngularPoint w).val
  have hk : IsCompact K := by
    apply IsCompact.prod _ hcφ
    apply Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hcζ
    intro s hsζ
    exact ⟨⟨s, hs hsζ⟩, rfl⟩
  have hP : Continuous P := continuous_subtype_val.comp continuous_bellmanAngularPoint
  have hPK : IsCompact (P '' K) := hk.image hP
  have hin : Function.support (bellmanAngularTest ζ φ) ⊆ P '' K := by
    intro q hq
    have hx : 0 < q.1 := by
      by_contra hn
      exact hq (ite_eq_right hn)
    let w := bellmanAngularHomeomorph.symm ⟨q, hx⟩
    have he : P w = q := bellmanAngularPoint_inverse q hx
    have hm : ζ (bellmanTestRadius q) * φ (bellmanTestAngle q) ≠ 0 := by
      change bellmanAngularTest ζ φ q ≠ 0 at hq
      simpa only [bellmanAngularTest, ite_eq_left hx, bellmanSeparatedExpression] using hq
    refine ⟨w, ?_, he⟩
    constructor
    · change w.1.val ∈ tsupport ζ
      have hr : bellmanTestRadius q = w.1.val := by
        rw [← he]
        exact bellmanTestRadius_angularPoint w
      rw [← hr]
      exact subset_tsupport ζ ((mul_ne_zero_iff.mp hm).1)
    · change w.2 ∈ tsupport φ
      have ha : bellmanTestAngle q = w.2 := by
        rw [← he]
        exact bellmanTestAngle_angularPoint w
      rw [← ha]
      exact subset_tsupport φ ((mul_ne_zero_iff.mp hm).2)
  have hts : tsupport (bellmanAngularTest ζ φ) ⊆ P '' K :=
    closure_minimal hin hPK.isClosed
  refine ⟨hPK.of_isClosed_subset (isClosed_tsupport _) hts, hts.trans ?_⟩
  rintro q ⟨w, _, rfl⟩
  exact pow_pos w.1.property 3

/-- Compact angular tests with positive radial support satisfy the punctured-test support
rule. -/
theorem bellmanAngularTest_support_punctured (ζ φ : ℝ → ℝ)
    (hcζ : HasCompactSupport ζ) (hcφ : HasCompactSupport φ)
    (hs : tsupport ζ ⊆ Ioi (0 : ℝ)) :
    tsupport (bellmanAngularTest ζ φ) ⊆ {q : ℝ × ℝ | q ≠ (0, 0)} := by
  intro q hq he
  have hx := (bellmanAngularTest_support_data ζ φ hcζ hcφ hs).2 hq
  rw [he] at hx
  change (0 : ℝ) < 0 at hx
  exact lt_irrefl 0 hx

end HypoellipticAleksandrov.KineticAleksandrov

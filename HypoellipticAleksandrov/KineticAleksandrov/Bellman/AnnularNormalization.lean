module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AnnularNormalizationMass
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AnnularNormalizationBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.RatioNormalizationMeasure
import Mathlib.Tactic

/-! # Common annular normalization and compact bounds for homogeneous adjoint pairs -/

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- A fixed radial cutoff normalizes every pair and uniformly controls every compact. -/
theorem bellman_pairs_annular_normalization (R : ℝ) (hR : 1 ≤ R)
    (beta : ℕ → ℝ) (mu eta : ℕ → Measure BellmanPuncturedPlane)
    (hp : ∀ n, IsBellmanAdjointPair 1 R (beta n) (mu n) (eta n))
    (hb : ∃ a b : ℝ, ∀ n, a ≤ beta n ∧ beta n ≤ b) :
    ∃ chi : (ℝ × ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) chi ∧ HasCompactSupport chi ∧
      tsupport chi ⊆ {q | 1 / 2 < bellmanGauge q ∧ bellmanGauge q < 4} ∧
      (∀ q, 0 ≤ chi q ∧ chi q ≤ 1) ∧
      (∀ q, 1 ≤ bellmanGauge q → bellmanGauge q ≤ 2 → chi q = 1) ∧
      (∃ chi0 : ℝ → ℝ, ∀ q, chi q = chi0 (bellmanGauge q)) ∧
      ∃ c : ℕ → ℝ, (∀ n, 0 < c n) ∧
        (∀ n, ∫ q, chi q.val ∂(ENNReal.ofReal (c n) • mu n) = 1) ∧
        ∀ K : Set BellmanPuncturedPlane, IsCompact K → ∃ C : ℝ≥0,
          ∀ n, (ENNReal.ofReal (c n) • mu n) K ≤ C ∧
            (ENNReal.ofReal (c n) • eta n) K ≤ C := by
  obtain ⟨chi, hchi, hc, hs, hr, hone, hrad⟩ := exists_bellman_annular_cutoff
  have hpos (n : ℕ) : 0 < ∫ q, chi q.val ∂mu n :=
    bellman_annular_integral_pos _ _ (hp n).1 (hp n).left_ne_zero
      (hp n).2.2.2.2.2.2.1 chi hchi.continuous hc hs (fun q => (hr q).1) hone
  have hn (n : ℕ) := bellman_annular_normalize (mu n) chi (hpos n)
  choose c hcp hcn using hn
  let nu (n : ℕ) := ENNReal.ofReal (c n) • mu n
  have hradnu (n : ℕ) : IsBellmanRadon (nu n) :=
    (hp n).1.smul _ ENNReal.ofReal_ne_top
  let (n : ℕ) : IsFiniteMeasureOnCompacts (nu n) := (hradnu n).1
  have hdeg (n : ℕ) : HasBellmanDensityDegree (beta n) (nu n) :=
    (hp n).2.2.2.2.2.2.1.smul _
  have hunit (n : ℕ) : nu n bellmanUnitAnnulus ≤ 1 := by
    have hi : Integrable (fun q : BellmanPuncturedPlane => chi q.val) (nu n) :=
      (hchi.continuous.comp continuous_subtype_val).integrable_of_hasCompactSupport
        (bellman_annular_test_compact chi hc hs)
    have h := hi.measure_le_integral (Filter.Eventually.of_forall
      (fun q : BellmanPuncturedPlane => (hr q.val).1))
      (s := bellmanUnitAnnulus) (fun q hq => by rw [hone _ hq.1 hq.2])
    rw [hcn n, ENNReal.ofReal_one] at h
    exact h
  refine ⟨chi, hchi, hc, hs, hr, hone, hrad, c, hcp, hcn, ?_⟩
  intro K hK
  obtain ⟨C, hC⟩ := bellman_homogeneous_compact_bound beta nu hdeg hunit hb K hK
  let M : ℝ≥0 := ⟨R, zero_le_one.trans hR⟩
  refine ⟨C + M * C, ?_⟩
  intro n
  have hm : nu n K ≤ (C : ℝ≥0∞) + M * C :=
    (hC n).trans (le_add_right le_rfl)
  have hh := smul_le_smul_left (ENNReal.ofReal (c n)) (hp n).2.2.2.2.1
  have he : (ENNReal.ofReal (c n) • eta n) ≤ ENNReal.ofReal R • nu n := by
    simpa only [nu, smul_smul, mul_comm] using hh
  have heK := Measure.le_iff.mp he K hK.measurableSet
  rw [Measure.smul_apply, smul_eq_mul] at heK
  have heM : ENNReal.ofReal R = (M : ℝ≥0∞) :=
    ENNReal.ofReal_eq_coe_nnreal (zero_le_one.trans hR)
  rw [heM] at heK
  constructor
  · simpa only [ENNReal.coe_add, ENNReal.coe_mul] using hm
  · calc (ENNReal.ofReal (c n) • eta n) K ≤ (M : ℝ≥0∞) * nu n K := heK
      _ ≤ (M : ℝ≥0∞) * C := mul_le_mul_right (hC n) _
      _ ≤ (C : ℝ≥0∞) + M * C := le_add_left le_rfl
      _ = _ := by simp only [ENNReal.coe_add, ENNReal.coe_mul]

end HypoellipticAleksandrov.KineticAleksandrov

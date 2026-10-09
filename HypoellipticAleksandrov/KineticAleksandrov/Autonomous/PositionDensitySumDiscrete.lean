module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionDensitySumGrid

/-! # Summing the source overlap convolution on the two-index lattice -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory
open scoped ENNReal

/-- Young's inequality in the source-index rather than displacement-index convention. -/
theorem position_two_index_young_source (w a : ℤ × ℤ → ℝ≥0∞) (q : ℝ) (hq : 1 < q) :
    (∑' g, (∑' h, w (g - h) * a h) ^ q) ≤
      (∑' h, w h) ^ q * ∑' g, a g ^ q := by
  have he (g : ℤ × ℤ) : (∑' h, w (g - h) * a h) =
      ∑' h, w h * a (g - h) := by
    have h := (Equiv.subLeft g).tsum_eq (fun h => w (g - h) * a h)
    simpa only [Equiv.subLeft_apply, sub_sub_cancel] using h.symm
  simp_rw [he]
  exact position_two_index_young w a q hq

/-- The source overlap q-power sum is bounded by the starting-mass q-power sum. -/
theorem position_overlap_power_sum (c₀ : ℝ) (hc₀ : 0 < c₀)
    (nu : Measure Point) (c : Clock) (s x q : ℝ) (hq : 1 < q) :
    (∑' b : ℕ × ℤ, (∑' a : ℕ × ℤ,
      positionOverlapWeight c₀ b.1 a.1 b.2 a.2 *
        nu (enlargedStartCell c s x a.1 a.2)) ^ q) ≤
      (ENNReal.ofReal (Real.exp (2 * c₀)) *
        ∑' h, ENNReal.ofReal (positionYoungKernel (c₀ / 12) h)) ^ q *
      ∑' a : ℕ × ℤ, nu (enlargedStartCell c s x a.1 a.2) ^ q := by
  let w := fun h => ENNReal.ofReal (positionYoungKernel (c₀ / 12) h)
  let a := positionMassSequence nu c s x
  let D := ENNReal.ofReal (Real.exp (2 * c₀))
  have hcell (b : ℕ × ℤ) : (∑' z : ℕ × ℤ,
      positionOverlapWeight c₀ b.1 z.1 b.2 z.2 *
        nu (enlargedStartCell c s x z.1 z.2)) ≤
      D * ∑' h, w (positionIndexEmbedding b - h) * a h := by
    calc
      _ ≤ ∑' z : ℕ × ℤ, D * w (positionIndexEmbedding b - positionIndexEmbedding z) *
          a (positionIndexEmbedding z) := by
        apply ENNReal.tsum_le_tsum
        intro z
        change _ ≤ D * w (positionIndexEmbedding b - positionIndexEmbedding z) *
          positionMassSequence nu c s x (positionIndexEmbedding z)
        rw [positionMassSequence_embed]
        exact mul_le_mul_left (positionOverlapWeight_le c₀ hc₀ b.1 z.1 b.2 z.2) _
      _ = D * ∑' z : ℕ × ℤ,
          w (positionIndexEmbedding b - positionIndexEmbedding z) *
            a (positionIndexEmbedding z) := by
        simp_rw [mul_assoc]
        rw [ENNReal.tsum_mul_left]
      _ ≤ _ := mul_le_mul_right (ENNReal.tsum_comp_le_tsum_of_injective
        positionIndexEmbedding_injective
        (fun h => w (positionIndexEmbedding b - h) * a h)) D
  calc
    _ ≤ ∑' b : ℕ × ℤ, (D * ∑' h, w (positionIndexEmbedding b - h) * a h) ^ q :=
      ENNReal.tsum_le_tsum (fun b => ENNReal.rpow_le_rpow (hcell b) (by linarith))
    _ = D ^ q * ∑' b : ℕ × ℤ,
        (∑' h, w (positionIndexEmbedding b - h) * a h) ^ q := by
      simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith : 0 ≤ q)]
      rw [ENNReal.tsum_mul_left]
    _ ≤ D ^ q * ∑' g, (∑' h, w (g - h) * a h) ^ q :=
      mul_le_mul_right (ENNReal.tsum_comp_le_tsum_of_injective
        positionIndexEmbedding_injective (fun g => (∑' h, w (g - h) * a h) ^ q)) _
    _ ≤ D ^ q * ((∑' h, w h) ^ q * ∑' g, a g ^ q) :=
      mul_le_mul_right (position_two_index_young_source w a q hq) _
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.mul_rpow_of_nonneg _ _ (by linarith : 0 ≤ q),
        positionMassSequence_power_sum nu c s x q (by linarith)]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

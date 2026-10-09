module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionDensitySumDiscrete
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionDensitySumPartition
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-! # The source global position-density q-power estimate -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory
open scoped ENNReal

/-- The overlap convolution gives the source global density power bound. -/
theorem position_density_power_sum (hpush : PushforwardStatement)
    (htail : RestartTailStatement)
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (q : ℝ) (hq : 1 < q ∧ q < 3 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam)
      (c : Clock) (_hc : |c.vbar| = 2 * c.r) (s x : ℝ)
      (nu : Measure Point) [IsFiniteMeasure nu],
      (∀ᵐ e ∂nu, s ≤ e.time ∧ e.velocity 0 ∈ c.active) →
      (∫⁻ z, positionMixtureDensity hH hLE hlam hLam A c nu z ^ q ∂volume) ≤
        ENNReal.ofReal (C * c.r ^ (6 - 4 * q)) *
          ∑' a : ℕ × ℤ, nu (enlargedStartCell c s x a.1 a.2) ^ q := by
  obtain ⟨C, c₀, hC, hc₀, hd⟩ :=
    position_density_convolution_positive hpush htail hH hLE hlam hLam q hq
  let W := ∑' h, positionYoungKernel (c₀ / 12) h
  have hs := positionYoungKernel_summable (c₀ / 12) (by linarith)
  have hw (h : ℤ × ℤ) : 0 ≤ positionYoungKernel (c₀ / 12) h :=
    mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have hW : 0 < W := hs.tsum_pos (fun _ => hw _) (0, 0) (by
    exact mul_pos (Real.exp_pos _) (Real.exp_pos _))
  have hWe : (∑' h, ENNReal.ofReal (positionYoungKernel (c₀ / 12) h)) =
      ENNReal.ofReal W := (ENNReal.ofReal_tsum_of_nonneg hw hs).symm
  let D := C * Real.exp (2 * c₀) * W
  have hD : 0 < D := mul_pos (mul_pos hC (Real.exp_pos _)) hW
  refine ⟨D ^ q, Real.rpow_pos_of_pos hD q, ?_⟩
  intro A c hc s x nu hfinite hnu
  have hq0 : 0 < q := by linarith [hq.1]
  rw [positionMixtureDensity_power_partition hpush hH hLE hlam hLam A c hc nu s x q hq0 hnu]
  calc
    _ ≤ ∑' b : ℕ × ℤ, (ENNReal.ofReal (C * c.r ^ (6 / q - 4)) *
        ∑' a : ℕ × ℤ, positionOverlapWeight c₀ b.1 a.1 b.2 a.2 *
          nu (enlargedStartCell c s x a.1 a.2)) ^ q :=
      ENNReal.tsum_le_tsum (fun b => ENNReal.rpow_le_rpow
        (hd A c hc s x nu hnu b.1 b.2) hq0.le)
    _ = ENNReal.ofReal (C * c.r ^ (6 / q - 4)) ^ q *
        ∑' b : ℕ × ℤ, (∑' a : ℕ × ℤ, positionOverlapWeight c₀ b.1 a.1 b.2 a.2 *
          nu (enlargedStartCell c s x a.1 a.2)) ^ q := by
      simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le]
      rw [ENNReal.tsum_mul_left]
    _ ≤ ENNReal.ofReal (C * c.r ^ (6 / q - 4)) ^ q *
        ((ENNReal.ofReal (Real.exp (2 * c₀)) * ENNReal.ofReal W) ^ q *
          ∑' a : ℕ × ℤ, nu (enlargedStartCell c s x a.1 a.2) ^ q) := by
      rw [← hWe]
      exact mul_le_mul_right (position_overlap_power_sum c₀ hc₀ nu c s x q hq.1) _
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.mul_rpow_of_nonneg _ _ hq0.le,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← ENNReal.ofReal_mul (mul_nonneg hC.le (Real.rpow_nonneg c.positive.le _)),
        ENNReal.ofReal_rpow_of_pos
          (mul_pos (mul_pos hC (Real.rpow_pos_of_pos c.positive _))
            (mul_pos (Real.exp_pos _) hW))]
      congr 2
      have hbase : C * c.r ^ (6 / q - 4) * (Real.exp (2 * c₀) * W) =
          D * c.r ^ (6 / q - 4) := by dsimp [D]; ring
      rw [hbase, Real.mul_rpow hD.le (Real.rpow_nonneg c.positive.le _),
        ← Real.rpow_mul c.positive.le]
      congr 2
      field_simp

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

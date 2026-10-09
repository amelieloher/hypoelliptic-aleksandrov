module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.SourceNotation

/-! # Euclidean frequency normalization for kinetic blocks -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Decay

/-- A nonzero Euclidean frequency has strictly positive Euclidean norm. -/
theorem frequency_norm_pos {d : ℕ} {ξ : PDE.Vec d} (hξ : ξ ≠ 0) :
    0 < PDE.vecEuclideanNorm ξ :=
  lt_of_le_of_ne (PDE.vecEuclideanNorm_nonneg ξ)
    (Ne.symm (fun h => hξ (PDE.vecEuclideanNorm_eq_zero_iff.mp h)))

/-- The source radius gives the required block duration and a unit rescaled frequency. -/
theorem frequency_radius_identities {d : ℕ} {ξ : PDE.Vec d} (hξ : ξ ≠ 0) :
    let r := PDE.vecEuclideanNorm ξ ^ (-(1 / 3 : ℝ))
    0 < r ∧ r ^ 2 = PDE.vecEuclideanNorm ξ ^ (-(2 / 3 : ℝ)) ∧
      PDE.vecNormSq (r ^ 3 • ξ) = 1 := by
  dsimp only
  let N := PDE.vecEuclideanNorm ξ
  have hN : 0 < N := frequency_norm_pos hξ
  have hr : 0 < N ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hN _
  have h2 : (N ^ (-(1 / 3 : ℝ))) ^ 2 = N ^ (-(2 / 3 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    norm_num
  have h3 : (N ^ (-(1 / 3 : ℝ))) ^ 3 = N⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    norm_num [Real.rpow_neg_one]
  refine ⟨hr, h2, ?_⟩
  rw [← PDE.vecEuclideanNorm_sq, PDE.vecEuclideanNorm_smul, h3,
    abs_of_pos (inv_pos.mpr hN)]
  change (N⁻¹ * N) ^ 2 = 1
  rw [inv_mul_cancel₀ hN.ne']
  norm_num

end HypoellipticAleksandrov.KineticAleksandrov.Decay

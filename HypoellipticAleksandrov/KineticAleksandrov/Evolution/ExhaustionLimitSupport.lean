module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitCover
public import HypoellipticAleksandrov.KineticAleksandrov.BoundedBorel

/-! # Deriving the collar margin from compact interior terminal support -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov Set

/-- Compact terminal support strictly inside the original moving ball has the
positive support margin required by the source collar construction. -/
theorem exists_innerBall_terminal_support_margin {n : ℕ} {Γ : ℝ → PDE.Vec n}
    {r0 τ : ℝ} (hr0 : 0 < r0) (F : BoundedBorel (EvolutionAmbientState n))
    (hFc : HasCompactSupport (F : EvolutionAmbientState n → ℝ))
    (hs : ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
      q.1 ∈ movingDomain (PDE.euclideanBall 0 r0) Γ τ) :
    ∃ d : ℝ, 0 < d ∧ d < r0 / 4 ∧
      ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
        4 * d ≤ r0 - PDE.vecEuclideanNorm (q.1 - Γ τ) := by
  by_cases hne : (tsupport (F : EvolutionAmbientState n → ℝ)).Nonempty
  · have hc : Continuous (fun q : EvolutionAmbientState n =>
        PDE.vecEuclideanNorm (q.1 - Γ τ)) :=
      PDE.continuous_vecEuclideanNorm.comp (continuous_fst.sub continuous_const)
    obtain ⟨q0, hq0, hmax⟩ := hFc.exists_isMaxOn hne hc.continuousOn
    let gap := r0 - PDE.vecEuclideanNorm (q0.1 - Γ τ)
    have hgap : 0 < gap := sub_pos.mpr ((mem_movingBall_iff_norm_lt hr0).mp (hs q0 hq0))
    let d := min (r0 / 8) (gap / 8)
    have hd : 0 < d := lt_min (by positivity) (by positivity)
    have hdr : d < r0 / 4 := (min_le_left _ _).trans_lt (by linarith)
    refine ⟨d, hd, hdr, fun q hq => ?_⟩
    have hqm : PDE.vecEuclideanNorm (q.1 - Γ τ) ≤
        PDE.vecEuclideanNorm (q0.1 - Γ τ) := hmax hq
    have hdm : d ≤ gap / 8 := min_le_right _ _
    dsimp only [gap] at hgap hdm
    linarith
  · refine ⟨r0 / 8, by positivity, by linarith, fun q hq => ?_⟩
    exact (hne ⟨q, hq⟩).elim

end HypoellipticAleksandrov.KineticAleksandrov

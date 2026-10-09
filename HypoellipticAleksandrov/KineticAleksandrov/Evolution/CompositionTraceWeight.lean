module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.CompositionTraceSlice
import Mathlib.Tactic.Linarith

/-! # Proper state weights and Euclidean radial control

The ambient norm is used only for compactness. The propagated comparison error is
expressed in the source's explicit Euclidean squared radius.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Metric

/-- Sublevel sets of the quadratic norm weight are compact in finite dimension. -/
theorem isCompact_quadratic_weight_sublevel
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (R : ℝ) : IsCompact {x : E | 1 + ‖x‖ ^ 2 ≤ R} := by
  apply (isCompact_closedBall (0 : E) (|R| + 1)).of_isClosed_subset
    (isClosed_le (continuous_const.add (continuous_norm.pow 2)) continuous_const)
  intro x hx
  rw [mem_closedBall_zero_iff]
  have hn := norm_nonneg x
  have hR := le_abs_self R
  have hs := sq_nonneg (‖x‖ - 1)
  have hr := abs_nonneg R
  have hx' : 1 + ‖x‖ ^ 2 ≤ R := hx
  nlinarith only [hn, hR, hs, hr, hx']

/-- The quadratic ambient norm weight is bounded by the actual Euclidean state weight. -/
theorem quadratic_state_weight_le_radial {n : ℕ} (r : ℝ) (x : EvolutionAmbientState n) :
    1 + ‖x‖ ^ 2 ≤ 1 + radialSq (⟨r, x.1, x.2⟩ : KineticPoint n) := by
  have hcomponent (y : PDE.Vec n) : ‖y‖ ^ 2 ≤ PDE.vecNormSq y := by
    rw [← PDE.vecEuclideanNorm_sq]
    exact (sq_le_sq₀ (norm_nonneg _) (PDE.vecEuclideanNorm_nonneg _)).mpr
      (PDE.norm_le_vecEuclideanNorm y)
  have h₁ := hcomponent x.1
  have h₂ := hcomponent x.2
  rw [Prod.norm_def]
  dsimp only [radialSq]
  rcases le_total ‖x.1‖ ‖x.2‖ with h | h
  · rw [max_eq_right h]
    linarith only [h₂, PDE.vecNormSq_nonneg x.1]
  · rw [max_eq_left h]
    linarith only [h₁, PDE.vecNormSq_nonneg x.2]

end HypoellipticAleksandrov.KineticAleksandrov

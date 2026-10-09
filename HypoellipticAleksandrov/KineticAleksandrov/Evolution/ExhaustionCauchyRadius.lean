module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionTerminalRadius
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.CurveRegularityExhaustion

/-!
# Uniform radius and support margins for the exhaustion comparison

These lemmas discharge the explicit geometric conditions in the finite comparison:
a common positive diffused-radius gap gives a transported cutoff threshold, and a
sufficiently small inner-ball error preserves the compact terminal support margin.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set

/-- A fixed common inner cylinder is contained in all sufficiently large ellipsoids
whose diffused radii have a common lower bound separated from the inner cylinder. -/
theorem exists_transportedRadius_common_innerCylinder
    {rmin ρ η : ℝ} (hρ : 0 < ρ) (hη : 0 ≤ η) (hgap : ρ + η < rmin) (S : ℝ) :
    ∃ R0 : ℝ, 0 < R0 ∧ ∀ r R : ℝ, rmin ≤ r → R0 ≤ R →
      (ρ + η) ^ 2 / r ^ 2 + S ^ 2 / R ^ 2 < 1 := by
  have hrmin : 0 < rmin := lt_trans (by linarith) hgap
  obtain ⟨R0, hR0, hR⟩ := exists_transportedRadius_terminal_window hrmin
    (sub_pos.mpr hgap) (by linarith : rmin - (ρ + η) < rmin) S
  refine ⟨R0, hR0, fun r R hr hRR => ?_⟩
  have hsize := hR R hRR
  have he : rmin - (rmin - (ρ + η)) = ρ + η := by ring
  rw [he] at hsize
  have hdiv : (ρ + η) ^ 2 / r ^ 2 ≤ (ρ + η) ^ 2 / rmin ^ 2 :=
    div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hrmin)
      (pow_le_pow_left₀ hrmin.le hr 2)
  linarith

/-- The original terminal support margin survives the source inner-ball approximation
with radius loss α and centre error at most α/2, once α ≤ d. -/
theorem terminal_support_margin_of_innerBall_close
    {n : ℕ} {Γ g : ℝ → PDE.Vec n} {τ r0 α d : ℝ} (hαd : α ≤ d)
    {F : BoundedBorel (EvolutionAmbientState n)}
    (hsupp : ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
      4 * d ≤ r0 - PDE.vecEuclideanNorm (q.1 - Γ τ))
    (hc : PDE.vecEuclideanNorm (g τ - Γ τ) ≤ α / 2) :
    ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
      2 * d ≤ (r0 - α) - PDE.vecEuclideanNorm (q.1 - g τ) := by
  intro q hq
  have hclose := vecEuclideanNorm_sub_add_le (c := (0 : PDE.Vec n)) hc q.1
  simp only [add_zero] at hclose
  have hs := hsupp q hq
  have hα0 : 0 ≤ α := by
    have := (PDE.vecEuclideanNorm_nonneg _).trans hc
    linarith
  linarith

end HypoellipticAleksandrov.KineticAleksandrov

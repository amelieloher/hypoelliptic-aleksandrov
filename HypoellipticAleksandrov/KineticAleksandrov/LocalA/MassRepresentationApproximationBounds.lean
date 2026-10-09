module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.MassRepresentationApproximation

/-! # The compact approximation error fits the actual quadratic growth barrier -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set Parabolic

/-- The growth barrier dominates the squared supremum norm used only for compact exhaustion. -/
theorem massGrowthBarrier_norm_lower {d : ℕ} (Lam T : ℝ) (P : KineticPoint d)
    (hP : P.time ≤ T) : ‖P.position‖ ^ 2 ≤ massGrowthBarrier Lam T P := by
  have hn := sq_le_sq₀ (norm_nonneg P.position) (PDE.vecEuclideanNorm_nonneg P.position)
    |>.mpr (PDE.norm_le_vecEuclideanNorm P.position)
  rw [PDE.vecEuclideanNorm_sq] at hn
  exact hn.trans ((le_add_of_nonneg_left zero_le_one).trans
    (massGrowthBarrier_lower Lam T P hP))

/-- A sufficiently large compact aperture turns a bounded approximation into weighted error. -/
theorem mass_trace_probe_weighted {d : ℕ} (Lam a T : ℝ) (v₀ : PDE.Vec d) (R : ℝ)
    (u φ : KineticPoint d → ℝ) (M L ε : ℝ) (hε : 0 ≤ ε)
    (hb : ∀ P ∈ localClosedStrip a T v₀ R, |u P| ≤ M)
    (hφ : ∀ P, |φ P| ≤ M + ε)
    (hclose : ∀ P ∈ localClosedStrip a T v₀ R, ‖P.position‖ ≤ L → |φ P - u P| ≤ ε)
    (hL : 0 ≤ L) (hsize : 2 * M + ε ≤ ε * L ^ 2) :
    ∀ P ∈ localClosedStrip a T v₀ R,
      |φ P - u P| ≤ ε * massGrowthBarrier Lam T P := by
  intro P hP
  by_cases hp : ‖P.position‖ ≤ L
  · exact (hclose P hP hp).trans (le_mul_of_one_le_right hε
      ((le_add_of_nonneg_right (PDE.vecNormSq_nonneg P.position)).trans
        (massGrowthBarrier_lower Lam T P hP.2.1)))
  · have hlp : L ^ 2 ≤ ‖P.position‖ ^ 2 :=
      (sq_le_sq₀ hL (norm_nonneg _)).mpr (not_le.mp hp).le
    exact ((abs_sub (φ P) (u P)).trans (add_le_add (hφ P) (hb P hP))).trans
      ((by linarith only [hsize] : M + ε + M ≤ ε * L ^ 2).trans
        (mul_le_mul_of_nonneg_left (hlp.trans (massGrowthBarrier_norm_lower Lam T P hP.2.1))
          hε))

/-- A concrete growing aperture meets the weighted-error size requirement. -/
theorem mass_aperture_size (M : ℝ) (hM : 0 ≤ M) (n : ℕ) :
    let ε := 1 / ((n : ℝ) + 1)
    let L := (2 * M + 1) * ((n : ℝ) + 1) + 1 + (n : ℝ)
    0 < ε ∧ ε ≤ 1 ∧ 0 ≤ L ∧ (n : ℝ) ≤ L ∧ 2 * M + ε ≤ ε * L ^ 2 := by
  dsimp only
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hp : 0 < (n : ℝ) + 1 := by positivity
  have he : 0 < 1 / ((n : ℝ) + 1) := one_div_pos.mpr hp
  have he1 : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one hp).mpr (by linarith only [hn])
  let L := (2 * M + 1) * ((n : ℝ) + 1) + 1 + (n : ℝ)
  have hL : 1 ≤ L := by dsimp only [L]; nlinarith only [hn, hM]
  have hnL : (n : ℝ) ≤ L := by dsimp only [L]; nlinarith only [hn, hM]
  have hsz : (2 * M + 1) * ((n : ℝ) + 1) ≤ L := by
    dsimp only [L]
    linarith only [hn]
  have hsq : L ≤ L ^ 2 := by nlinarith only [hL]
  have hsz' : 2 * M + 1 ≤ (1 / ((n : ℝ) + 1)) * L := by
    rw [one_div, ← div_eq_inv_mul]
    exact (le_div_iff₀ hp).mpr hsz
  refine ⟨he, he1, (by linarith only [hL]), hnL, ?_⟩
  have hsmall : 2 * M + 1 / ((n : ℝ) + 1) ≤ 2 * M + 1 := by
    linarith only [he1]
  exact hsmall.trans (hsz'.trans (mul_le_mul_of_nonneg_left hsq he.le))

end HypoellipticAleksandrov.KineticAleksandrov.LocalA

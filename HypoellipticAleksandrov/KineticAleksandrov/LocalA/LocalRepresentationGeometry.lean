module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.ConeSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.DomainDominationMeasure

/-! # The strict time and position margins of the local exit cone -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set Parabolic

/-- Centered positions add along a cone displacement without changing the center velocity. -/
theorem relativePosition_cone_add {d : ℕ} (Z₀ P Q : KineticPoint d) :
    relativePosition Z₀ Q = relativePosition Z₀ P +
      (Q.position - P.position - (Q.time - P.time) • Z₀.velocity) := by
  ext i
  simp only [relativePosition, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The reached cone has the source's exact strict time and position margins. -/
theorem local_cone_margins {d : ℕ} (Z₀ P Q : KineticPoint d)
    {R : ℝ} (hR : 0 < R)
    (hP : P ∈ forwardCylinder Z₀ (3 * R / 4) (by positivity))
    (htlo : P.time ≤ Q.time) (hthi : Q.time ≤ P.time + R ^ 2 / 8)
    (hcone : PDE.vecEuclideanNorm
      (Q.position - P.position - (Q.time - P.time) • Z₀.velocity) ≤
        R * (Q.time - P.time)) :
    Z₀.time < Q.time ∧ Q.time < Z₀.time + (9 / 16 + 1 / 8 : ℝ) * R ^ 2 ∧
      PDE.vecEuclideanNorm (relativePosition Z₀ Q) <
        (27 / 64 + 1 / 8 : ℝ) * R ^ 3 := by
  have hp := (mem_forwardCylinder_iff Z₀ P _ (by positivity)).mp hP
  have hx := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
    (pow_pos (by positivity : 0 < 3 * R / 4) 3)).mp hp.2.2.2
  simp only [sub_zero] at hx
  refine ⟨hp.1.trans_le htlo, ?_, ?_⟩
  · nlinarith only [hp.2.1, hthi]
  · rw [relativePosition_cone_add Z₀ P Q]
    have hΔ : Q.time - P.time ≤ R ^ 2 / 8 := by linarith only [hthi]
    have hc := hcone.trans (mul_le_mul_of_nonneg_left hΔ hR.le)
    have hn := PDE.vecEuclideanNorm_add_le (relativePosition Z₀ P)
      (Q.position - P.position - (Q.time - P.time) • Z₀.velocity)
    nlinarith only [hx, hc, hn]

/-- A smooth compact position cutoff can be chosen between literal Euclidean radii. -/
theorem exists_local_position_cutoff {d : ℕ} {R : ℝ} (hR : 0 < R) :
    ∃ χ : PDE.Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ PDE.euclideanBall 0 (R ^ 3) ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      ∀ x ∈ PDE.euclideanClosedBall 0 ((3 / 4 : ℝ) * R ^ 3), χ x = 1 := by
  apply exists_smooth_bump_of_isCompact_subset_isOpen
    (PDE.isCompact_euclideanClosedBall 0 (by positivity))
    (PDE.isOpen_euclideanBall 0 (R ^ 3))
  exact PDE.euclideanClosedBall_subset_euclideanBall (by positivity)
    (by nlinarith only [pow_pos hR 3])

end HypoellipticAleksandrov.KineticAleksandrov.LocalA

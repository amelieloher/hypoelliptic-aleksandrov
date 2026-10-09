module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCollarBound
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.CurveRegularityExhaustion

/-!
# Common inner-cylinder geometry for the source Cauchy comparison

All ellipsoid containment conditions here are explicit numerical radius inequalities.
The diffused boundary distance estimate uses only closeness of the two centre curves.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set

/-- A common bounded inner cylinder lies strictly inside a finite ellipsoid whenever
the explicit block-radius inequality holds. -/
theorem mem_straightenedEllipsoid_of_common_innerCylinder
    {n : ℕ} {Γ g : ℝ → PDE.Vec n} {α τ ρ η S r R : ℝ}
    (hρ : 0 < ρ) (hr : 0 < r) (hR : 0 < R)
    (hclose : ∀ s ∈ Icc α τ, PDE.vecEuclideanNorm (g s - Γ s) ≤ η)
    (hsize : (ρ + η) ^ 2 / r ^ 2 + S ^ 2 / R ^ 2 < 1)
    {p : KineticPoint n}
    (hp : p ∈ movingClosedSlab (PDE.euclideanBall 0 ρ) Γ α τ ∩
      {q | radialSq q ≤ S ^ 2}) :
    (straightenedPoint g p).2 ∈ openEllipsoid (straightenedEllipsoidMatrix n r R) := by
  have hc := hclose p.time ⟨hp.1.1, hp.1.2.1⟩
  have hsq := vecNormSq_le_of_mem_closure_movingDomain hp.1.2.2
  have hnorm : PDE.vecEuclideanNorm (p.position - Γ p.time) ≤ ρ := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨hρ.le, by simpa only [add_zero] using hsq⟩
  have hng := vecEuclideanNorm_sub_add_le (c := (0 : PDE.Vec n)) hc p.position
  simp only [add_zero] at hng
  have hng' : PDE.vecEuclideanNorm (p.position - g p.time) ≤ ρ + η :=
    hng.trans (add_le_add hnorm (le_refl η))
  have hY : PDE.vecNormSq (p.position - g p.time) ≤ (ρ + η) ^ 2 := by
    have he := pow_le_pow_left₀ (PDE.vecEuclideanNorm_nonneg _) hng' 2
    rwa [PDE.vecEuclideanNorm_sq] at he
  have hZ : PDE.vecNormSq p.velocity ≤ S ^ 2 := by
    have hb : PDE.vecNormSq p.position + PDE.vecNormSq p.velocity ≤ S ^ 2 := hp.2
    linarith [PDE.vecNormSq_nonneg p.position]
  rw [(straightenedEllipsoid_characterization n r R hr hR).2]
  simp only [straightenedPoint, spatialY_spatialPack, spatialZ_spatialPack]
  exact lt_of_le_of_lt
    (add_le_add (div_le_div_of_nonneg_right hY (sq_nonneg r))
      (div_le_div_of_nonneg_right hZ (sq_nonneg R))) hsize

/-- On the common diffused lateral face, the distance to any approximating ball boundary
is at most the common collar error, independently of the transported radius. -/
theorem distance_to_approximating_boundary_le_of_common_frontier
    {n : ℕ} {Γ g : ℝ → PDE.Vec n} {ρ r r0 η : ℝ} (hρ : 0 < ρ) (hr : r ≤ r0)
    {p : KineticPoint n} (hc : PDE.vecEuclideanNorm (g p.time - Γ p.time) ≤ η)
    (hp : p.position ∈ frontier (movingDomain (PDE.euclideanBall 0 ρ) Γ p.time)) :
    r - PDE.vecEuclideanNorm (p.position - g p.time) ≤ r0 - ρ + η := by
  have hs := vecNormSq_eq_of_mem_frontier_movingDomain hp
  have hn : PDE.vecEuclideanNorm (p.position - Γ p.time) = ρ := by
    unfold PDE.vecEuclideanNorm
    simp only [add_zero] at hs
    rw [hs, Real.sqrt_sq hρ.le]
  have hc' : PDE.vecEuclideanNorm (Γ p.time - g p.time) ≤ η := by
    rwa [PDE.vecEuclideanNorm_sub_comm]
  have hb := vecEuclideanNorm_sub_add_le (c := (0 : PDE.Vec n)) hc' p.position
  simp only [add_zero, hn] at hb
  linarith

end HypoellipticAleksandrov.KineticAleksandrov

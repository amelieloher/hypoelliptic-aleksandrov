module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCollar

/-!
# The two-part collar bound on the entire actual finite ellipsoid

The bound combines the finite-cylinder constant estimate and the proved collar estimate.
No whole-domain solution is consumed. Constants are independent of the transported radius.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set
open scoped MatrixOrder

/-- The actual finite Dirichlet solution obeys the full minimum-form collar bound on
its entire inset closed cylinder, uniformly in the transported truncation radius. -/
theorem abs_le_min_collar_straightened_dirichlet
    {n : ℕ} {lam Lam : ℝ} {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    (hlam : 0 < lam) (hB : HasEverywhereLoewnerBounds lam Lam B)
    (hBs : IsSmoothFullKineticCoefficient B) (hbs : IsSmoothDrift b)
    {a α τ r R d L C ε : ℝ} (haα : a < α) (hατ : α < τ)
    (hr : 0 < r) (hR : 0 < R) (hd : 0 < d) (hdr : d < r)
    {g : ℝ → PDE.Vec n} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hL : 0 ≤ L)
    (hgL : ∀ s t, PDE.vecEuclideanNorm (g s - g t) ≤ L * |s - t|)
    (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (F : BoundedBorel (EvolutionAmbientState n)) (hFC : ∀ q, |F q| ≤ C)
    (hsupp : ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
      2 * d ≤ r - PDE.vecEuclideanNorm (q.1 - g τ))
    (u : TimeVelocity (n + n) → ℝ)
    (hu : IsClassicalBackwardDirichletSolution a τ
      (openEllipsoid (straightenedEllipsoidMatrix n r R))
      (straightenedCoefficient B g ε) (straightenedDrift b g)
      (fun _ _ => 0) (fun _ _ => 0)
      (fun x => F (g τ + spatialY x, spatialZ x)) (fun _ => 0) u) :
    ∀ p ∈ straightenedPoint g ⁻¹' scalarParabolicClosedCylinder α τ
      (openEllipsoid (straightenedEllipsoidMatrix n r R)),
      |straightenedPullback g u p| ≤ C * min 1
        (barrierW (collarKappa L lam) (r - PDE.vecEuclideanNorm (p.position - g p.time)) /
          barrierW (collarKappa L lam) d) := by
  intro p hp
  have hκ : 0 < collarKappa L lam := div_pos (by linarith) hlam
  have hW := barrierW_pos hκ hd
  have hbound := abs_le_straightened_dirichlet hlam hB hBs hbs (haα.trans hατ) hr hR
    hg hε F u hu hC hFC (straightenedPoint g p)
    ⟨⟨haα.le.trans hp.1.1, hp.1.2⟩, hp.2⟩
  by_cases hratio : 1 ≤
      barrierW (collarKappa L lam) (r - PDE.vecEuclideanNorm (p.position - g p.time)) /
        barrierW (collarKappa L lam) d
  · rw [min_eq_left hratio, mul_one]
    exact hbound
  · have hw : barrierW (collarKappa L lam) (r - PDE.vecEuclideanNorm (p.position - g p.time)) ≤
        barrierW (collarKappa L lam) d := by
      exact (div_le_one hW).mp (le_of_lt (not_le.mp hratio))
    have hd' := le_of_barrierW_le hκ hw
    have hn : r - d ≤ PDE.vecEuclideanNorm (p.position - g p.time) := by linarith
    have hS : (r - d) ^ 2 ≤ centreSq 0 g p := by
      have he := pow_le_pow_left₀ (by linarith : 0 ≤ r - d) hn 2
      simpa only [PDE.vecEuclideanNorm_sq, centreSq, add_zero] using he
    have he := abs_le_collar_straightened_dirichlet hlam hB hBs hbs haα hατ hr hR hd hdr
      hg hL hgL hε hC F hFC hsupp u hu p hp hS
    rw [min_eq_right (le_of_lt (not_le.mp hratio))]
    simpa only [collarSupersolution, collarBarrier, collarProfile, barrierW, add_zero,
      PDE.vecEuclideanNorm, mul_div_assoc, div_mul_eq_mul_div] using he

end HypoellipticAleksandrov.KineticAleksandrov

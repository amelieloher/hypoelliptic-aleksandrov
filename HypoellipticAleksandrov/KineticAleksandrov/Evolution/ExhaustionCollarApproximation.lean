module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCollarBound
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCauchyRadius

/-!
# Uniform collar control relative to the original moving boundary

The actual approximating solution is controlled by the collar distance for the original
curve. The radius loss dominates the centre error, so no index-dependent trace modulus
is introduced. This estimate is available before the exhaustion limit exists.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set
open scoped MatrixOrder

/-- The actual approximant has a common collar bound measured from the original curve.
All constants are independent of the approximation error and transported radius. -/
theorem abs_le_original_collar_straightened_dirichlet
    {n : ℕ} {lam Lam : ℝ} {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    (hlam : 0 < lam) (hB : HasEverywhereLoewnerBounds lam Lam B)
    (hBs : IsSmoothFullKineticCoefficient B) (hbs : IsSmoothDrift b)
    {a α τ r0 R β d L C ε : ℝ} (haα : a < α) (hατ : α < τ)
    (hR : 0 < R) (hβ : 0 ≤ β) (hβd : β ≤ d) (hd : 0 < d) (hdr : d < r0 / 4)
    {Γ g : ℝ → PDE.Vec n} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hL : 0 ≤ L)
    (hgL : ∀ s t, PDE.vecEuclideanNorm (g s - g t) ≤ L * |s - t|)
    (hclose : ∀ s ∈ Icc α τ, PDE.vecEuclideanNorm (g s - Γ s) ≤ β / 2)
    (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (F : BoundedBorel (EvolutionAmbientState n)) (hFC : ∀ q, |F q| ≤ C)
    (hsupp : ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
      4 * d ≤ r0 - PDE.vecEuclideanNorm (q.1 - Γ τ))
    (u : TimeVelocity (n + n) → ℝ)
    (hu : IsClassicalBackwardDirichletSolution a τ
      (openEllipsoid (straightenedEllipsoidMatrix n (r0 - β) R))
      (straightenedCoefficient B g ε) (straightenedDrift b g)
      (fun _ _ => 0) (fun _ _ => 0)
      (fun x => F (g τ + spatialY x, spatialZ x)) (fun _ => 0) u) :
    ∀ p ∈ straightenedPoint g ⁻¹' scalarParabolicClosedCylinder α τ
      (openEllipsoid (straightenedEllipsoidMatrix n (r0 - β) R)),
      |straightenedPullback g u p| ≤ C *
        (barrierW (collarKappa L lam) (r0 - PDE.vecEuclideanNorm (p.position - Γ p.time)) /
          barrierW (collarKappa L lam) d) := by
  intro p hp
  have hs := terminal_support_margin_of_innerBall_close hβd hsupp
    (hclose τ ⟨hατ.le, le_rfl⟩)
  have he := abs_le_min_collar_straightened_dirichlet hlam hB hBs hbs haα hατ
    (by linarith : 0 < r0 - β) hR hd (by linarith : d < r0 - β)
    hg hL hgL hε hC F hFC hs u hu p hp
  have hc : PDE.vecEuclideanNorm (Γ p.time - g p.time) ≤ β / 2 := by
    rw [PDE.vecEuclideanNorm_sub_comm]
    exact hclose p.time hp.1
  have hh := vecEuclideanNorm_sub_add_le (c := (0 : PDE.Vec n)) hc p.position
  simp only [add_zero] at hh
  have hdist : (r0 - β) - PDE.vecEuclideanNorm (p.position - g p.time) ≤
      r0 - PDE.vecEuclideanNorm (p.position - Γ p.time) := by linarith
  have hκ : 0 < collarKappa L lam := div_pos (by linarith) hlam
  have hW := barrierW_pos hκ hd
  have hw : barrierW (collarKappa L lam)
      ((r0 - β) - PDE.vecEuclideanNorm (p.position - g p.time)) ≤
      barrierW (collarKappa L lam) (r0 - PDE.vecEuclideanNorm (p.position - Γ p.time)) := by
    rcases hdist.lt_or_eq with h | h
    · exact (barrierW_strictMono hκ h).le
    · rw [h]
  exact he.trans (mul_le_mul_of_nonneg_left
    ((min_le_right _ _).trans (div_le_div_of_nonneg_right hw hW.le)) hC)

end HypoellipticAleksandrov.KineticAleksandrov

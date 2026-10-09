module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2Cutoff
public import Mathlib.Topology.Order.Compact
import Lean.Elab.Tactic.Omega

/-!
# Seed sign control in dimensions at least two

The orthogonal direction is constructed in native coordinates, so the positive
Hessian direction requires exactly the source's dimension-at-least-two assumption.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- A native vector in dimension at least two has a nonzero perpendicular direction. -/
theorem exists_native_perpendicular (d : ℕ) (hd : 2 ≤ d) (z : PDE.Vec d) :
    ∃ w : PDE.Vec d, w ≠ 0 ∧ PDE.vecDot z w = 0 := by
  let i : Fin d := ⟨0, by omega⟩
  let j : Fin d := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j]
  by_cases hz : z i = 0
  · refine ⟨Pi.single i 1, ?_, ?_⟩
    · intro h
      have hh := congrFun h i
      simp at hh
    · simp [PDE.vecDot, Pi.single_apply, hz]
  · let w : PDE.Vec d := z i • Pi.single j 1 - z j • Pi.single i 1
    refine ⟨w, ?_, ?_⟩
    · intro h
      have hh := congrFun h j
      have hji : j ≠ i := Ne.symm hij
      simp [w, hji] at hh
      exact hz hh
    · simp [w, PDE.vecDot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib,
        Pi.single_apply]
      ring


/-- The seed has a strictly positive Hessian direction at every point. -/
theorem seed_positive_direction (d : ℕ) (hd : 2 ≤ d) (alpha C₀ sigma : ℝ)
    (ha : 0 < alpha) (hsigma : 0 < sigma) (y e : PDE.Vec d) :
    ∃ w : PDE.Vec d,
      0 < fderiv ℝ (fun z => fderiv ℝ (fun a => seed alpha C₀ sigma a e) z w) y w := by
  obtain ⟨w, hw, hperp⟩ := exists_native_perpendicular d hd (y - e)
  refine ⟨w, ?_⟩
  rw [seed_hessian_tangent alpha C₀ sigma hsigma y e w w hperp]
  have hn : 0 < PDE.vecNormSq w :=
    (PDE.vecNormSq_nonneg w).lt_of_ne' (PDE.vecNormSq_eq_zero_iff.not.mpr hw)
  exact mul_pos (seedTangentialEigenvalue_pos alpha sigma ha hsigma y e) hn

/-- Past the source threshold the seed has a strictly negative Hessian direction. -/
theorem seed_negative_direction {d : ℕ} (alpha C₀ sigma : ℝ)
    (ha : 0 < alpha) (hsigma : 0 < sigma) (y e : PDE.Vec d)
    (hthreshold : sigma ^ 2 < (1 - alpha) * PDE.vecNormSq (y - e)) :
    ∃ w : PDE.Vec d,
      fderiv ℝ (fun z => fderiv ℝ (fun a => seed alpha C₀ sigma a e) z w) y w < 0 := by
  refine ⟨y - e, ?_⟩
  rw [seed_hessian_radial alpha C₀ sigma hsigma]
  have hn : 0 < PDE.vecNormSq (y - e) := by
    by_contra h
    have hzero : PDE.vecNormSq (y - e) = 0 :=
      le_antisymm (le_of_not_gt h) (PDE.vecNormSq_nonneg _)
    rw [hzero, mul_zero] at hthreshold
    exact (sq_nonneg sigma).not_gt hthreshold
  exact mul_neg_of_neg_of_pos
    ((seedRadialEigenvalue_neg_iff alpha sigma ha hsigma y e).mpr hthreshold) hn

/-- A point in the small source seed ball has a uniformly positive position dot product. -/
theorem seed_ball_dot_lower {d : ℕ} (y e : PDE.Vec d)
    (he : PDE.vecNormSq e = 1) (hy : PDE.vecEuclideanNorm (y - e) ≤ 1 / 4) :
    (3 / 4 : ℝ) ≤ PDE.vecDot y e := by
  have henorm : PDE.vecEuclideanNorm e = 1 := by
    simp [PDE.vecEuclideanNorm, he]
  have hcs := PDE.abs_vecDot_le_vecEuclideanNorm_mul (y - e) e
  rw [henorm, mul_one] at hcs
  have hdot : PDE.vecDot (y - e) e = PDE.vecDot y e - 1 := by
    simp only [PDE.vecDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    change PDE.vecDot y e - PDE.vecNormSq e = _
    rw [he]
    rfl
  rw [hdot] at hcs
  have hh := (abs_le.mp (hcs.trans hy)).1
  linarith

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

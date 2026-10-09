module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
public import HypoellipticAleksandrov.KineticAleksandrov.EvolutionProblem

/-!
# A bounded interval is a one-dimensional ball

For `d = 1` an admissible bounded interval `(lo, hi)` is the Euclidean ball with centre
`(lo + hi)/2` and radius `(hi - lo)/2`, and the Euclidean distance to the centre is the absolute
value of the scalar coordinate.  The distance `d = r₀ - |y - m|` to the lateral boundary of the
ball is the distance to the nearer of the two endpoints.  Consequently an admissible domain
other than `ℝ^d` is always a ball, and the ball barriers of (A.1) apply to it.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open Set

/-- The midpoint of the interval `(lo, hi)` as a point of `Vec 1`. -/
def intervalCentre (lo hi : ℝ) : PDE.Vec 1 := fun _ => (lo + hi) / 2

/-- The distance `min (x - lo) (hi - x)` of a scalar coordinate to the endpoints of `(lo, hi)`. -/
def intervalLateralDist (lo hi x : ℝ) : ℝ := min (x - lo) (hi - x)

/-- The Euclidean norm on `Vec 1` is the absolute value of the coordinate. -/
theorem vecEuclideanNorm_vec_one (x : PDE.Vec 1) : PDE.vecEuclideanNorm x = |x 0| := by
  unfold PDE.vecEuclideanNorm
  rw [PDE.vecNormSq_eq_sum_sq, Fin.sum_univ_one, Real.sqrt_sq_eq_abs]

/-- The distance to the endpoints is the radius minus the distance to the midpoint. -/
theorem intervalLateralDist_eq (lo hi x : ℝ) :
    intervalLateralDist lo hi x = (hi - lo) / 2 - |x - (lo + hi) / 2| := by
  unfold intervalLateralDist
  rcases le_total x ((lo + hi) / 2) with h | h
  · rw [abs_of_nonpos (by linarith), min_eq_left (by linarith)]
    ring
  · rw [abs_of_nonneg (by linarith), min_eq_right (by linarith)]
    ring

/-- The radius minus the Euclidean distance of `x` to the moving centre `g + (lo + hi)/2` is the
distance of the coordinate `x 0 - g 0` to the endpoints. -/
theorem intervalRadius_sub_norm_eq (lo hi : ℝ) (x g : PDE.Vec 1) :
    (hi - lo) / 2 - PDE.vecEuclideanNorm (x - (g + intervalCentre lo hi)) =
      intervalLateralDist lo hi (x 0 - g 0) := by
  rw [vecEuclideanNorm_vec_one, intervalLateralDist_eq]
  have : (x - (g + intervalCentre lo hi)) 0 = x 0 - g 0 - (lo + hi) / 2 := by
    simp [intervalCentre]
    ring
  rw [this]

/-- A bounded interval is a Euclidean ball in `Vec 1`. -/
theorem oneDimensionalAxisBox_eq_euclideanBall {lo hi : ℝ} (hlohi : lo < hi) :
    PDE.oneDimensionalAxisBox lo hi =
      PDE.euclideanBall (intervalCentre lo hi) ((hi - lo) / 2) := by
  ext x
  rw [PDE.mem_oneDimensionalAxisBox_iff,
    PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by linarith), vecEuclideanNorm_vec_one]
  simp only [PDE.vecOneCoordinate, Pi.sub_apply, intervalCentre, mem_Ioo]
  rw [abs_lt]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- An admissible evolution domain is `ℝ^d` or a Euclidean ball: the bounded-interval case
`d = 1` is a ball. -/
theorem eq_univ_or_exists_euclideanBall_of_isAdmissibleEvolutionDomain {n : ℕ}
    {Ω : Set (PDE.Vec n)} (hΩ : IsAdmissibleEvolutionDomain Ω) :
    Ω = Set.univ ∨ ∃ (c : PDE.Vec n) (r : ℝ), 0 < r ∧ Ω = PDE.euclideanBall c r := by
  rcases hΩ with h | h | ⟨hn, lo, hi, hlohi, h⟩
  · exact Or.inl h
  · exact Or.inr h
  · cases hn
    have h' : Ω = PDE.oneDimensionalAxisBox lo hi := by simpa using h
    exact Or.inr ⟨intervalCentre lo hi, (hi - lo) / 2, by linarith,
      h'.trans (oneDimensionalAxisBox_eq_euclideanBall hlohi)⟩

end HypoellipticAleksandrov.KineticAleksandrov

end

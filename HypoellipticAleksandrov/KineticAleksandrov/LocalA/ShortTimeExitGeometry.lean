module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.Geometry
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic

/-! # The coordinate distance from an interior velocity to the lateral sphere -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open HypoellipticAleksandrov Set

/-- Lateral velocities are at Euclidean distance at least one quarter radius
from every velocity in the inner three-quarter ball. -/
theorem ballExit_lateral_distance {d : ℕ} {R : ℝ} (hR : 0 < R)
    (v₀ v w : PDE.Vec d) (hv : v ∈ PDE.euclideanBall v₀ (3 * R / 4))
    (hw : w ∈ frontier (PDE.euclideanBall v₀ R)) :
    R / 4 ≤ PDE.vecEuclideanNorm (w - v) := by
  have hvn := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).mp hv
  have hwn : R ≤ PDE.vecEuclideanNorm (w - v₀) := by
    apply le_of_not_gt
    intro h
    rw [(PDE.isOpen_euclideanBall v₀ R).frontier_eq] at hw
    exact hw.2 ((PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR).mpr h)
  have ht := PDE.vecEuclideanNorm_add_le (w - v) (v - v₀)
  rw [sub_add_sub_cancel] at ht
  linarith only [hvn, hwn, ht]

/-- Some signed coordinate accounts for the Euclidean lateral distance. -/
theorem ballExit_lateral_coordinate {d : ℕ} (hd : 1 ≤ d) {R : ℝ} (hR : 0 < R)
    (v₀ v w : PDE.Vec d) (hv : v ∈ PDE.euclideanBall v₀ (3 * R / 4))
    (hw : w ∈ frontier (PDE.euclideanBall v₀ R)) :
    ∃ i : Fin d, R / (4 * Real.sqrt d) ≤ |w i - v i| := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdR
  have hδ : 0 < R / (4 * Real.sqrt d) := div_pos hR (by positivity)
  by_contra h
  push Not at h
  have hn : ‖w - v‖ < R / (4 * Real.sqrt d) := by
    apply (pi_norm_lt_iff hδ).mpr
    intro i
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using h i
  have he := PDE.vecEuclideanNorm_le_sqrt_natCast_mul_norm (w - v)
  have hm := mul_lt_mul_of_pos_left hn hs
  have hc : Real.sqrt d * (R / (4 * Real.sqrt d)) = R / 4 := by
    field_simp
  rw [hc] at hm
  exact (not_lt_of_ge (ballExit_lateral_distance hR v₀ v w hv hw)) (he.trans_lt hm)

end HypoellipticAleksandrov.KineticAleksandrov.LocalA

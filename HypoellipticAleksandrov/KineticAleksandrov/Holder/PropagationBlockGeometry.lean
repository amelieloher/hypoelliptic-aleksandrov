module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.PropagationParametersBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometryTopology
import PDEFoundation.Geometry.EuclideanBall.Topology
import Mathlib.Tactic

/-! # Weak coordinate bounds on source backward-cylinder closures -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set

/-- The closure has precisely the weak time and Euclidean radius bounds needed for blocks. -/
theorem closure_backwardCylinder_bounds {d : ℕ} (P₀ : KineticPoint d) {R : ℝ}
    (hR : 0 < R) :
    closure (backwardCylinder P₀ R) ⊆
      {P | P₀.time - R ^ 2 ≤ P.time ∧ P.time ≤ P₀.time ∧
        PDE.vecEuclideanNorm (P.velocity - P₀.velocity) ≤ R ∧
        PDE.vecEuclideanNorm (relativePosition P₀ P) ≤ R ^ 3} := by
  have hx : Continuous (relativePosition P₀) := by
    unfold relativePosition
    exact (continuous_position.sub continuous_const).sub
      ((continuous_time.sub continuous_const).smul continuous_const)
  have hv : Continuous (fun P : KineticPoint d => P.velocity - P₀.velocity) :=
    continuous_velocity.sub continuous_const
  apply closure_minimal
  · intro P hP
    refine ⟨hP.1.le, hP.2.1.le, ?_, ?_⟩
    · exact ((PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR).mp hP.2.2.1).le
    · have he := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (pow_pos hR 3)).mp hP.2.2.2
      simpa only [sub_zero] using he.le
  · exact (isClosed_le continuous_const continuous_time).inter
      ((isClosed_le continuous_time continuous_const).inter
        ((isClosed_le (PDE.continuous_vecEuclideanNorm.comp hv) continuous_const).inter
          (isClosed_le (PDE.continuous_vecEuclideanNorm.comp hx) continuous_const)))

/-- The block radius has its literal source time scale. -/
theorem propagation_block_radius_sq {h W : ℝ} (hh : 0 ≤ h) :
    (W * Real.sqrt h) ^ 2 = W ^ 2 * h := by rw [mul_pow, Real.sq_sqrt hh]

/-- The block radius has its literal source position scale. -/
theorem propagation_block_radius_cube {h W : ℝ} (hh : 0 ≤ h) :
    (W * Real.sqrt h) ^ 3 = W ^ 3 * h ^ (3 / 2 : ℝ) := by
  rw [mul_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast (h ^ (1 / 2 : ℝ)) 3,
    ← Real.rpow_mul hh]
  norm_num

end HypoellipticAleksandrov.KineticAleksandrov.Holder

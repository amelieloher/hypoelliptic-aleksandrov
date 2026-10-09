module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.HolderDistance

/-! # Common cylinders for close pairs, with no top-time dependence -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Set
open KineticAleksandrov.LocalA

/-- A ball closure retains its Euclidean norm bound. -/
theorem norm_sub_le_of_mem_ball_closure {N : ℕ} (v : PDE.Vec N) {r : ℝ}
    (hr : 0 < r) {y : PDE.Vec N} (hy : y ∈ closure (PDE.euclideanBall v r)) :
    PDE.vecEuclideanNorm (y - v) ≤ r := by
  have hc : IsClosed {y : PDE.Vec N | PDE.vecEuclideanNorm (y - v) ≤ r} :=
    isClosed_le (PDE.continuous_vecEuclideanNorm.comp (continuous_id.sub continuous_const))
      continuous_const
  exact closure_minimal (fun y hy =>
    ((PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr).mp hy).le) hc hy

/-- The fixed-radius common cylinder remains inside the outer source cylinder. -/
theorem pair_base_closed_cylinder_subset {N : ℕ} {z : TimeVelocity N}
    (hz : z ∈ scalarParabolicOpenCylinder (-1 / 4) 0
      (PDE.euclideanBall 0 (1 / 2 : ℝ))) {T : ℝ} (hzt : z.1 < T) (hT : T < 0) :
    scalarParabolicClosedCylinder (T - (1 / 8 : ℝ) ^ 2) T
      (PDE.euclideanBall z.2 (1 / 8 : ℝ)) ⊆
    scalarParabolicOpenCylinder (-9 / 16) 0 (PDE.euclideanBall 0 (3 / 4 : ℝ)) := by
  intro y hy
  constructor
  · constructor <;> linarith only [hy.1.1, hy.1.2, hz.1.1, hzt, hT]
  · rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)]
    have hcenter := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
      (by norm_num : (0 : ℝ) < 1 / 2)).mp hz.2
    have hdiff := norm_sub_le_of_mem_ball_closure z.2
      (by norm_num : (0 : ℝ) < 1 / 8) hy.2
    have htri := PDE.vecEuclideanNorm_add_le (y.2 - z.2) z.2
    rw [sub_add_cancel] at htri
    simp only [sub_zero] at hcenter ⊢
    linarith only [hcenter, hdiff, htri]

/-- Both points fit in a common cylinder of radius at least twice their distance. -/
theorem pair_mem_common_backward_cylinder {N : ℕ} {z z' : TimeVelocity N}
    (hne : z ≠ z') {T r : ℝ} (hT : max z.1 z'.1 < T)
    (hmargin : T - max z.1 z'.1 ≤ parabolicDistance z z' ^ 2)
    (hr : 2 * parabolicDistance z z' ≤ r) :
    z ∈ scalarParabolicOpenCylinder (T - r ^ 2) T (PDE.euclideanBall z.2 r) ∧
    z' ∈ scalarParabolicOpenCylinder (T - r ^ 2) T (PDE.euclideanBall z.2 r) := by
  let δ := parabolicDistance z z'
  have hδ : 0 < δ := parabolicDistance_pos hne
  have hrpos : 0 < r := (mul_pos (by norm_num) hδ).trans_le hr
  have ht := abs_time_sub_le_parabolicDistance_sq z z'
  have hd := abs_le.mp ht
  have hdiff : max z.1 z'.1 - z.1 ≤ δ ^ 2 := by
    rcases le_total z.1 z'.1 with h | h
    · rw [max_eq_right h]
      linarith only [hd.1]
    · rw [max_eq_left h, sub_self]
      exact sq_nonneg δ
  have hdiff' : max z.1 z'.1 - z'.1 ≤ δ ^ 2 := by
    rcases le_total z.1 z'.1 with h | h
    · rw [max_eq_right h, sub_self]
      exact sq_nonneg δ
    · rw [max_eq_left h]
      exact hd.2
  have hsq : 2 * δ ^ 2 < r ^ 2 := by
    nlinarith only [hr, hδ, sq_nonneg (r - 2 * δ)]
  have hzt : z.1 < T := (le_max_left _ _).trans_lt hT
  have hz't : z'.1 < T := (le_max_right _ _).trans_lt hT
  constructor
  · constructor
    · constructor
      · linarith only [hmargin, hdiff, hsq]
      · exact hzt
    · rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hrpos, sub_self]
      simpa [PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot] using hrpos
  · constructor
    · constructor
      · linarith only [hmargin, hdiff', hsq]
      · exact hz't
    · rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hrpos,
        PDE.vecEuclideanNorm_sub_comm]
      have hv := velocity_sub_le_parabolicDistance z z'
      exact hv.trans_lt (by linarith only [hr, hδ])

end HypoellipticAleksandrov.Parabolic.LocalHolder

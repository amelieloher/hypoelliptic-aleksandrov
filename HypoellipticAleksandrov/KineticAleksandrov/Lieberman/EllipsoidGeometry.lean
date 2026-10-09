module

public import HypoellipticAleksandrov.KineticAleksandrov.EllipsoidDirichlet
public import HypoellipticAleksandrov.Parabolic.ScalarDirichletGeometry
import PDEFoundation.Geometry.EuclideanBall.Topology
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

/-! # Geometry and compact-cylinder drift bounds for the literal ellipsoid -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Lieberman
open HypoellipticAleksandrov Parabolic Set
open scoped Matrix Topology BigOperators

private theorem quadratic_continuous {d : ℕ} (Q : PDE.Mat d) :
    Continuous (fun x => PDE.vecDot x (Q *ᵥ x)) := by
  unfold PDE.vecDot Matrix.mulVec dotProduct
  fun_prop

private theorem quadratic_smul {d : ℕ} (Q : PDE.Mat d) (c : ℝ) (x : PDE.Vec d) :
    PDE.vecDot (c • x) (Q *ᵥ (c • x)) = c ^ 2 * PDE.vecDot x (Q *ᵥ x) := by
  simp only [Matrix.mulVec_smul, PDE.vecDot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem quadratic_nonneg {d : ℕ} {Q : PDE.Mat d} (hQ : Q.PosDef)
    (x : PDE.Vec d) : 0 ≤ PDE.vecDot x (Q *ᵥ x) := by
  simpa only [PDE.vecDot, dotProduct, star_trivial] using
    hQ.posSemidef.dotProduct_mulVec_nonneg x

/-- Every literal open ellipsoid is open, without a definiteness assumption. -/
theorem isOpen_openEllipsoid {d : ℕ} (Q : PDE.Mat d) : IsOpen (openEllipsoid Q) :=
  isOpen_lt (quadratic_continuous Q) continuous_const

private theorem ellipsoid_bounded {d : ℕ} {Q : PDE.Mat d} (hQ : Q.PosDef) :
    Bornology.IsBounded (openEllipsoid Q) := by
  obtain ⟨m, hm, hmin⟩ := (isCompact_sphere (0 : PDE.Vec d) 1).exists_forall_le'
    (quadratic_continuous Q).continuousOn (a := 0) (by
      intro x hx
      have hxne : x ≠ 0 := by
        intro he
        simp [he] at hx
      simpa only [PDE.vecDot, dotProduct, star_trivial] using
        hQ.dotProduct_mulVec_pos hxne)
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨1 + 1 / m, ?_⟩
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    simp only [norm_zero]
    positivity
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hs : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : PDE.Vec d) 1 := by
    simp [norm_smul, hn.ne']
  have hh := hmin _ hs
  rw [quadratic_smul] at hh
  have hmul : m * ‖x‖ ^ 2 ≤ PDE.vecDot x (Q *ᵥ x) := by
    have hh' := mul_le_mul_of_nonneg_right hh (sq_nonneg ‖x‖)
    field_simp at hh'
    exact hh'
  have hq : PDE.vecDot x (Q *ᵥ x) < 1 := hx
  have hmdiv : m * (1 / m) = 1 := mul_one_div_cancel hm.ne'
  have hdiv : 0 < 1 / m := one_div_pos.mpr hm
  nlinarith only [hm, hn, hmul, hq, hmdiv, hdiv, sq_nonneg (‖x‖ - 1)]

private theorem ellipsoid_closure {d : ℕ} {Q : PDE.Mat d} (_hQ : Q.PosDef) :
    closure (openEllipsoid Q) = {x | PDE.vecDot x (Q *ᵥ x) ≤ 1} := by
  apply subset_antisymm
  · exact closure_lt_subset_le (quadratic_continuous Q) continuous_const
  · intro x hx
    have hc : Continuous (fun c : ℝ => c • x) := continuous_id.smul continuous_const
    have him : (fun c : ℝ => c • x) '' Ioo 0 1 ⊆ openEllipsoid Q := by
      rintro y ⟨c, hc', rfl⟩
      change PDE.vecDot (c • x) (Q *ᵥ (c • x)) < 1
      rw [quadratic_smul]
      have hc2 : c ^ 2 < 1 := by nlinarith only [hc'.1, hc'.2]
      exact lt_of_le_of_lt
        (mul_le_mul_of_nonneg_left hx (sq_nonneg c)) (by simpa using hc2)
    have h1 : (1 : ℝ) ∈ closure (Ioo (0 : ℝ) 1) := by
      rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
      exact ⟨by norm_num, le_rfl⟩
    have hh := image_closure_subset_closure_image hc (mem_image_of_mem _ h1)
    have ht := closure_mono him hh
    simpa only [one_smul] using ht

private theorem quadratic_add {d : ℕ} {Q : PDE.Mat d} (hQ : Q.IsSymm)
    (x y : PDE.Vec d) :
    PDE.vecDot (x + y) (Q *ᵥ (x + y)) = PDE.vecDot x (Q *ᵥ x) +
      2 * PDE.vecDot y (Q *ᵥ x) + PDE.vecDot y (Q *ᵥ y) := by
  change (x + y) ⬝ᵥ (Q *ᵥ (x + y)) = x ⬝ᵥ (Q *ᵥ x) +
    2 * (y ⬝ᵥ (Q *ᵥ x)) + y ⬝ᵥ (Q *ᵥ y)
  rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add,
    hQ.dotProduct_mulVec_comm (x := x) (y := y)]
  ring

/-- Positive-definite ellipsoids have bounded closure and Euclidean exterior cones. -/
theorem openEllipsoid_geometry {d : ℕ} {Q : PDE.Mat d} (hQ : Q.PosDef) :
    Bornology.IsBounded (openEllipsoid Q) ∧
    closure (openEllipsoid Q) = {x | PDE.vecDot x (Q *ᵥ x) ≤ 1} ∧
    frontier (openEllipsoid Q) = {x | PDE.vecDot x (Q *ᵥ x) = 1} ∧
    HasUniformNondegenerateExteriorCone (openEllipsoid Q) := by
  have hcl := ellipsoid_closure hQ
  have hf : frontier (openEllipsoid Q) = {x | PDE.vecDot x (Q *ᵥ x) = 1} := by
    rw [(isOpen_openEllipsoid Q).frontier_eq, hcl]
    ext x
    change (_ ≤ 1 ∧ ¬ _ < 1) ↔ _ = 1
    exact ⟨fun h => le_antisymm h.1 (not_lt.mp h.2), fun h => by simp [h]⟩
  refine ⟨ellipsoid_bounded hQ, hcl, hf, 1, 1 / 2, by norm_num, by norm_num,
    by norm_num, ?_⟩
  intro y hy
  have hyq : PDE.vecDot y (Q *ᵥ y) = 1 := by rwa [hf] at hy
  have hyp : Q *ᵥ y ≠ 0 := by
    intro hp
    have hy0 : y = 0 := hQ.mulVec_injective (hp.trans (Matrix.mulVec_zero Q).symm)
    simp [hy0, PDE.vecDot] at hyq
  have hn := PDE.vecEuclideanNorm_pos_iff.mpr hyp
  let ν := (PDE.vecEuclideanNorm (Q *ᵥ y))⁻¹ • (Q *ᵥ y)
  refine ⟨ν, ?_, ?_⟩
  · rw [PDE.vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  · intro z hz _hr hangle
    have hdot : PDE.vecDot z ν =
        (PDE.vecEuclideanNorm (Q *ᵥ y))⁻¹ * PDE.vecDot z (Q *ᵥ y) := by
      simp only [ν, PDE.vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hdot] at hangle
    have hpos : 0 < PDE.vecDot z (Q *ᵥ y) := by
      have hh : 0 < (PDE.vecEuclideanNorm (Q *ᵥ y))⁻¹ *
          PDE.vecDot z (Q *ᵥ y) := lt_of_lt_of_le (by positivity) hangle
      exact (mul_pos_iff_of_pos_left (inv_pos.mpr hn)).mp hh
    change ¬ PDE.vecDot (y + z) (Q *ᵥ (y + z)) < 1
    rw [quadratic_add hQ.isHermitian.isSymm, hyq]
    have hzq := quadratic_nonneg hQ z
    linarith only [hpos, hzq]

/-- A continuous drift is Euclidean-bounded on every bounded closed spatial cylinder. -/
theorem exists_closedCylinder_drift_bound {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : Bornology.IsBounded Ω) (a T : ℝ) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (hb : Continuous (fun z : TimeVelocity d => b z.1 z.2)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ scalarParabolicClosedCylinder a T Ω,
      PDE.vecEuclideanNorm (b z.1 z.2) ≤ B := by
  have hK : IsCompact (scalarParabolicClosedCylinder a T Ω) :=
    isCompact_Icc.prod hΩ.isCompact_closure
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    (PDE.continuous_vecEuclideanNorm.comp hb).continuousOn
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro z hz
  exact (le_abs_self _).trans ((hB z hz).trans (le_max_left _ _))

end HypoellipticAleksandrov.KineticAleksandrov.Lieberman

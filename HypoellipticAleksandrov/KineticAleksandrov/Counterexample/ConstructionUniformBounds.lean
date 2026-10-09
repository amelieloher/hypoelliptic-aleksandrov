module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionSecondBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.BarrierPackedJets

/-! # Uniform bounds on raw selected jets over compact time intervals -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Set

/-- Continuous scalar functions are bounded on any compact carrier. -/
theorem construction_compact_scalar_bound {X : Type*} [TopologicalSpace X]
    (K : Set X) (hK : IsCompact K) (f : X → ℝ) (hf : Continuous f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, |f x| ≤ C := by
  obtain ⟨C, hb⟩ := hK.bddAbove_image hf.abs.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun x hx =>
    (hb ⟨x, hx, rfl⟩).trans (le_max_left _ _)⟩

/-- Uniform scalar bounds are preserved by subtraction. -/
theorem construction_scalar_bound_sub {X : Type*} (K : Set X) (f g : X → ℝ)
    (hf : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, |f x| ≤ C)
    (hg : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, |g x| ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, |f x - g x| ≤ C := by
  obtain ⟨C, hC, hf⟩ := hf
  obtain ⟨D, hD, hg⟩ := hg
  exact ⟨C + D, add_nonneg hC hD, fun x hx =>
    (abs_sub _ _).trans (add_le_add (hf x hx) (hg x hx))⟩

/-- Uniform scalar bounds are preserved by multiplication. -/
theorem construction_scalar_bound_mul {X : Type*} (K : Set X) (f g : X → ℝ)
    (hf : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, |f x| ≤ C)
    (hg : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, |g x| ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, |f x * g x| ≤ C := by
  obtain ⟨C, hC, hf⟩ := hf
  obtain ⟨D, hD, hg⟩ := hg
  refine ⟨C * D, mul_nonneg hC hD, fun x hx => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hf x hx) (hg x hx) (abs_nonneg _) hC

/-- Uniform scalar bounds are preserved by addition. -/
theorem construction_scalar_bound_add {X : Type*} (K : Set X) (f g : X → ℝ)
    (hf : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, |f x| ≤ C)
    (hg : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, |g x| ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, |f x + g x| ≤ C := by
  obtain ⟨C, hC, hf⟩ := hf
  obtain ⟨D, hD, hg⟩ := hg
  exact ⟨C + D, add_nonneg hC hD, fun x hx =>
    (abs_add_le _ _).trans (add_le_add (hf x hx) (hg x hx))⟩

/-- The packed barrier gradient depends continuously on time and space together. -/
theorem construction_barrier_gradient_joint_continuous (d : ℕ) (mu R : ℝ)
    (i : Fin (d + d)) : Continuous (fun z : ℝ × PDE.Vec (d + d) =>
      PDE.classicalGradient (spatialPackedBarrier d mu R z.1) z.2 i) := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [spatialPackedBarrier_positionGradient]
    exact continuous_const
  · simp only [spatialPackedBarrier_velocityGradient]
    exact (((continuous_const.mul (continuous_const.mul continuous_fst).rexp).div_const
      (R ^ 2)).neg).mul
      ((continuous_apply j).comp ((spatialCoordinateCLE d).continuous.comp
        continuous_snd).snd)

/-- The packed barrier Hessian is jointly continuous. -/
theorem construction_barrier_hessian_joint_continuous (d : ℕ) (mu R : ℝ)
    (i k : Fin d) : Continuous (fun z : ℝ × PDE.Vec (d + d) =>
      PDE.classicalGradient (fun y => PDE.classicalGradient
        (spatialPackedBarrier d mu R z.1) y (Fin.natAdd d k)) z.2 (Fin.natAdd d i)) := by
  simp only [spatialPackedBarrier_velocityHessian]
  exact (((continuous_const.mul (continuous_const.mul continuous_fst).rexp).div_const
    (R ^ 2)).neg).mul continuous_const

/-- First raw representatives have bounds uniform over both compact time and compact space. -/
theorem construction_rawGradient_uniform_bound {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r) (mu R a b : ℝ)
    (K : Set (PDE.Vec (d + d))) (hK : IsCompact K) (i : Fin (d + d)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b, ∀ x ∈ K,
      |spatialPackedCutoffGradient h r mu R t x i| ≤ C := by
  let D := Icc a b ×ˢ K
  have hD : IsCompact D := isCompact_Icc.prod hK
  obtain ⟨C, hC, hb⟩ := construction_packedGradient_compact_bound h r hr i K hK
  have hf : ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ D,
      |spatialPackedGradient (flatProfilePositionJet h r)
        (flatProfileVelocityJet h r) z.2 i| ≤ C :=
    ⟨C, hC, fun z hz => hb z.2 hz.2⟩
  have hg := construction_compact_scalar_bound D hD _
    (construction_barrier_gradient_joint_continuous d mu R i)
  obtain ⟨N, hN, hbN⟩ := construction_scalar_bound_sub D _ _ hf hg
  refine ⟨N, hN, fun t ht x hx => ?_⟩
  have htheta := timeCutoffTheta_deriv_bounds
    (selectedFlatProfile h r (spatialCoordinateCLE d x) - spatialPackedBarrier d mu R t x)
  rw [spatialPackedCutoffGradient, abs_mul, abs_of_nonneg htheta.1]
  exact (mul_le_mul_of_nonneg_right htheta.2 (abs_nonneg _)).trans
    (by simpa only [one_mul] using hbN (t, x) ⟨ht, hx⟩)

/-- Second raw representatives have bounds uniform over compact time and compact space. -/
theorem construction_rawHessian_uniform_bound {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r) (mu R a b : ℝ)
    (K : Set (PDE.Vec (d + d))) (hK : IsCompact K) (i k : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b, ∀ x ∈ K,
      |spatialPackedCutoffVelocityHessian h r mu R t x i k| ≤ C := by
  let D := Icc a b ×ˢ K
  have hD : IsCompact D := isCompact_Icc.prod hK
  obtain ⟨M, hM, hbM⟩ := flatProfile_jets_compact_bound_of_profile h r hr
    ((spatialCoordinateCLE d) '' K) (hK.image (spatialCoordinateCLE d).continuous)
  have hh : ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ D,
      |flatProfileHessian h r (spatialCoordinateCLE d z.2) i k| ≤ C :=
    ⟨M, hM, fun z hz => (hbM _ ⟨z.2, hz.2, rfl⟩).2.2 i k⟩
  have hg (j : Fin d) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ D,
      |flatProfileVelocityJet h r (spatialCoordinateCLE d z.2) j -
        PDE.classicalGradient (spatialPackedBarrier d mu R z.1) z.2 (Fin.natAdd d j)|
        ≤ C := by
    have hf : ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ D,
        |flatProfileVelocityJet h r (spatialCoordinateCLE d z.2) j| ≤ C :=
      ⟨M, hM, fun z hz => by
        simpa only [Real.norm_eq_abs] using
          (norm_le_pi_norm _ j).trans (hbM _ ⟨z.2, hz.2, rfl⟩).2.1⟩
    exact construction_scalar_bound_sub D _ _ hf
      (construction_compact_scalar_bound D hD _
        (construction_barrier_gradient_joint_continuous d mu R (Fin.natAdd d j)))
  obtain ⟨N, hN, hbN⟩ := construction_scalar_bound_sub D _ _ hh
    (construction_compact_scalar_bound D hD _
      (construction_barrier_hessian_joint_continuous d mu R i k))
  obtain ⟨C, hC, hbC⟩ := construction_scalar_bound_mul D _ _ (hg i) (hg k)
  obtain ⟨L, hL, hbL⟩ := timeCutoffTheta_deriv2_abs_bound
  refine ⟨N + L * C, add_nonneg hN (mul_nonneg hL.le hC), fun t ht x hx => ?_⟩
  have htheta := timeCutoffTheta_deriv_bounds
    (selectedFlatProfile h r (spatialCoordinateCLE d x) - spatialPackedBarrier d mu R t x)
  unfold spatialPackedCutoffVelocityHessian
  apply (abs_add_le _ _).trans
  apply add_le_add
  · rw [abs_mul, abs_of_nonneg htheta.1]
    exact (mul_le_mul_of_nonneg_right htheta.2 (abs_nonneg _)).trans
      (by simpa only [one_mul] using hbN (t, x) ⟨ht, hx⟩)
  · rw [mul_assoc, abs_mul]
    exact mul_le_mul (hbL _) (hbC (t, x) ⟨ht, hx⟩) (abs_nonneg _) hL.le

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

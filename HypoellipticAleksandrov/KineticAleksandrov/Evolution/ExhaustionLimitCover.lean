module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitGeometry

/-! # Inner cylinders cover the diffused interior, including time faces -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov Set Filter
open scoped Topology

/-- Membership in a moving ball is measured by the explicit Euclidean norm. -/
theorem mem_movingBall_iff_norm_lt {n : ℕ} {Γ : ℝ → PDE.Vec n} {r σ : ℝ}
    (hr : 0 < r) {y : PDE.Vec n} :
    y ∈ movingDomain (PDE.euclideanBall 0 r) Γ σ ↔
      PDE.vecEuclideanNorm (y - Γ σ) < r := by
  rw [mem_movingDomain_iff, PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr, sub_zero]

/-- A point in a closed moving ball has distance at most its Euclidean radius. -/
theorem norm_le_of_mem_closure_movingBall {n : ℕ} {Γ : ℝ → PDE.Vec n} {r σ : ℝ}
    (hr : 0 < r) {y : PDE.Vec n}
    (hy : y ∈ closure (movingDomain (PDE.euclideanBall 0 r) Γ σ)) :
    PDE.vecEuclideanNorm (y - Γ σ) ≤ r := by
  apply Real.sqrt_le_iff.mpr
  exact ⟨hr.le, by simpa only [add_zero] using vecNormSq_le_of_mem_closure_movingDomain hy⟩

/-- Every point of a closed strict inner cylinder lies in the original diffused interior. -/
theorem innerClosedCylinder_subset_movingBall {n : ℕ} {Γ : ℝ → PDE.Vec n}
    {r0 δ α τ S : ℝ} (hδ : 0 < δ) (hδr : δ < r0) :
    movingClosedSlab (PDE.euclideanBall 0 (r0 - δ)) Γ α τ ∩
      {p | radialSq p ≤ S ^ 2} ⊆
      {p | p.position ∈ movingDomain (PDE.euclideanBall 0 r0) Γ p.time} := by
  intro p hp
  apply (mem_movingBall_iff_norm_lt (by linarith : 0 < r0)).mpr
  exact (norm_le_of_mem_closure_movingBall (sub_pos.mpr hδr) hp.1.2.2).trans_lt
    (by linarith)

/-- Strict inner cylinders cover every point of the strict original moving interior. -/
theorem exists_boundedInnerOpenCylinder_mem {n : ℕ} {Γ : ℝ → PDE.Vec n}
    {r0 α τ : ℝ} (hr0 : 0 < r0) {p : KineticPoint n}
    (ht : α < p.time ∧ p.time < τ)
    (hi : p.position ∈ movingDomain (PDE.euclideanBall 0 r0) Γ p.time) :
    ∃ δ S : ℝ, 0 < δ ∧ δ < r0 ∧
      p ∈ boundedInnerOpenCylinder (r0 - δ) Γ α τ S := by
  let np := PDE.vecEuclideanNorm (p.position - Γ p.time)
  let δ := (r0 - np) / 2
  let S := radialSq p + 1
  have hnp : np < r0 := (mem_movingBall_iff_norm_lt hr0).mp hi
  have hnp0 : 0 ≤ np := PDE.vecEuclideanNorm_nonneg _
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδr : δ < r0 := by dsimp [δ]; linarith
  have hpr : np < r0 - δ := by dsimp [δ]; linarith
  have hrad0 : 0 ≤ radialSq p :=
    add_nonneg (PDE.vecNormSq_nonneg _) (PDE.vecNormSq_nonneg _)
  refine ⟨δ, S, hδ, hδr, ht.1, ht.2,
    (mem_movingBall_iff_norm_lt (sub_pos.mpr hδr)).mpr hpr, ?_⟩
  dsimp [S]
  nlinarith

/-- Fixed closed inner cylinders form relative neighbourhoods of every point in the
original diffused interior, including the two closed time faces. -/
theorem exists_innerClosedCylinder_mem_nhdsWithin {n : ℕ} {Γ : ℝ → PDE.Vec n}
    (hΓ : Continuous Γ) {r0 α τ : ℝ} (hr0 : 0 < r0) {p : KineticPoint n}
    (hp : p ∈ movingClosedSlab (PDE.euclideanBall 0 r0) Γ α τ)
    (hi : p.position ∈ movingDomain (PDE.euclideanBall 0 r0) Γ p.time) :
    ∃ δ S : ℝ, 0 < δ ∧ δ < r0 ∧
      p ∈ movingClosedSlab (PDE.euclideanBall 0 (r0 - δ)) Γ α τ ∩
        {q | radialSq q ≤ S ^ 2} ∧
      (movingClosedSlab (PDE.euclideanBall 0 (r0 - δ)) Γ α τ ∩
        {q | radialSq q ≤ S ^ 2}) ∈
        𝓝[movingClosedSlab (PDE.euclideanBall 0 r0) Γ α τ] p := by
  let np := PDE.vecEuclideanNorm (p.position - Γ p.time)
  let δ := (r0 - np) / 2
  let S := radialSq p + 1
  have hnp : np < r0 := (mem_movingBall_iff_norm_lt hr0).mp hi
  have hnp0 : 0 ≤ np := PDE.vecEuclideanNorm_nonneg _
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδr : δ < r0 := by dsimp [δ]; linarith
  have hpr : np < r0 - δ := by dsimp [δ]; linarith
  have hr : 0 < r0 - δ := sub_pos.mpr hδr
  have hrad0 : 0 ≤ radialSq p :=
    add_nonneg (PDE.vecNormSq_nonneg _) (PDE.vecNormSq_nonneg _)
  have hrad : radialSq p < S ^ 2 := by dsimp [S]; nlinarith
  have hnc : Continuous (fun q : KineticPoint n =>
      PDE.vecEuclideanNorm (q.position - Γ q.time)) :=
    PDE.continuous_vecEuclideanNorm.comp (continuous_position.sub (hΓ.comp continuous_time))
  refine ⟨δ, S, hδ, hδr, ⟨⟨hp.1, hp.2.1,
    subset_closure ((mem_movingBall_iff_norm_lt hr).mpr hpr)⟩, hrad.le⟩, ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    (hnc.continuousAt.eventually (gt_mem_nhds hpr)).filter_mono nhdsWithin_le_nhds,
    (continuous_radialSq.continuousAt.eventually (gt_mem_nhds hrad)).filter_mono
      nhdsWithin_le_nhds] with q hq hnq hrq
  exact ⟨⟨hq.1, hq.2.1,
    subset_closure ((mem_movingBall_iff_norm_lt hr).mpr hnq)⟩, hrq.le⟩

end HypoellipticAleksandrov.KineticAleksandrov

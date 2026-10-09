module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.InnerCylinderGeometry
public import Mathlib.Topology.Algebra.ConstMulAction

/-! # Affine inner-cylinder maps and boundary surjectivity -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set

/-- The retraction has exactly the source formula on relative coordinates. -/
theorem innerRetraction_relative {d : ℕ} (Z₀ P : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (δ : ℝ) (hδ0 : 0 < δ) (hδlt : δ < R ^ 2 / 2) :
    let ρ := innerRatio R hR δ hδ0 hδlt
    let Q := innerRetraction Z₀ R hR δ hδ0 hδlt P
    Q.time = Z₀.time + δ + ρ ^ 2 * (P.time - Z₀.time) ∧
      relativePosition Z₀ Q = ρ ^ 3 • relativePosition Z₀ P ∧
      relativeVelocity Z₀ Q = ρ • relativeVelocity Z₀ P := by
  dsimp only
  refine ⟨rfl,?_,?_⟩
  · ext i
    simp [relativePosition, innerRetraction]
    ring
  · ext i
    simp [relativeVelocity, innerRetraction]

/-- The affine inner map as a homeomorphism, with an explicit positive-scaling inverse. -/
def innerRetractionHomeomorph {d : ℕ} (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (δ : ℝ) (hδ0 : 0 < δ) (hδlt : δ < R ^ 2 / 2) : KineticPoint d ≃ₜ KineticPoint d :=
  let ρ := innerRatio R hR δ hδ0 hδlt
  let hρ := (innerRatio_spec R hR δ hδ0 hδlt).1.ne'
  let ht := ((Homeomorph.subRight Z₀.time).trans
    (Homeomorph.mulLeft₀ (ρ^2) (pow_ne_zero 2 hρ))).trans
      (Homeomorph.addLeft (Z₀.time+δ))
  let hx := Homeomorph.smulOfNeZero (ρ^3) (pow_ne_zero 3 hρ) (α := PDE.Vec d)
  let hv := Homeomorph.smulOfNeZero ρ hρ (α := PDE.Vec d)
  ((relativeHomeomorph Z₀).trans (ht.prodCongr (hx.prodCongr hv))).trans
    (relativeHomeomorph Z₀).symm

/-- The homeomorphism implements the literal physical-coordinate retraction. -/
theorem innerRetractionHomeomorph_apply {d : ℕ}
    (Z₀ P : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (δ : ℝ) (hδ0 : 0 < δ) (hδlt : δ < R ^ 2 / 2) :
    innerRetractionHomeomorph Z₀ R hR δ hδ0 hδlt P =
      innerRetraction Z₀ R hR δ hδ0 hδlt P := rfl

private theorem smul_ball_iff {d : ℕ} (x : PDE.Vec d) (a r : ℝ) (ha : 0 < a) :
    a • x ∈ PDE.euclideanBall 0 (a*r) ↔ x ∈ PDE.euclideanBall 0 r := by
  change PDE.vecNormSq (a • x - 0) < (a*r)^2 ↔ PDE.vecNormSq (x-0) < r^2
  simp only [sub_zero, PDE.vecNormSq_smul, mul_pow]
  exact mul_lt_mul_iff_right₀ (sq_pos_of_pos ha)

private theorem smul_sphere_iff {d : ℕ} (x : PDE.Vec d) (a r : ℝ) (ha : 0 < a) :
    a • x ∈ PDE.euclideanSphere 0 (a*r) ↔ x ∈ PDE.euclideanSphere 0 r := by
  change PDE.vecNormSq (a • x - 0) = (a*r)^2 ↔ PDE.vecNormSq (x-0) = r^2
  simp only [sub_zero, PDE.vecNormSq_smul, mul_pow]
  constructor
  · exact mul_left_cancel₀ (ne_of_gt (sq_pos_of_pos ha))
  · intro h
    rw [h]

private theorem retraction_mem_inner_iff {d : ℕ}
    (Z₀ P : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (δ : ℝ) (hδ0 : 0 < δ) (hδlt : δ < R ^ 2 / 2) :
    innerRetraction Z₀ R hR δ hδ0 hδlt P ∈ innerCylinder Z₀ R hR δ hδ0 hδlt ↔
      P ∈ forwardCylinder Z₀ R hR := by
  obtain ⟨hρ,_,hs⟩ := innerRatio_spec R hR δ hδ0 hδlt
  have hr := innerRetraction_relative Z₀ P R hR δ hδ0 hδlt
  dsimp only at hr
  rw [mem_innerCylinder_iff, mem_forwardCylinder_iff, hr.1, hr.2.1, hr.2.2,
    smul_ball_iff _ _ _ hρ, smul_ball_iff _ _ _ (pow_pos hρ 3)]
  have hv : relativeVelocity Z₀ P ∈ PDE.euclideanBall 0 R ↔
      P.velocity ∈ PDE.euclideanBall Z₀.velocity R := by
    simp [relativeVelocity, PDE.euclideanBall, PDE.euclideanSqDist]
  rw [hv]
  constructor <;> rintro ⟨h1,h2,hv,hx⟩ <;> refine ⟨?_,?_,hv,hx⟩ <;>
    nlinarith [sq_pos_of_pos hρ]

/-- Retraction maps the original open cylinder onto the explicit inner cylinder. -/
theorem innerRetraction_image_forwardCylinder {d : ℕ}
    (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (δ : ℝ) (hδ0 : 0 < δ) (hδlt : δ < R ^ 2 / 2) :
    innerRetraction Z₀ R hR δ hδ0 hδlt '' forwardCylinder Z₀ R hR =
      innerCylinder Z₀ R hR δ hδ0 hδlt := by
  ext P
  constructor
  · rintro ⟨Q,hQ,rfl⟩
    exact (retraction_mem_inner_iff Z₀ Q R hR δ hδ0 hδlt).2 hQ
  · intro hP
    let e := innerRetractionHomeomorph Z₀ R hR δ hδ0 hδlt
    refine ⟨e.symm P,?_,e.apply_symm_apply P⟩
    apply (retraction_mem_inner_iff Z₀ (e.symm P) R hR δ hδ0 hδlt).1
    change e (e.symm P) ∈ innerCylinder Z₀ R hR δ hδ0 hδlt
    simpa only [e.apply_symm_apply] using hP

/-- Retraction is onto on the closures. -/
theorem innerRetraction_image_closure {d : ℕ}
    (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (δ : ℝ) (hδ0 : 0 < δ) (hδlt : δ < R ^ 2 / 2) :
    innerRetraction Z₀ R hR δ hδ0 hδlt '' closure (forwardCylinder Z₀ R hR) =
      closure (innerCylinder Z₀ R hR δ hδ0 hδlt) := by
  rw [← innerRetraction_image_forwardCylinder Z₀ R hR δ hδ0 hδlt]
  exact (innerRetractionHomeomorph Z₀ R hR δ hδ0 hδlt).image_closure _

private theorem retraction_dot {d : ℕ}
    (Z₀ P : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (δ : ℝ) (hδ0 : 0 < δ) (hδlt : δ < R ^ 2 / 2) :
    PDE.vecDot (relativeVelocity Z₀ (innerRetraction Z₀ R hR δ hδ0 hδlt P))
        (relativePosition Z₀ (innerRetraction Z₀ R hR δ hδ0 hδlt P)) =
      (innerRatio R hR δ hδ0 hδlt)^4 *
        PDE.vecDot (relativeVelocity Z₀ P) (relativePosition Z₀ P) := by
  have hr := innerRetraction_relative Z₀ P R hR δ hδ0 hδlt
  dsimp only at hr
  rw [hr.2.1,hr.2.2]
  unfold PDE.vecDot
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

private theorem retraction_mem_exit_iff {d : ℕ}
    (Z₀ P : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (δ : ℝ) (hδ0 : 0 < δ) (hδlt : δ < R ^ 2 / 2) :
    innerRetraction Z₀ R hR δ hδ0 hδlt P ∈ innerExitBoundary Z₀ R hR δ hδ0 hδlt ↔
      P ∈ exitBoundary Z₀ R hR := by
  obtain ⟨hρ,_,hs⟩ := innerRatio_spec R hR δ hδ0 hδlt
  have hr := innerRetraction_relative Z₀ P R hR δ hδ0 hδlt
  dsimp only at hr
  rw [mem_innerExitBoundary_iff,mem_exitBoundary_iff]
  dsimp only
  rw [← innerRetraction_image_closure Z₀ R hR δ hδ0 hδlt]
  have hi : innerRetraction Z₀ R hR δ hδ0 hδlt P ∈
      innerRetraction Z₀ R hR δ hδ0 hδlt '' closure (forwardCylinder Z₀ R hR) ↔
      P ∈ closure (forwardCylinder Z₀ R hR) :=
    (innerRetractionHomeomorph Z₀ R hR δ hδ0 hδlt).injective.mem_set_image
  rw [hi,hr.1,hr.2.1,hr.2.2,smul_sphere_iff _ _ _ hρ,
    smul_sphere_iff _ _ _ (pow_pos hρ 3)]
  have ht : Z₀.time+δ+(innerRatio R hR δ hδ0 hδlt)^2*(P.time-Z₀.time) =
      Z₀.time+R^2-δ ↔ P.time = Z₀.time+R^2 := by
    constructor <;> intro h <;> nlinarith [sq_pos_of_pos hρ]
  have hv : relativeVelocity Z₀ P ∈ PDE.euclideanSphere 0 R ↔
      P.velocity ∈ PDE.euclideanSphere Z₀.velocity R := by
    simp [relativeVelocity,PDE.euclideanSphere,PDE.euclideanSqDist]
  rw [ht,hv]
  have hd := retraction_dot Z₀ P R hR δ hδ0 hδlt
  rw [hr.2.1,hr.2.2] at hd
  rw [hd, mul_nonneg_iff_of_pos_left (pow_pos hρ 4)]

/-- Retraction is onto on the exit boundaries, including grazing points. -/
theorem innerRetraction_image_exitBoundary {d : ℕ}
    (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (δ : ℝ) (hδ0 : 0 < δ) (hδlt : δ < R ^ 2 / 2) :
    innerRetraction Z₀ R hR δ hδ0 hδlt '' exitBoundary Z₀ R hR =
      innerExitBoundary Z₀ R hR δ hδ0 hδlt := by
  ext P
  constructor
  · rintro ⟨Q,hQ,rfl⟩
    exact (retraction_mem_exit_iff Z₀ Q R hR δ hδ0 hδlt).2 hQ
  · intro hP
    let e := innerRetractionHomeomorph Z₀ R hR δ hδ0 hδlt
    refine ⟨e.symm P,?_,e.apply_symm_apply P⟩
    apply (retraction_mem_exit_iff Z₀ (e.symm P) R hR δ hδ0 hδlt).1
    change e (e.symm P) ∈ innerExitBoundary Z₀ R hR δ hδ0 hδlt
    simpa only [e.apply_symm_apply] using hP

end HypoellipticAleksandrov.KineticAleksandrov

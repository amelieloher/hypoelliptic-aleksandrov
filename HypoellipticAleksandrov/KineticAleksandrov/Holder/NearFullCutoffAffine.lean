module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullCutoff
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.AffineGeometry
import Mathlib.Tactic

/-! # Affine transport and boundary values of the source interior cutoff -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set

/-- The product-coordinate inverse of the source affine map is smooth for every radius. -/
theorem contDiff_kineticAffineInverse_prod {d : ℕ} (P₀ : KineticPoint d) (R : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × (PDE.Vec d × PDE.Vec d) =>
      KineticPoint.equivProd d
        (kineticAffineInverse P₀ R ((KineticPoint.equivProd d).symm z))) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × (PDE.Vec d × PDE.Vec d) =>
    ((z.1 - P₀.time) / R ^ 2,
      ((R ^ 3)⁻¹ • (z.2.1 - P₀.position - (z.1 - P₀.time) • P₀.velocity),
        R⁻¹ • (z.2.2 - P₀.velocity))))
  have ht : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : ℝ × (PDE.Vec d × PDE.Vec d) => z.1) := contDiff_fst
  have hx : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : ℝ × (PDE.Vec d × PDE.Vec d) => z.2.1) :=
    contDiff_fst.comp contDiff_snd
  have hv : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : ℝ × (PDE.Vec d × PDE.Vec d) => z.2.2) :=
    contDiff_snd.comp contDiff_snd
  simpa only [Pi.smul_apply', Pi.sub_apply] using
    ((ht.sub contDiff_const).div_const (R ^ 2)).prodMk
      (((contDiff_const (c := ((R ^ 3)⁻¹ : ℝ))).smul
        ((hx.sub contDiff_const).sub
          ((ht.sub contDiff_const).smul (contDiff_const (c := P₀.velocity))))).prodMk
        ((contDiff_const (c := (R⁻¹ : ℝ))).smul (hv.sub contDiff_const)))

/-- The source cutoff scaled to a physical cylinder and level. -/
def scaledUnitCutoff {d : ℕ} (f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ)
    (P₀ : KineticPoint d) (R ell : ℝ) (P : KineticPoint d) : ℝ :=
  ell * f (KineticPoint.equivProd d (kineticAffineInverse P₀ R P))

/-- Smooth unit cutoffs give source-smooth tests near every set after affine transport. -/
theorem scaledUnitCutoff_isSmoothNear {d : ℕ}
    {f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (P₀ : KineticPoint d) (R ell : ℝ)
    (E : Set (KineticPoint d)) : IsSmoothNear (scaledUnitCutoff f P₀ R ell) E := by
  refine ⟨univ, isOpen_univ, subset_univ E, ?_⟩
  exact (contDiff_const.mul (hf.comp (contDiff_kineticAffineInverse_prod P₀ R))).contDiffOn

/-- The scaled cutoff stays between zero and its nonnegative level. -/
theorem scaledUnitCutoff_bounds {d : ℕ}
    {f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ}
    (hf : ∀ z, 0 ≤ f z ∧ f z ≤ 1) (P₀ : KineticPoint d) (R ell : ℝ)
    (hell : 0 ≤ ell) (P : KineticPoint d) :
    0 ≤ scaledUnitCutoff f P₀ R ell P ∧ scaledUnitCutoff f P₀ R ell P ≤ ell := by
  obtain ⟨h0, h1⟩ := hf (KineticPoint.equivProd d (kineticAffineInverse P₀ R P))
  exact ⟨mul_nonneg hell h0, (mul_le_mul_of_nonneg_left h1 hell).trans_eq (mul_one ell)⟩

/-- The scaled plateau has exactly the prescribed level on the source affine cap. -/
theorem scaledUnitCutoff_eq_level {d : ℕ}
    {f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ}
    (hf : ∀ P ∈ closure (cap d), f (KineticPoint.equivProd d P) = 1)
    (P₀ : KineticPoint d) {R : ℝ} (hR : 0 < R) (ell : ℝ)
    {P : KineticPoint d} (hP : P ∈ kineticAffine P₀ R '' cap d) :
    scaledUnitCutoff f P₀ R ell P = ell := by
  obtain ⟨Q, hQ, rfl⟩ := hP
  unfold scaledUnitCutoff
  rw [kineticAffineInverse_apply P₀ hR.ne' Q, hf Q (subset_closure hQ), mul_one]

/-- A unit cutoff supported inside the cylinder vanishes outside its affine image. -/
theorem scaledUnitCutoff_eq_zero_of_not_mem {d : ℕ}
    {f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ}
    (hf : tsupport f ⊆ KineticPoint.equivProd d ''
      backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1)
    (P₀ : KineticPoint d) {R : ℝ} (hR : 0 < R) (ell : ℝ)
    {P : KineticPoint d} (hP : P ∉ backwardCylinder P₀ R) :
    scaledUnitCutoff f P₀ R ell P = 0 := by
  have hz : f (KineticPoint.equivProd d (kineticAffineInverse P₀ R P)) = 0 := by
    by_contra hn
    have hm := hf (subset_closure (show KineticPoint.equivProd d
      (kineticAffineInverse P₀ R P) ∈ Function.support f from hn))
    obtain ⟨Q, hQ, hEq⟩ := hm
    have hQP : Q = kineticAffineInverse P₀ R P :=
      (KineticPoint.equivProd d).injective hEq
    rw [hQP] at hQ
    have ha := (kineticAffine_mem_cylinder P₀ _ hR).mpr hQ
    rw [kineticAffine_apply_inverse P₀ hR.ne' P] at ha
    exact hP ha
  simp only [scaledUnitCutoff, hz, mul_zero]

/-- The source kinetic boundary is disjoint from the open backward cylinder. -/
theorem kineticBoundary_not_mem_backwardCylinder {d : ℕ} {P₀ P : KineticPoint d}
    {R : ℝ} (hP : P ∈ kineticBoundary P₀ R) : P ∉ backwardCylinder P₀ R := by
  intro hQ
  rw [mem_kineticBoundary_iff] at hP
  obtain ⟨_, ht | hv | hx⟩ := hP
  · exact (ne_of_gt hQ.1) ht
  · exact (ne_of_lt hQ.2.2.1) hv
  · exact (ne_of_lt hQ.2.2.2) hx.1

/-- The cutoff has zero value on every source comparison boundary point. -/
theorem scaledUnitCutoff_boundary_eq_zero {d : ℕ}
    {f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ}
    (hf : tsupport f ⊆ KineticPoint.equivProd d ''
      backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1)
    (P₀ : KineticPoint d) {R : ℝ} (hR : 0 < R) (ell : ℝ)
    {P : KineticPoint d} (hP : P ∈ kineticBoundary P₀ R) :
    scaledUnitCutoff f P₀ R ell P = 0 :=
  scaledUnitCutoff_eq_zero_of_not_mem hf P₀ hR ell
    (kineticBoundary_not_mem_backwardCylinder hP)

end HypoellipticAleksandrov.KineticAleksandrov.Holder

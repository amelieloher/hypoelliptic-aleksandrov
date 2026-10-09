module

public import HypoellipticAleksandrov.Parabolic.HarnackUnitCylinder.ClassicalWeakEquation
public import HypoellipticAleksandrov.Parabolic.HarnackUnitCylinder.LocalWeakHarnack
public import HypoellipticAleksandrov.Parabolic.HarnackUnitCylinder.ChainGeometry

/-! # The classical parabolic Harnack inequality on the unit cylinder -/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open Set

/-- Every nonnegative C¹,² solution satisfies the unit-cylinder Harnack comparison. -/
theorem parabolic_harnack_unit_cylinder_aux
    (N : ℕ) (hN : 1 ≤ N) (lam : ℝ) (hlam : 0 < lam)
    (Lam : ℝ) (hlamLam : lam ≤ Lam) :
    ∃ h : ℝ, 0 < h ∧
      ∀ (B : CoefficientField N) (u : TimeVelocity N → ℝ),
        IsContinuousCoefficientOn B
          (Set.Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec N) 1) →
        (∀ z ∈ Set.Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec N) 1,
          (coefficientAt B z).IsSymm) →
        HasLowerEllipticityOn lam B
          (Set.Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec N) 1) →
        HasUpperEllipticityOn Lam B
          (Set.Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec N) 1) →
        IsScalarC12On u
          (Set.Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec N) 1) →
        IsNonnegativeOn u
          (Set.Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec N) 1) →
        (∀ z ∈ Set.Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec N) 1,
          scalarTimeDerivative u z =
            matrixContraction (coefficientAt B z) (scalarSpatialHessian u z)) →
        ∀ P ∈ Set.Ioo (1 / 4 : ℝ) (1 / 2 : ℝ) ×ˢ
            PDE.euclideanBall (0 : PDE.Vec N) (1 / 2 : ℝ),
          ∀ P' ∈ Set.Ioo (3 / 4 : ℝ) 1 ×ˢ
              PDE.euclideanBall (0 : PDE.Vec N) (1 / 2 : ℝ),
            h * u P ≤ u P' := by
  obtain ⟨hBox, hh0, _hh1, hlocal⟩ :=
    exists_local_parabolic_harnack_weak_continuous N hN lam hlam Lam hlamLam
  refine ⟨hBox ^ (256 * N), pow_pos hh0 _, ?_⟩
  intro B u hB hSymm hLower hUpper hu huNonneg heq P hP P' hP'
  let U := Ioo (0 : ℝ) 1 ×ˢ PDE.euclideanBall (0 : PDE.Vec N) 1
  have hU : IsOpen U := isOpen_Ioo.prod (PDE.isOpen_euclideanBall _ _)
  have hWeak := IsScalarC12On.isWeakParabolicEquationLoc hU hu heq (parabolicExponent N)
  let m : ℕ := 256 * N
  let dt : ℝ := (P'.1 - P.1) / (m : ℝ)
  let r : ℝ := Real.sqrt dt
  let t : ℕ → ℝ := fun k => P.1 + (k : ℝ) * dt
  let v : ℕ → PDE.Vec N := fun k =>
    P.2 + ((k : ℝ) / (m : ℝ)) • (P'.2 - P.2)
  have hgeom := unitCylinder_harnack_link_geometry N hN P P' hP hP'
  change 0 < m ∧ 0 < r ∧ (t 0, v 0) = P ∧ (t m, v m) = P' ∧
    (∀ k < m, t (k + 1) = t k + r ^ 2) ∧
    (∀ k < m, parabolicClosedBox 2 r (t k - r ^ 2) (v k) ⊆ U) ∧
    (∀ k < m, v (k + 1) ∈ velocityCube (v k) (r / 2)) at hgeom
  obtain ⟨_hm, hr, hstart, hend, htstep, hboxes, hvstep⟩ := hgeom
  have hchain : ∀ k ≤ m, hBox ^ k * u P ≤ u (t k, v k) := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [pow_zero, one_mul, hstart, le_refl]
    | succ k ih =>
      intro hk
      have hkm : k < m := Nat.lt_of_succ_le hk
      have hlink := hlocal U B u (t k) (v k) r hU hr (hboxes k hkm)
        hB hSymm hLower hUpper hWeak hu.continuousOn huNonneg (v (k + 1)) (hvstep k hkm)
      rw [← htstep k hkm] at hlink
      calc
        hBox ^ (k + 1) * u P = hBox * (hBox ^ k * u P) := by rw [pow_succ]; ring
        _ ≤ hBox * u (t k, v k) :=
          mul_le_mul_of_nonneg_left (ih (Nat.le_of_lt hkm)) hh0.le
        _ ≤ u (t (k + 1), v (k + 1)) := hlink
  simpa only [hend] using hchain m le_rfl

end HypoellipticAleksandrov.Parabolic

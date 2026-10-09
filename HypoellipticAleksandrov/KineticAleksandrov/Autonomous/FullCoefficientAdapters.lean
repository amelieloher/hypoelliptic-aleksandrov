module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ScalarAdapters
public import HypoellipticAleksandrov.KineticAleksandrov.EvolutionProblem

/-! # Full-coefficient smoothness, symmetry, and Loewner adapters -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open scoped MatrixOrder

/-- The physical full coefficient has exactly the smoothness of the source scalar. -/
theorem autonomousCoefficient_smooth {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) :
    IsSmoothFullKineticCoefficient (autonomousCoefficient A.a) := by
  intro i j
  exact A.smooth.comp
    (((contDiff_apply ℝ ℝ (0 : Fin 1)).comp (contDiff_snd.fst)).prodMk
      ((contDiff_apply ℝ ℝ (0 : Fin 1)).comp (contDiff_snd.snd)))

/-- Swapping physical coordinates preserves smoothness for the evolution convention. -/
theorem evolutionCoefficient_smooth {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) :
    IsSmoothFullKineticCoefficient (evolutionCoefficient A.a) := by
  intro i j
  exact A.smooth.comp
    (((contDiff_apply ℝ ℝ (0 : Fin 1)).comp (contDiff_snd.snd)).prodMk
      ((contDiff_apply ℝ ℝ (0 : Fin 1)).comp (contDiff_snd.fst)))

/-- A one-dimensional scalar coefficient is symmetric. -/
theorem autonomousCoefficient_symmetric (a : ℝ → ℝ → ℝ) :
    IsSymmetricFullKineticCoefficient (autonomousCoefficient a) := by
  intro t x v
  rfl

/-- The evolution coefficient is symmetric too. -/
theorem evolutionCoefficient_symmetric (a : ℝ → ℝ → ℝ) :
    IsSymmetricFullKineticCoefficient (evolutionCoefficient a) := by
  intro t y z
  rfl

private theorem scalar_matrix_le {a b : ℝ} (hab : a ≤ b) :
    Matrix.diagonal (fun _ : Fin 1 => a) ≤ Matrix.diagonal (fun _ : Fin 1 => b) := by
  rw [Matrix.le_iff, Matrix.diagonal_sub, Matrix.posSemidef_diagonal_iff]
  intro i
  exact sub_nonneg.mpr hab

private theorem scalar_diagonal (a : ℝ) :
    Matrix.diagonal (fun _ : Fin 1 => a) = fun _ _ => a := by
  ext i j
  have hi := Fin.eq_zero i
  have hj := Fin.eq_zero j
  subst i
  subst j
  exact Matrix.diagonal_apply_eq _ _

private theorem scalar_smul_identity (a : ℝ) :
    a • (1 : PDE.Mat 1) = fun _ _ => a := by
  ext i j
  have hi : i = 0 := Fin.eq_zero i
  have hj : j = 0 := Fin.eq_zero j
  subst i
  subst j
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]

/-- Pointwise scalar ellipticity is exactly full-matrix Loewner ellipticity in dimension one. -/
theorem autonomousCoefficient_bounds {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) :
    HasEverywhereLoewnerBounds lam Lam (autonomousCoefficient A.a) := by
  intro t x v
  simp only [scalar_smul_identity]
  have heq : autonomousCoefficient A.a t x v =
      Matrix.diagonal (fun _ : Fin 1 => A.a (x 0) (v 0)) :=
    (scalar_diagonal _).symm
  rw [← scalar_diagonal lam, ← scalar_diagonal Lam, heq]
  exact ⟨scalar_matrix_le (A.bounds (x 0) (v 0)).1,
    scalar_matrix_le (A.bounds (x 0) (v 0)).2⟩

/-- The physical bounds survive the Section Two coordinate exchange. -/
theorem evolutionCoefficient_bounds {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) :
    HasEverywhereLoewnerBounds lam Lam (evolutionCoefficient A.a) := by
  intro t y z
  simp only [scalar_smul_identity]
  have heq : evolutionCoefficient A.a t y z =
      Matrix.diagonal (fun _ : Fin 1 => A.a (z 0) (y 0)) :=
    (scalar_diagonal _).symm
  rw [← scalar_diagonal lam, ← scalar_diagonal Lam, heq]
  exact ⟨scalar_matrix_le (A.bounds (z 0) (y 0)).1,
    scalar_matrix_le (A.bounds (z 0) (y 0)).2⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

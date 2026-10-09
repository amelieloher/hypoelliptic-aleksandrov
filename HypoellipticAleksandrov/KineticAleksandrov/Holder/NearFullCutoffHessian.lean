module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullCutoffJets
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonLinear
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCalculus
import Mathlib.Tactic

/-! # Exact velocity-Hessian scaling of the source cutoff -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Parabolic Scaling

/-- The velocity slice of the unit product cutoff. -/
def unitCutoffVelocitySlice {d : ℕ}
    (f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ) (Q : KineticPoint d) : PDE.Vec d → ℝ :=
  fun w => f (Q.time, (Q.position, w))

/-- A source-smooth product cutoff has smooth velocity slices. -/
theorem contDiff_unitCutoffVelocitySlice {d : ℕ}
    {f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (Q : KineticPoint d) :
    ContDiff ℝ (⊤ : ℕ∞) (unitCutoffVelocitySlice f Q) :=
  hf.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))

/-- The physical velocity Hessian scales by level times inverse-square radius. -/
theorem scaledUnitCutoff_velocityHessian {d : ℕ}
    {f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (P₀ P : KineticPoint d) (R ell : ℝ) :
    kineticVelocityHessian (scaledUnitCutoff f P₀ R ell) P =
      (ell * (R ^ 2)⁻¹) • sliceHessian
        (unitCutoffVelocitySlice f (kineticAffineInverse P₀ R P))
        (kineticAffineInverse P₀ R P).velocity := by
  let Q := kineticAffineInverse P₀ R P
  let g := unitCutoffVelocitySlice f Q
  let w₀ := -(R⁻¹ • P₀.velocity)
  have hg : ContDiff ℝ 2 g :=
    (contDiff_unitCutoffVelocitySlice hf Q).of_le (by simp)
  have hmap : ContDiff ℝ 2 (fun w : PDE.Vec d => w₀ + R⁻¹ • w) := by fun_prop
  have heq : (fun w : PDE.Vec d => scaledUnitCutoff f P₀ R ell
      ⟨P.time, P.position, w⟩) = fun w => ell * g (w₀ + R⁻¹ • w) := by
    funext w
    change ell * f ((P.time - P₀.time) / R ^ 2,
      ((R ^ 3)⁻¹ • relativePosition P₀ P, R⁻¹ • (w - P₀.velocity))) =
        ell * f ((P.time - P₀.time) / R ^ 2,
          ((R ^ 3)⁻¹ • relativePosition P₀ P, w₀ + R⁻¹ • w))
    have hv : R⁻¹ • (w - P₀.velocity) = w₀ + R⁻¹ • w := by
      ext i
      simp [w₀]
      ring
    rw [hv]
  have hbase : w₀ + R⁻¹ • P.velocity = Q.velocity := by
    ext i
    simp [w₀, Q, kineticAffineInverse, relativeVelocity]
    ring
  have hgmap : ContDiff ℝ 2 (fun w => g (w₀ + R⁻¹ • w)) := by
    simpa only [Function.comp_def] using hg.comp hmap
  rw [kineticVelocityHessian_eq_sliceHessian, heq,
    sliceHessian_const_mul ell hgmap.contDiffAt,
    sliceHessian_affine (g := g) (y₀ := w₀) (c := R⁻¹) hg.contDiffAt, hbase]
  simp only [smul_smul, inv_pow]
  rfl

/-- The physical backward operator is the exact inverse-square unit jet expression. -/
theorem scaledUnitCutoff_backwardOperator {d : ℕ}
    {f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (A : FullKineticCoefficient d)
    (P₀ P : KineticPoint d) (R ell : ℝ) :
    backwardOperator A (scaledUnitCutoff f P₀ R ell) P =
      ell * (R ^ 2)⁻¹ *
        (fderiv ℝ f (KineticPoint.equivProd d (kineticAffineInverse P₀ R P))
          (1, ((kineticAffineInverse P₀ R P).velocity, 0)) -
          matrixContraction (fullKineticCoefficientAt A P)
            (sliceHessian (unitCutoffVelocitySlice f (kineticAffineInverse P₀ R P))
              (kineticAffineInverse P₀ R P).velocity)) := by
  rw [backwardOperator_apply, scaledUnitCutoff_transport hf,
    scaledUnitCutoff_velocityHessian hf, matrixContraction_smul_right]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Holder

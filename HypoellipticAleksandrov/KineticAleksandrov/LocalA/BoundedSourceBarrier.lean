module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceTraces
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonNodes
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonRadial
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # Velocity-quadratic source barrier

The diffused position coordinate in Section Two is the physical velocity coordinate.
Lower ellipticity gives the required dimension-dependent quadratic supersolution.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov Parabolic Set Matrix Evolution
open scoped MatrixOrder

/-- Quadratic source barrier in the diffused coordinate. -/
def boundedSourceQuadratic {d : ℕ} (c : PDE.Vec d) (R lam : ℝ)
    (p : KineticPoint d) : ℝ :=
  (R ^ 2 - PDE.vecNormSq (p.position - c)) / (2 * (d : ℝ) * lam)

/-- The quadratic barrier is continuous without any sign assumptions on its parameters. -/
theorem continuous_boundedSourceQuadratic {d : ℕ} (c : PDE.Vec d) (R lam : ℝ) :
    Continuous (boundedSourceQuadratic c R lam) :=
  (continuous_const.sub
    ((contDiff_vecNormSq_sub c).continuous.comp continuous_position)).div_const _

/-- Every coordinate slice of the quadratic barrier has the required classical regularity. -/
theorem isSliceRegularAt_boundedSourceQuadratic {d : ℕ} (c : PDE.Vec d)
    (R lam : ℝ) (p : KineticPoint d) :
    IsSliceRegularAt (boundedSourceQuadratic c R lam) p := by
  unfold boundedSourceQuadratic
  refine ⟨?_, ?_, ?_⟩
  · change DifferentiableAt ℝ (fun _ : ℝ =>
      (R ^ 2 - PDE.vecNormSq (p.position - c)) / (2 * (d : ℝ) * lam)) p.time
    exact differentiableAt_const _
  · change ContDiffAt ℝ 2 (fun y : PDE.Vec d =>
      (R ^ 2 - PDE.vecNormSq (y - c)) / (2 * (d : ℝ) * lam)) p.position
    exact ((contDiff_const.sub (contDiff_vecNormSq_sub c)).div_const _).contDiffAt
  · change ContDiffAt ℝ 2 (fun _ : PDE.Vec d =>
      (R ^ 2 - PDE.vecNormSq (p.position - c)) / (2 * (d : ℝ) * lam)) p.velocity
    exact contDiffAt_const

/-- Lower Loewner ellipticity controls the trace in the exact dimension normalization. -/
theorem trace_ge_of_smul_one_le {d : ℕ} {A : PDE.Mat d} {lam : ℝ}
    (h : lam • (1 : PDE.Mat d) ≤ A) : (d : ℝ) * lam ≤ A.trace := by
  have htrace := (Matrix.le_iff.mp h).trace_nonneg
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one] at htrace
  simp only [Fintype.card_fin, smul_eq_mul] at htrace
  linarith

/-- The unregularized kinetic operator of the quadratic barrier. -/
theorem viscousTransportedOperator_boundedSourceQuadratic {d : ℕ}
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (c : PDE.Vec d) (R lam : ℝ) (p : KineticPoint d) :
    viscousTransportedOperator B b 0 (boundedSourceQuadratic c R lam) p =
      -(2 * (B p.time p.position p.velocity).trace) / (2 * (d : ℝ) * lam) := by
  let Ψ : ℝ → ℝ := fun s => (R ^ 2 - s) / (2 * (d : ℝ) * lam)
  have hΨ : ContDiff ℝ 2 Ψ := (contDiff_const.sub contDiff_id).div_const _
  have hd : ∀ s, deriv Ψ s = -(1 / (2 * (d : ℝ) * lam)) := by
    intro s
    simpa only [Pi.sub_apply, id_eq, zero_sub, neg_div] using
      (((hasDerivAt_const s (R ^ 2)).sub (hasDerivAt_id s)).div_const
        (2 * (d : ℝ) * lam)).deriv
  have hdd : ∀ s, deriv (deriv Ψ) s = 0 := by
    intro s
    rw [show deriv Ψ = fun _ => -(1 / (2 * (d : ℝ) * lam)) from funext hd]
    exact deriv_const _ _
  have hdiff : matrixContraction (B p.time p.position p.velocity)
      (diffusedHessian (boundedSourceQuadratic c R lam) p) =
      -(2 * (B p.time p.position p.velocity).trace) / (2 * (d : ℝ) * lam) := by
    rw [diffusedHessian_eq_sliceHessian]
    change matrixContraction _ (sliceHessian (fun y => Ψ (PDE.vecNormSq (y - c))) _) = _
    rw [matrixContraction_sliceHessian_comp_vecNormSq_sub hΨ.contDiffAt, hd, hdd]
    ring
  have ht : kineticTimeDerivative (boundedSourceQuadratic c R lam) p = 0 := by
    change deriv (fun _ : ℝ =>
      (R ^ 2 - PDE.vecNormSq (p.position - c)) / (2 * (d : ℝ) * lam)) p.time = 0
    exact deriv_const _ _
  have hv : kineticVelocityGradient (boundedSourceQuadratic c R lam) p = 0 := by
    ext i
    change fderiv ℝ (fun _ : PDE.Vec d =>
      (R ^ 2 - PDE.vecNormSq (p.position - c)) / (2 * (d : ℝ) * lam))
        p.velocity (PDE.basisVec i) = 0
    rw [fderiv_const_apply]
    rfl
  rw [viscousTransportedOperator_apply, transportedForwardOperator_apply,
    fullKineticCoefficientAt_apply, ht, hdiff, hv]
  simp only [PDE.vecDot, Pi.zero_apply, mul_zero,
    Finset.sum_const_zero, zero_add, add_zero, zero_mul]

/-- Positive dimension and lower ellipticity make the quadratic a source-one supersolution. -/
theorem viscousTransportedOperator_boundedSourceQuadratic_le {d : ℕ}
    (hd : 0 < d) {lam Lam : ℝ} (hlam : 0 < lam)
    (B : FullKineticCoefficient d) (hell : HasEverywhereLoewnerBounds lam Lam B)
    (b : PDE.Vec d → PDE.Vec d) (c : PDE.Vec d) (R : ℝ) (p : KineticPoint d) :
    viscousTransportedOperator B b 0 (boundedSourceQuadratic c R lam) p ≤ -1 := by
  rw [viscousTransportedOperator_boundedSourceQuadratic]
  have htr := trace_ge_of_smul_one_le (hell p.time p.position p.velocity).1
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  apply (div_le_iff₀ (mul_pos (mul_pos (by norm_num) hdR) hlam)).2
  nlinarith only [htr]

/-- Smoothness in transported coordinates implies slice regularity of the literal potential. -/
theorem boundedSource_sliceRegular_of_smooth {d : ℕ} (u : KineticPoint d → ℝ)
    (p : KineticPoint d)
    (hu : ContDiffAt ℝ (⊤ : ℕ∞) (u ∘ evolutionHomeomorph d)
      ((evolutionHomeomorph d).symm p)) : IsSliceRegularAt u p := by
  apply IsSliceRegularAt.of_contDiffAt
  have h := hu.comp (p.time, p.position, p.velocity)
    (evolutionProdCLE d).symm.contDiff.contDiffAt
  have hraw : rawLift u = (u ∘ evolutionHomeomorph d) ∘ (evolutionProdCLE d).symm := by
    funext q
    change u ⟨q.1, q.2.1, q.2.2⟩ = u (evolutionHomeomorph d (Occupation.packQ d q))
    rw [duhamel_homeomorph_packQ]
  rw [hraw]
  exact h.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))

/-- The quadratic barrier is nonnegative on the closed ball in the actual Euclidean geometry. -/
theorem boundedSourceQuadratic_nonneg {d : ℕ} {lam : ℝ}
    (hlam : 0 < lam) (c : PDE.Vec d) (R : ℝ) (p : KineticPoint d)
    (hp : p.position ∈ closure (PDE.euclideanBall c R)) :
    0 ≤ boundedSourceQuadratic c R lam p := by
  have hs : closure (PDE.euclideanBall c R) ⊆
      {y : PDE.Vec d | PDE.vecNormSq (y - c) ≤ R ^ 2} := by
    apply closure_minimal
    · intro y hy
      change PDE.vecNormSq (y - c) < R ^ 2 at hy
      exact le_of_lt hy
    · exact isClosed_le (contDiff_vecNormSq_sub c).continuous continuous_const
  exact div_nonneg (sub_nonneg.mpr (hs hp))
    (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) hlam.le)

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

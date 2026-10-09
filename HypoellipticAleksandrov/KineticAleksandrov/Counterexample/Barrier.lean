module

public import HypoellipticAleksandrov.KineticAleksandrov.Operator
public import HypoellipticAleksandrov.Analysis.EuclideanNormCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Appendix C's decaying velocity barrier

The quadratic uses the explicit Euclidean squared norm on native vectors.
The operator identity is global; endpoint positivity is restricted to the velocity domain.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open HypoellipticAleksandrov.Parabolic
open scoped BigOperators MatrixOrder

/-- Decaying quadratic barrier from Appendix C. -/
def barrier {d : ℕ} (mu R : ℝ) (P : KineticPoint d) : ℝ :=
  Real.exp (-mu * P.time) * (2 - PDE.vecNormSq P.velocity / R ^ 2)

/-- Exact time derivative. -/
theorem barrier_timeDerivative {d : ℕ} (mu R : ℝ) (P : KineticPoint d) :
    kineticTimeDerivative (barrier mu R) P =
      -mu * Real.exp (-mu * P.time) * (2 - PDE.vecNormSq P.velocity / R ^ 2) := by
  have h := (((hasDerivAt_id P.time).const_mul (-mu)).exp).mul_const
    (2 - PDE.vecNormSq P.velocity / R ^ 2)
  change deriv (fun t => Real.exp (-mu * t) *
    (2 - PDE.vecNormSq P.velocity / R ^ 2)) P.time = _
  simpa only [id_eq, mul_one, mul_assoc, mul_comm, mul_left_comm] using h.deriv

/-- Independence of position. -/
theorem barrier_positionGradient {d : ℕ} (mu R : ℝ) (P : KineticPoint d) :
    kineticPositionGradient (barrier mu R) P = 0 := by
  ext i
  change fderiv ℝ (fun _x : PDE.Vec d =>
    Real.exp (-mu * P.time) * (2 - PDE.vecNormSq P.velocity / R ^ 2))
      P.position (PDE.basisVec i) = 0
  rw [fderiv_const_apply]
  rfl

/-- Exact coordinate velocity gradient. -/
theorem barrier_velocityGradient {d : ℕ} (mu R : ℝ) (P : KineticPoint d) :
    kineticVelocityGradient (barrier mu R) P =
      fun i => -(2 * Real.exp (-mu * P.time) / R ^ 2) * P.velocity i := by
  have h := ((hasFDerivAt_const (c := (2 : ℝ)) P.velocity).sub
    ((hasFDerivAt_vecNormSq P.velocity).mul_const ((R ^ 2)⁻¹))).const_mul
      (Real.exp (-mu * P.time))
  ext i
  change fderiv ℝ (fun v => Real.exp (-mu * P.time) *
    (2 - PDE.vecNormSq v / R ^ 2)) P.velocity (PDE.basisVec i) = _
  dsimp only [Pi.sub_apply] at h
  simp only [div_eq_mul_inv] at *
  rw [h.fderiv]
  simp only [_root_.smul_apply, _root_.sub_apply,
    _root_.zero_apply, smul_eq_mul, vecNormSqFDeriv_apply]
  simp only [PDE.vecDot, PDE.basisVec_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- Exact velocity Hessian, including its diagonal factor two. -/
theorem barrier_velocityHessian {d : ℕ} (mu R : ℝ) (P : KineticPoint d) :
    kineticVelocityHessian (barrier mu R) P =
      (-(2 * Real.exp (-mu * P.time) / R ^ 2)) • (1 : PDE.Mat d) := by
  have hg : (fun v : PDE.Vec d => PDE.classicalGradient
      (fun w => barrier mu R ⟨P.time, P.position, w⟩) v) =
      fun v => (-(2 * Real.exp (-mu * P.time) / R ^ 2)) • v := by
    funext v
    exact barrier_velocityGradient mu R ⟨P.time, P.position, v⟩
  ext i j
  unfold kineticVelocityHessian
  rw [hg]
  have h := (hasFDerivAt_id (𝕜 := ℝ) P.velocity).const_smul
    (-(2 * Real.exp (-mu * P.time) / R ^ 2))
  change HasFDerivAt (fun v : PDE.Vec d =>
    (-(2 * Real.exp (-mu * P.time) / R ^ 2)) • v) _ P.velocity at h
  rw [h.fderiv]
  simp only [_root_.smul_apply, ContinuousLinearMap.id_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, Matrix.one_apply, PDE.basisVec_apply]
  simp only [eq_comm]

/-- Contraction of the barrier Hessian with an arbitrary coefficient. -/
theorem barrier_hessianContraction {d : ℕ} (A : PDE.Mat d) (mu R : ℝ)
    (P : KineticPoint d) :
    matrixContraction A (kineticVelocityHessian (barrier mu R) P) =
      -(2 * Real.exp (-mu * P.time) / R ^ 2) * A.trace := by
  rw [barrier_velocityHessian, matrixContraction_smul_right]
  congr 1
  simp only [matrixContraction, Matrix.one_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, Matrix.trace, Matrix.diag_apply]

/-- Exact backward operator formula, before ellipticity is used. -/
theorem barrier_operator {d : ℕ}
    (A : (PDE.Vec d × PDE.Vec d) → PDE.Mat d) (mu R : ℝ) (P : KineticPoint d) :
    backwardOperator (fun _t x v => A (x, v)) (barrier mu R) P =
      Real.exp (-mu * P.time) *
        (2 * (A (P.position, P.velocity)).trace / R ^ 2 -
          mu * (2 - PDE.vecNormSq P.velocity / R ^ 2)) := by
  rw [backwardOperator_apply, barrier_timeDerivative, barrier_positionGradient]
  simp only [PDE.vecDot, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  rw [barrier_hessianContraction, fullKineticCoefficientAt_apply]
  ring

/-- Loewner lower control implies the dimension-normalized trace lower bound. -/
theorem barrier_trace_lower {d : ℕ} (A : PDE.Mat d) (lam : ℝ)
    (hA : lam • (1 : PDE.Mat d) ≤ A) : (d : ℝ) * lam ≤ A.trace := by
  have hdiag : ∀ i : Fin d, lam ≤ A i i := by
    intro i
    have h := (Matrix.le_iff.mp hA).diag_nonneg (i := i)
    simpa only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
      ite_eq_left, mul_one, sub_nonneg] using h
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hdiag i)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Matrix.trace, Matrix.diag_apply] using hsum

/-- The prescribed decay rate gives a nonnegative backward operator globally. -/
theorem barrier_operator_nonneg {d : ℕ} (hd : 1 ≤ d)
    (A : (PDE.Vec d × PDE.Vec d) → PDE.Mat d) (lam R : ℝ)
    (hlam : 0 < lam) (hR : 0 < R)
    (hA : ∀ q, lam • (1 : PDE.Mat d) ≤ A q) (P : KineticPoint d) :
    0 ≤ backwardOperator (fun _t x v => A (x, v))
      (barrier ((d : ℝ) * lam / R ^ 2) R) P := by
  rw [barrier_operator]
  apply mul_nonneg (Real.exp_pos _).le
  have htrace := barrier_trace_lower _ lam (hA (P.position, P.velocity))
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hbase : 0 ≤ (d : ℝ) * lam := (mul_pos hdpos hlam).le
  have hs : 0 < R ^ 2 := sq_pos_of_pos hR
  have hn := PDE.vecNormSq_nonneg P.velocity
  have hfirst : 0 ≤ 2 * ((A (P.position, P.velocity)).trace - d * lam) / R ^ 2 :=
    div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr htrace)) hs.le
  have hsecond : 0 ≤ (d * lam / R ^ 2) * (PDE.vecNormSq P.velocity / R ^ 2) :=
    mul_nonneg (div_nonneg hbase hs.le) (div_nonneg hn hs.le)
  have heq : 2 * (A (P.position, P.velocity)).trace / R ^ 2 -
      (d * lam / R ^ 2) * (2 - PDE.vecNormSq P.velocity / R ^ 2) =
      2 * ((A (P.position, P.velocity)).trace - d * lam) / R ^ 2 +
        (d * lam / R ^ 2) * (PDE.vecNormSq P.velocity / R ^ 2) := by ring
  rw [heq]
  exact add_nonneg hfirst hsecond

/-- Source terminal time, fixed independently of the flattening scale. -/
def barrierTime (mu : ℝ) : ℝ := Real.log 8 / mu

/-- The chosen terminal time is positive for positive decay rate. -/
theorem barrierTime_pos {mu : ℝ} (hmu : 0 < mu) : 0 < barrierTime mu :=
  div_pos (Real.log_pos (by norm_num)) hmu

/-- The terminal exponential factor is exactly one eighth. -/
theorem barrier_terminal_factor {mu : ℝ} (hmu : 0 < mu) :
    Real.exp (-mu * barrierTime mu) = (1 / 8 : ℝ) := by
  have he : -mu * barrierTime mu = -Real.log 8 := by
    unfold barrierTime
    field_simp
  rw [he, Real.exp_neg, Real.exp_log (by norm_num)]
  norm_num

/-- All endpoint and collar estimates on the source velocity domain. -/
theorem barrier_endpoint_bounds {d : ℕ} (mu R : ℝ)
    (hmu : 0 < mu) (hR : 0 < R) (x v : PDE.Vec d)
    (hv : PDE.vecNormSq v < R ^ 2) :
    1 < barrier mu R ⟨0, x, v⟩ ∧
    (0 < barrier mu R ⟨barrierTime mu, x, v⟩ ∧
      barrier mu R ⟨barrierTime mu, x, v⟩ ≤ 1 / 4) ∧
    (∀ t ∈ Set.Icc 0 (barrierTime mu), (1 / 8 : ℝ) ≤ barrier mu R ⟨t, x, v⟩) := by
  have hs : 0 < R ^ 2 := sq_pos_of_pos hR
  have hv1 : PDE.vecNormSq v / R ^ 2 < 1 := (div_lt_one hs).mpr hv
  have hv0 : 0 ≤ PDE.vecNormSq v / R ^ 2 :=
    div_nonneg (PDE.vecNormSq_nonneg v) hs.le
  have hb : 1 < 2 - PDE.vecNormSq v / R ^ 2 := by linarith only [hv1]
  have hb2 : 2 - PDE.vecNormSq v / R ^ 2 ≤ 2 := by linarith only [hv0]
  constructor
  · simpa only [barrier, mul_zero, Real.exp_zero, one_mul] using hb
  constructor
  · simp only [barrier, barrier_terminal_factor hmu]
    constructor
    · exact mul_pos (by norm_num) (lt_trans (by norm_num) hb)
    · nlinarith only [hb2]
  · intro t ht
    have hexp : (1 / 8 : ℝ) ≤ Real.exp (-mu * t) := by
      rw [← barrier_terminal_factor hmu]
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left ht.2 (neg_nonpos.mpr hmu.le)
    change (1 / 8 : ℝ) ≤ Real.exp (-mu * t) * (2 - PDE.vecNormSq v / R ^ 2)
    calc
      (1 / 8 : ℝ) ≤ Real.exp (-mu * t) := hexp
      _ ≤ Real.exp (-mu * t) * (2 - PDE.vecNormSq v / R ^ 2) :=
        le_mul_of_one_le_right (Real.exp_pos _).le hb.le

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

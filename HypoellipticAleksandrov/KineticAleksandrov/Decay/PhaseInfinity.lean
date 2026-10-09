module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.SourceNotation
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.MaxPrinciple
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCalculus
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonGrowth
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Quadratic phase penalty at transported infinity

Compactness bounds the drift on the moving diffused tube. The resulting local
constant is used only for comparison with a vanishing positive penalty.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open Set Filter
open scoped Topology

/-- The quadratic infinity penalty is continuous in all source coordinates. -/
theorem infinityBarrier_continuous {d : ℕ} (η M τ : ℝ) (z0 : PDE.Vec d) :
    Continuous (infinityBarrier η M τ z0) := by
  have hv : Continuous (fun p : KineticPoint d => p.velocity - z0) :=
    continuous_velocity.sub continuous_const
  have hn := PDE.continuous_vecNormSq.comp hv
  exact (continuous_const.mul (continuous_const.add hn)).mul
    (Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_time)))

/-- The quadratic infinity penalty is slice regular everywhere. -/
theorem infinityBarrier_isSliceRegularAt {d : ℕ} (η M τ : ℝ) (z0 : PDE.Vec d)
    (p : KineticPoint d) : IsSliceRegularAt (infinityBarrier η M τ z0) p := by
  apply IsSliceRegularAt.of_contDiffAt
  unfold rawLift infinityBarrier PDE.vecNormSq PDE.vecDot
  fun_prop

/-- The operator on the quadratic transported-variable penalty. -/
theorem lop_infinityBarrier {d : ℕ} (B : CoefficientField d)
    (b : PDE.Vec d → PDE.Vec d) (η M τ : ℝ) (z0 : PDE.Vec d) (p : KineticPoint d) :
    lop B b (infinityBarrier η M τ z0) p =
      η * Real.exp ((M + 1) * (τ - p.time)) *
        (-(M + 1) * (1 + PDE.vecNormSq (p.velocity - z0)) +
          2 * PDE.vecDot (b p.position) (p.velocity - z0)) := by
  have ht : kineticTimeDerivative (infinityBarrier η M τ z0) p =
      η * (1 + PDE.vecNormSq (p.velocity - z0)) *
        (Real.exp ((M + 1) * (τ - p.time)) * (-(M + 1))) := by
    have h := (((hasDerivAt_id p.time).const_sub τ).const_mul (M + 1)).exp
    have he := (h.const_mul (η * (1 + PDE.vecNormSq (p.velocity - z0)))).deriv
    change kineticTimeDerivative (infinityBarrier η M τ z0) p = _ at he
    simpa only [id_eq, mul_neg_one] using he
  have hg : kineticVelocityGradient (infinityBarrier η M τ z0) p =
      fun i => 2 * (η * Real.exp ((M + 1) * (τ - p.time))) * (p.velocity i - z0 i) := by
    have hf : (fun z : PDE.Vec d => infinityBarrier η M τ z0 ⟨p.time, p.position, z⟩) =
        fun z => (fun s : ℝ => η * Real.exp ((M + 1) * (τ - p.time)) * (1 + s))
          (PDE.vecNormSq (z - z0)) := by
      funext z
      unfold infinityBarrier
      ring
    unfold kineticVelocityGradient
    rw [hf, classicalGradient_comp_vecNormSq_sub
      ((contDiffAt_affine_weight _ _ _).differentiableAt (by norm_num)), deriv_affine_weight]
  have hh : diffusedHessian (infinityBarrier η M τ z0) p = 0 := by
    have hzero : (fun y : PDE.Vec d => kineticPositionGradient
        (infinityBarrier η M τ z0) ⟨p.time, y, p.velocity⟩) = fun _ => 0 := by
      funext y i
      change fderiv ℝ (fun _ : PDE.Vec d => η *
        (1 + PDE.vecNormSq (p.velocity - z0)) *
        Real.exp ((M + 1) * (τ - p.time))) y (PDE.basisVec i) = 0
      rw [fderiv_const_apply]
      rfl
    ext i j
    simp only [diffusedHessian]
    rw [hzero, fderiv_const_apply]
    rfl
  unfold lop transportedForwardOperatorOfTimeDiffusedCoefficient transportedForwardOperator
  rw [ht, hg, hh]
  simp only [matrixContraction, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  have hd : PDE.vecDot (b p.position)
      (fun i => 2 * (η * Real.exp ((M + 1) * (τ - p.time))) * (p.velocity i - z0 i)) =
      2 * (η * Real.exp ((M + 1) * (τ - p.time))) *
        PDE.vecDot (b p.position) (p.velocity - z0) := by
    simp only [PDE.vecDot, Pi.sub_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hd]
  ring

/-- A local drift bound makes the quadratic infinity penalty a strict supersolution. -/
theorem lop_infinityBarrier_le {d : ℕ} (B : CoefficientField d)
    (b : PDE.Vec d → PDE.Vec d) {η M τ : ℝ} (hη : 0 ≤ η) (hM : 0 ≤ M)
    (z0 : PDE.Vec d) (p : KineticPoint d) (hb : PDE.vecEuclideanNorm (b p.position) ≤ M) :
    lop B b (infinityBarrier η M τ z0) p ≤ -infinityBarrier η M τ z0 p := by
  have hcs := PDE.abs_vecDot_le_vecEuclideanNorm_mul (b p.position) (p.velocity - z0)
  have hn := PDE.vecEuclideanNorm_nonneg (p.velocity - z0)
  have hsq := PDE.vecEuclideanNorm_sq (p.velocity - z0)
  have hdot : 2 * PDE.vecDot (b p.position) (p.velocity - z0) ≤
      M * (1 + PDE.vecNormSq (p.velocity - z0)) := by
    have hb' := mul_le_mul_of_nonneg_right hb hn
    have hm' := mul_nonneg hM (sq_nonneg (PDE.vecEuclideanNorm (p.velocity - z0) - 1))
    nlinarith [le_abs_self (PDE.vecDot (b p.position) (p.velocity - z0))]
  rw [lop_infinityBarrier]
  unfold infinityBarrier
  have hh := mul_le_mul_of_nonneg_left hdot
    (mul_nonneg hη (Real.exp_pos ((M + 1) * (τ - p.time))).le)
  nlinarith

/-- The quadratic penalty dominates every level uniformly at transported infinity. -/
theorem infinityBarrier_uniform_growth {d : ℕ} {η M τ : ℝ}
    (hη : 0 < η) (hM : 0 ≤ M) (z0 : PDE.Vec d) (A : ℝ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ p : KineticPoint d, p.time ≤ τ →
      R ≤ PDE.vecEuclideanNorm p.velocity → A ≤ infinityBarrier η M τ z0 p := by
  let Q := max (A / η) 0 + 1
  refine ⟨PDE.vecEuclideanNorm z0 + Q, ?_, ?_⟩
  · dsimp [Q]
    exact add_nonneg (PDE.vecEuclideanNorm_nonneg _)
      (by linarith [le_max_right (A / η) 0])
  · intro p ht hp
    have htriangle := PDE.vecEuclideanNorm_add_le (p.velocity - z0) z0
    rw [sub_add_cancel] at htriangle
    have hQ : 1 ≤ Q := by dsimp [Q]; linarith [le_max_right (A / η) 0]
    have hq : Q ≤ PDE.vecEuclideanNorm (p.velocity - z0) := by linarith
    have hsq := PDE.vecEuclideanNorm_sq (p.velocity - z0)
    have hbase : A ≤ η * (1 + PDE.vecNormSq (p.velocity - z0)) := by
      have hA : A / η ≤ Q := by dsimp [Q]; linarith [le_max_left (A / η) 0]
      have hAs : A ≤ η * Q := by
        simpa only [mul_comm] using (div_le_iff₀ hη).mp hA
      have hmul := mul_le_mul_of_nonneg_left
        (show Q ≤ 1 + PDE.vecNormSq (p.velocity - z0) by nlinarith) hη.le
      exact hAs.trans hmul
    have he : 1 ≤ Real.exp ((M + 1) * (τ - p.time)) :=
      Real.one_le_exp (mul_nonneg (by linarith) (sub_nonneg.mpr ht))
    unfold infinityBarrier
    exact hbase.trans (le_mul_of_one_le_right
      (mul_nonneg hη.le (by linarith [PDE.vecNormSq_nonneg (p.velocity - z0)])) he)

/-- A finite local drift bound supplies the source supersolution and uniform growth. -/
theorem phase_infinity_barrier {d : ℕ} (B : CoefficientField d)
    (b : PDE.Vec d → PDE.Vec d) (σ τ ρ : ℝ) (hρ : 0 < ρ)
    (γ : ℝ → PDE.Vec d) (hγ : ContinuousOn γ (Icc σ τ))
    (hb : Continuous b) (z0 : PDE.Vec d) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ p ∈ maximumClosedTube (PDE.euclideanBall 0 ρ) γ σ τ,
        PDE.vecEuclideanNorm (b p.position) ≤ M) ∧
      ∀ η : ℝ, 0 < η →
        (∀ p ∈ maximumOpenTube (PDE.euclideanBall 0 ρ) γ σ τ,
          lop B b (infinityBarrier η M τ z0) p ≤ -infinityBarrier η M τ z0 p) ∧
        (∀ A : ℝ, ∃ R : ℝ, 0 ≤ R ∧
          ∀ p ∈ maximumClosedTube (PDE.euclideanBall 0 ρ) γ σ τ,
            R ≤ PDE.vecEuclideanNorm p.velocity → A ≤ infinityBarrier η M τ z0 p) := by
  have hc := isCompact_maximumClosedTube_truncated
    (isCompact_closure_of_maximumPrinciple_domain (Or.inl ⟨0, ρ, hρ, rfl⟩)) hγ
    (show (0 : ℝ) ≤ 0 from le_rfl)
  have hf : Continuous
      (fun p : KineticPoint d => PDE.vecEuclideanNorm (b p.position)) :=
    PDE.continuous_vecEuclideanNorm.comp
      (hb.comp (KineticPoint.homeomorphProd d).continuous.snd.fst)
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn hf.continuousOn
  have hbnd : ∀ p ∈ maximumClosedTube (PDE.euclideanBall 0 ρ) γ σ τ,
      PDE.vecEuclideanNorm (b p.position) ≤ max C 0 := by
    intro p hp
    have hh := hC ⟨p.time, p.position, 0⟩
      (show (⟨p.time, p.position, 0⟩ : KineticPoint d) ∈
          {p ∈ maximumClosedTube (PDE.euclideanBall 0 ρ) γ σ τ |
            p.velocity ∈ PDE.euclideanClosedBall 0 0} from
        ⟨hp, by simp [PDE.euclideanClosedBall, PDE.euclideanSqDist,
          PDE.vecNormSq, PDE.vecDot]⟩)
    have ha : ‖PDE.vecEuclideanNorm (b p.position)‖ =
        PDE.vecEuclideanNorm (b p.position) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (PDE.vecEuclideanNorm_nonneg _)]
    rw [ha] at hh
    exact hh.trans (le_max_left C 0)
  refine ⟨max C 0, le_max_right C 0, hbnd, fun η hη => ⟨?_, ?_⟩⟩
  · intro p hp
    apply lop_infinityBarrier_le B b hη.le (le_max_right C 0) z0 p
    exact hbnd p ⟨⟨hp.1.1.le, hp.1.2.le⟩, subset_closure hp.2⟩
  · intro A
    obtain ⟨R, hR, hh⟩ := infinityBarrier_uniform_growth hη (le_max_right C 0) z0 A
    exact ⟨R, hR, fun p hp => hh p hp.1.2⟩

end HypoellipticAleksandrov.KineticAleksandrov.Decay

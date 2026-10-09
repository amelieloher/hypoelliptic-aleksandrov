module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.SourceNotation
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonLinear
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Signed phase barrier calculus

The position field is the diffused source variable v; the velocity field is the
transported source variable z. The source's positive radius is explicit.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open Set Filter
open scoped Topology NNReal

/-- An explicit Euclidean Lipschitz bound implies continuity in the native topology. -/
theorem continuous_of_euclidean_lipschitz {d : ℕ} {Lb : ℝ}
    {b : PDE.Vec d → PDE.Vec d} (hb : HasEuclideanLipschitzDrift Lb b) :
    Continuous b := by
  let K : ℝ≥0 := ⟨|Lb| * Real.sqrt d, mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)⟩
  apply (LipschitzWith.of_dist_le_mul (K := K) ?_).continuous
  intro x y
  simp only [dist_eq_norm]
  calc
    ‖b x - b y‖ ≤ PDE.vecEuclideanNorm (b x - b y) := PDE.norm_le_vecEuclideanNorm _
    _ ≤ Lb * PDE.vecEuclideanNorm (x - y) := hb x y
    _ ≤ |Lb| * PDE.vecEuclideanNorm (x - y) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (PDE.vecEuclideanNorm_nonneg _)
    _ ≤ |Lb| * (Real.sqrt d * ‖x - y‖) :=
      mul_le_mul_of_nonneg_left (PDE.vecEuclideanNorm_le_sqrt_natCast_mul_norm _)
        (abs_nonneg _)
    _ = (K : ℝ) * ‖x - y‖ := by change _ = (|Lb| * Real.sqrt d) * ‖x - y‖; ring

/-- The phase center has the source integrand as its derivative at interior times. -/
theorem phaseCenter_hasDerivAt {d : ℕ} (ξ : PDE.Vec d)
    {Lb : ℝ} {b : PDE.Vec d → PDE.Vec d} (hb : HasEuclideanLipschitzDrift Lb b)
    {γ : ℝ → PDE.Vec d} {σ τ t : ℝ} (hγ : ContinuousOn γ (Icc σ τ))
    (ht : t ∈ Ioo σ τ) :
    HasDerivAt (phaseCenter ξ b γ σ) (PDE.vecDot ξ (b (γ t))) t := by
  have hc : Continuous (fun y : PDE.Vec d => PDE.vecDot ξ (b y)) := by
    unfold PDE.vecDot
    exact continuous_finsetSum _ fun i _ =>
      continuous_const.mul ((continuous_apply i).comp (continuous_of_euclidean_lipschitz hb))
  have hf := hc.comp_continuousOn hγ
  have hat : ContinuousAt (fun r => PDE.vecDot ξ (b (γ r))) t :=
    hf.continuousAt (Icc_mem_nhds ht.1 ht.2)
  have hi : IntervalIntegrable (fun r => PDE.vecDot ξ (b (γ r))) MeasureTheory.volume σ t :=
    (hf.mono (Icc_subset_Icc_right ht.2.le)).intervalIntegrable_of_Icc ht.1.le
  exact intervalIntegral.integral_hasDerivAt_right hi
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
      (hf.mono Ioo_subset_Icc_self) t ht) hat

/-- The transported gradient of the signed phase is its signed unit direction. -/
theorem phase_velocity_gradient {d : ℕ} (sgn : ℝ) (ξ z0 : PDE.Vec d)
    (b : PDE.Vec d → PDE.Vec d) (γ : ℝ → PDE.Vec d) (σ Lb ρ : ℝ)
    (p : KineticPoint d) :
    kineticVelocityGradient (phaseBarrier sgn ξ z0 b γ σ Lb ρ) p = sgn • ξ := by
  let L : PDE.Vec d →L[ℝ] ℝ :=
    ∑ i, (sgn * ξ i) • (ContinuousLinearMap.proj i : PDE.Vec d →L[ℝ] ℝ)
  have h : HasFDerivAt
      (fun z => phaseBarrier sgn ξ z0 b γ σ Lb ρ ⟨p.time, p.position, z⟩)
      L p.velocity := by
    have hd : HasFDerivAt (fun z : PDE.Vec d => PDE.vecDot ξ (z - z0))
        (∑ i, ξ i • (ContinuousLinearMap.proj i : PDE.Vec d →L[ℝ] ℝ)) p.velocity := by
      unfold PDE.vecDot
      exact HasFDerivAt.fun_sum fun i _ =>
        ((hasFDerivAt_apply i p.velocity).sub_const (z0 i)).const_mul (ξ i)
    convert ((hd.sub_const (phaseCenter ξ b γ σ p.time)).const_mul sgn).sub_const
      (Lb * ρ * (p.time - σ)) using 1
    · rfl
    · simp [L, Finset.smul_sum, smul_smul]
  ext i
  change fderiv ℝ _ p.velocity (PDE.basisVec i) = _
  rw [h.fderiv]
  simp [L, PDE.basisVec_apply]

/-- The signed phase is independent of the diffused coordinate. -/
theorem phase_diffused_hessian {d : ℕ} (sgn : ℝ) (ξ z0 : PDE.Vec d)
    (b : PDE.Vec d → PDE.Vec d) (γ : ℝ → PDE.Vec d) (σ Lb ρ : ℝ)
    (p : KineticPoint d) :
    diffusedHessian (phaseBarrier sgn ξ z0 b γ σ Lb ρ) p = 0 := by
  have hg : (fun y : PDE.Vec d => kineticPositionGradient
      (phaseBarrier sgn ξ z0 b γ σ Lb ρ) ⟨p.time, y, p.velocity⟩) = fun _ => 0 := by
    funext y i
    change fderiv ℝ (fun _ : PDE.Vec d =>
      sgn * (PDE.vecDot ξ (p.velocity - z0) - phaseCenter ξ b γ σ p.time) -
      Lb * ρ * (p.time - σ)) y (PDE.basisVec i) = 0
    rw [fderiv_const_apply]
    rfl
  ext i j
  simp only [diffusedHessian]
  rw [hg, fderiv_const_apply]
  rfl

/-- The signed phase barrier has its explicit time derivative at interior times. -/
theorem phaseBarrier_hasDerivAt {d : ℕ} (sgn : ℝ) (ξ z0 : PDE.Vec d)
    {b : PDE.Vec d → PDE.Vec d} {Lb : ℝ} (hb : HasEuclideanLipschitzDrift Lb b)
    {γ : ℝ → PDE.Vec d} {σ τ ρ : ℝ} (hγ : ContinuousOn γ (Icc σ τ))
    (p : KineticPoint d) (ht : p.time ∈ Ioo σ τ) :
    HasDerivAt (fun t => phaseBarrier sgn ξ z0 b γ σ Lb ρ ⟨t, p.position, p.velocity⟩)
      (sgn * (0 - PDE.vecDot ξ (b (γ p.time))) - Lb * ρ) p.time := by
  unfold phaseBarrier
  convert
    (((hasDerivAt_const p.time (PDE.vecDot ξ (p.velocity - z0))).sub
      (phaseCenter_hasDerivAt ξ hb hγ ht)).const_mul sgn).sub
        (((hasDerivAt_id p.time).sub_const σ).const_mul (Lb * ρ)) using 1 <;>
    first | rfl | simp only [mul_one]

/-- The phase barrier is slice regular; no derivative of the moving center is needed. -/
theorem phaseBarrier_isSliceRegularAt {d : ℕ} (sgn : ℝ) (ξ z0 : PDE.Vec d)
    {b : PDE.Vec d → PDE.Vec d} {Lb : ℝ} (hb : HasEuclideanLipschitzDrift Lb b)
    {γ : ℝ → PDE.Vec d} {σ τ ρ : ℝ} (hγ : ContinuousOn γ (Icc σ τ))
    (p : KineticPoint d) (ht : p.time ∈ Ioo σ τ) :
    IsSliceRegularAt (phaseBarrier sgn ξ z0 b γ σ Lb ρ) p := by
  refine ⟨(phaseBarrier_hasDerivAt sgn ξ z0 hb hγ p ht).differentiableAt, ?_, ?_⟩
  · change ContDiffAt ℝ 2 (fun _ : PDE.Vec d =>
      sgn * (PDE.vecDot ξ (p.velocity - z0) - phaseCenter ξ b γ σ p.time) -
      Lb * ρ * (p.time - σ)) p.position
    exact contDiffAt_const
  · dsimp only [phaseBarrier]
    unfold PDE.vecDot
    simp only [Pi.sub_apply]
    fun_prop

/-- The integral phase center is continuous on its defining closed time interval. -/
theorem phaseCenter_continuousOn {d : ℕ} (ξ : PDE.Vec d)
    {b : PDE.Vec d → PDE.Vec d} {Lb : ℝ} (hb : HasEuclideanLipschitzDrift Lb b)
    {γ : ℝ → PDE.Vec d} {σ τ : ℝ} (hστ : σ ≤ τ)
    (hγ : ContinuousOn γ (Icc σ τ)) : ContinuousOn (phaseCenter ξ b γ σ) (Icc σ τ) := by
  have hc : Continuous (fun y : PDE.Vec d => PDE.vecDot ξ (b y)) := by
    unfold PDE.vecDot
    exact continuous_finsetSum _ fun i _ =>
      continuous_const.mul ((continuous_apply i).comp (continuous_of_euclidean_lipschitz hb))
  have hi : IntervalIntegrable (fun r => PDE.vecDot ξ (b (γ r)))
      MeasureTheory.volume σ τ := (hc.comp_continuousOn hγ).intervalIntegrable_of_Icc hστ
  unfold phaseCenter
  simpa only [uIcc_of_le hστ] using
    intervalIntegral.continuousOn_primitive_interval' hi Set.left_mem_uIcc

/-- The phase barrier is continuous on the closed time slab. -/
theorem phaseBarrier_continuousOn {d : ℕ} (sgn : ℝ) (ξ z0 : PDE.Vec d)
    {b : PDE.Vec d → PDE.Vec d} {Lb : ℝ} (hb : HasEuclideanLipschitzDrift Lb b)
    {γ : ℝ → PDE.Vec d} {σ τ ρ : ℝ} (hστ : σ ≤ τ)
    (hγ : ContinuousOn γ (Icc σ τ)) :
    ContinuousOn (phaseBarrier sgn ξ z0 b γ σ Lb ρ) {p | p.time ∈ Icc σ τ} := by
  have hc : Continuous (fun p : KineticPoint d => PDE.vecDot ξ (p.velocity - z0)) := by
    unfold PDE.vecDot
    exact continuous_finsetSum _ fun i _ => continuous_const.mul
      (((continuous_apply i).comp continuous_velocity).sub continuous_const)
  exact ((hc.continuousOn.sub ((phaseCenter_continuousOn ξ hb hστ hγ).comp
    continuous_time.continuousOn (fun _ hp => hp))).const_mul sgn).sub
    ((continuous_time.continuousOn.sub continuousOn_const).const_mul (Lb * ρ))

/-- The signed affine phase barrier has nonpositive transported operator in the tube. -/
theorem phase_barrier_drift {d : ℕ} (B : CoefficientField d)
    (b : PDE.Vec d → PDE.Vec d) (γ : ℝ → PDE.Vec d)
    (σ τ Lb ρ : ℝ) (hρ : 0 < ρ) (ξ z0 : PDE.Vec d) (hξ : PDE.vecNormSq ξ = 1)
    (hb : HasEuclideanLipschitzDrift Lb b) (hγ : ContinuousOn γ (Icc σ τ))
    (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1)
    (p : KineticPoint d) (ht : p.time ∈ Ioo σ τ)
    (hv : p.position ∈ PDE.euclideanBall (γ p.time) ρ) :
    lop B b (phaseBarrier sgn ξ z0 b γ σ Lb ρ) p =
      sgn * PDE.vecDot ξ (b p.position - b (γ p.time)) - Lb * ρ ∧
    lop B b (phaseBarrier sgn ξ z0 b γ σ Lb ρ) p ≤ 0 := by
  have htime : kineticTimeDerivative (phaseBarrier sgn ξ z0 b γ σ Lb ρ) p =
      -sgn * PDE.vecDot ξ (b (γ p.time)) - Lb * ρ := by
    have h := (((hasDerivAt_const p.time (PDE.vecDot ξ (p.velocity - z0))).sub
      (phaseCenter_hasDerivAt ξ hb hγ ht)).const_mul sgn).sub
      (((hasDerivAt_id p.time).sub_const σ).const_mul (Lb * ρ))
    change deriv _ p.time = _
    change deriv (fun t => sgn * (PDE.vecDot ξ (p.velocity - z0) -
      phaseCenter ξ b γ σ t) - Lb * ρ * (t - σ)) p.time = _
    have he := h.deriv
    change deriv (fun t => sgn * (PDE.vecDot ξ (p.velocity - z0) -
      phaseCenter ξ b γ σ t) - Lb * ρ * (t - σ)) p.time = _ at he
    rw [he]
    ring
  have heq : lop B b (phaseBarrier sgn ξ z0 b γ σ Lb ρ) p =
      sgn * PDE.vecDot ξ (b p.position - b (γ p.time)) - Lb * ρ := by
    unfold lop transportedForwardOperatorOfTimeDiffusedCoefficient transportedForwardOperator
    rw [htime, phase_diffused_hessian, phase_velocity_gradient]
    simp only [matrixContraction, Matrix.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
    have hd : PDE.vecDot (b p.position) (sgn • ξ) =
        sgn * PDE.vecDot ξ (b p.position) := by
      unfold PDE.vecDot
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hd]
    have hs : PDE.vecDot ξ (b p.position - b (γ p.time)) =
        PDE.vecDot ξ (b p.position) - PDE.vecDot ξ (b (γ p.time)) := by
      simp only [PDE.vecDot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    rw [hs]
    ring
  refine ⟨heq, ?_⟩
  rw [heq]
  have hnorm : PDE.vecEuclideanNorm ξ = 1 := by
    simp [PDE.vecEuclideanNorm, hξ]
  have hLb : 0 ≤ Lb := by
    have hh := hb ξ 0
    have hn : PDE.vecEuclideanNorm (ξ - 0) = 1 := by simpa using hnorm
    rw [hn, mul_one] at hh
    exact (PDE.vecEuclideanNorm_nonneg _).trans hh
  have hdot : |PDE.vecDot ξ (b p.position - b (γ p.time))| ≤ Lb * ρ := by
    calc
      _ ≤ PDE.vecEuclideanNorm ξ * PDE.vecEuclideanNorm
          (b p.position - b (γ p.time)) := PDE.abs_vecDot_le_vecEuclideanNorm_mul _ _
      _ = PDE.vecEuclideanNorm (b p.position - b (γ p.time)) := by rw [hnorm, one_mul]
      _ ≤ Lb * PDE.vecEuclideanNorm (p.position - γ p.time) := hb _ _
      _ ≤ Lb * ρ := mul_le_mul_of_nonneg_left
        ((PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hρ).mp hv).le hLb
  rcases hsgn with rfl | rfl
  · nlinarith [le_abs_self (PDE.vecDot ξ (b p.position - b (γ p.time)))]
  · nlinarith [neg_le_abs (PDE.vecDot ξ (b p.position - b (γ p.time)))]

end HypoellipticAleksandrov.KineticAleksandrov.Decay

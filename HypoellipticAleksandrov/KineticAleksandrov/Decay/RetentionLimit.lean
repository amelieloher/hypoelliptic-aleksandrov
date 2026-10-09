module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.RetentionMatrix
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.SourceComparison
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.UniquenessMeasure
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonRadial
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierGeometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The coefficient-uniform retention rate bound

This elementary closing bound preserves the source's ellipticity signs and
literal radius dependence.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Decay

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter MeasureTheory
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped Topology MatrixOrder

/-- The explicit retention rate has the stated structural upper bound. -/
theorem retention_rate_uniform {d N : ℕ} (hN : 3 ≤ N)
    (lam Lam ρ H : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hρ : 0 < ρ) (hc : 0 < barrierC d N lam Lam) :
    barrierRate d N lam Lam ρ H ≤
      (2 * N * d * Lam + (N : ℝ) ^ 2 / barrierC d N lam Lam) * (ρ⁻¹ ^ 2 + H ^ 2) := by
  have _hN := hN
  have _hρ := hρ
  have hLam : 0 ≤ Lam := (hlam.trans_le hlamLam).le
  have hA : 0 ≤ 2 * (N : ℝ) * d * Lam := by positivity
  have hB : 0 ≤ (N : ℝ) ^ 2 / barrierC d N lam Lam := by positivity
  have h1 : 0 ≤ (2 * (N : ℝ) * d * Lam) * H ^ 2 := mul_nonneg hA (sq_nonneg H)
  have h2 : 0 ≤ ((N : ℝ) ^ 2 / barrierC d N lam Lam) * ρ⁻¹ ^ 2 :=
    mul_nonneg hB (sq_nonneg _)
  unfold barrierRate
  simp only [div_eq_mul_inv, inv_pow] at h1 h2 ⊢
  nlinarith only [h1, h2]


private theorem gradient_translate {d : ℕ} {f : PDE.Vec d → ℝ}
    (hf : ContDiff ℝ 2 f) (c x : PDE.Vec d) :
    PDE.classicalGradient (fun y => f (y - c)) x = PDE.classicalGradient f (x - c) := by
  have h := (hf.differentiable (by norm_num) (x - c)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).sub_const c)
  change HasFDerivAt (fun y => f (y - c))
    ((fderiv ℝ f (x - c)).comp (ContinuousLinearMap.id ℝ (PDE.Vec d))) x at h
  ext i
  simp only [PDE.classicalGradient_apply, h.fderiv,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]

private theorem hessian_translate {d : ℕ} {f : PDE.Vec d → ℝ}
    (hf : ContDiff ℝ 2 f) (c x : PDE.Vec d) :
    Hess (fun y => f (y - c)) x = Hess f (x - c) := by
  have hg : ContDiff ℝ 1 (PDE.classicalGradient f) := by
    apply contDiff_pi.mpr
    intro i
    exact (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have heq : (fun y => PDE.classicalGradient (fun w => f (w - c)) y) =
      (fun y => PDE.classicalGradient f (y - c)) := by
    funext y
    exact gradient_translate hf c y
  have h := (hg.differentiable (by norm_num) (x - c)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).sub_const c)
  change HasFDerivAt (fun y => PDE.classicalGradient f (y - c))
    ((fderiv ℝ (PDE.classicalGradient f) (x - c)).comp
      (ContinuousLinearMap.id ℝ (PDE.Vec d))) x at h
  ext i j
  change (fderiv ℝ (fun y => PDE.classicalGradient (fun w => f (w - c)) y) x
    (PDE.basisVec i)) j = _
  rw [heq]
  change (fderiv ℝ (fun y => PDE.classicalGradient f (y - c)) x
    (PDE.basisVec i)) j =
    (fderiv ℝ (PDE.classicalGradient f) (x - c) (PDE.basisVec i)) j
  rw [h.fderiv]
  rfl

private def movingBarrier {d : ℕ} (N : ℕ) (s rate τ : ℝ)
    (γ : ℝ → PDE.Vec d) (p : TimeVelocity d) : ℝ :=
  Real.exp (-rate * (τ - p.1)) * barrier N s (p.2 - γ p.1)

private theorem movingBarrier_time_derivative {d N : ℕ} (hN : 3 ≤ N)
    (s rate τ t : ℝ) (γ : ℝ → PDE.Vec d) (y : PDE.Vec d)
    (hγ : DifferentiableAt ℝ γ t) :
    HasDerivAt (fun r => movingBarrier N s rate τ γ (r, y))
      (Real.exp (-rate * (τ - t)) *
        (rate * barrier N s (y - γ t) -
          PDE.vecDot (deriv γ t) (PDE.classicalGradient (barrier N s) (y - γ t)))) t := by
  have hf := (retention_barrier_contDiff (d := d) hN s).differentiable (by norm_num)
  have hpath := hγ.hasDerivAt.const_sub y
  have hcomp := (hf (y - γ t)).hasFDerivAt.comp_hasDerivAt t hpath
  have he := (((hasDerivAt_id t).const_sub τ).const_mul (-rate)).exp
  have h := he.mul hcomp
  refine h.congr_deriv ?_
  simp only [id_eq, Function.comp_apply]
  rw [PDE.fderiv_apply_eq_vecDot_classicalGradient]
  unfold PDE.vecDot
  simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
  have hc : (∑ i, PDE.classicalGradient (barrier N s) (y - γ t) i * deriv γ t i) =
      ∑ i, deriv γ t i * PDE.classicalGradient (barrier N s) (y - γ t) i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hc]
  ring


/-- Constant extension of a continuous curve on an ordered interval is continuous. -/
theorem continuous_clippedCurve {d : ℕ} {γ : ℝ → PDE.Vec d} {σ τ : ℝ}
    (hστ : σ ≤ τ) (hγ : ContinuousOn γ (Icc σ τ)) :
    Continuous (clippedCurve γ σ τ) := by
  apply hγ.comp_continuous (show Continuous (fun r : ℝ => max σ (min τ r)) by fun_prop)
  intro r
  exact ⟨le_max_left _ _, max_le hστ (min_le_left _ _)⟩

private theorem movingBarrier_hessian {d N : ℕ} (hN : 3 ≤ N)
    (s rate τ : ℝ) (γ : ℝ → PDE.Vec d) (p : TimeVelocity d) :
    scalarSpatialHessian (movingBarrier N s rate τ γ) p =
      Real.exp (-rate * (τ - p.1)) • Hess (barrier N s) (p.2 - γ p.1) := by
  have hf : ContDiff ℝ 2 (fun y : PDE.Vec d => barrier N s (y - γ p.1)) :=
    (retention_barrier_contDiff hN s).comp (contDiff_id.sub contDiff_const)
  change sliceHessian (fun y => Real.exp (-rate * (τ - p.1)) *
    barrier N s (y - γ p.1)) p.2 = _
  rw [sliceHessian_const_mul _ hf.contDiffAt]
  change _ • Hess (fun y => barrier N s (y - γ p.1)) p.2 = _
  rw [hessian_translate (retention_barrier_contDiff hN s)]

private theorem movingBarrier_subsolution {d N : ℕ} (hN : 3 ≤ N)
    (lam Lam s H τ : ℝ) (hs : 0 < s) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hc : 0 < barrierC d N lam Lam) (B : CoefficientField d)
    (hB : IsSectionTwoCoefficient lam Lam B) (γ : ℝ → PDE.Vec d)
    (p : TimeVelocity d) (hγ : DifferentiableAt ℝ γ p.1)
    (hspd : PDE.vecEuclideanNorm (deriv γ p.1) ≤ H) :
    0 ≤ scalarParabolicOperator B 0
      (movingBarrier N s (barrierRate d N lam Lam s H) τ γ) p := by
  have htime := movingBarrier_time_derivative hN s (barrierRate d N lam Lam s H)
    τ p.1 γ p.2 hγ
  have hineq := retention_barrier_drift_inequality hN lam Lam s H hs hlam hlamLam hc
    (B p.1 p.2) (hB.2.2.2.1 p.1 p.2) (hB.2.2.2.2.1 p.1 p.2)
    (hB.2.2.2.2.2 p.1 p.2) (deriv γ p.1) (p.2 - γ p.1) hspd
  unfold scalarParabolicOperator scalarTimeDerivative
  rw [htime.deriv, movingBarrier_hessian hN, matrixContraction_smul_right]
  simp only [Pi.zero_apply, PDE.vecDot, zero_mul, Finset.sum_const_zero, add_zero]
  have he : 0 ≤ Real.exp (-barrierRate d N lam Lam s H * (τ - p.1)) := (Real.exp_pos _).le
  convert mul_nonneg he (sub_nonneg.mpr hineq) using 1
  unfold PDE.vecDot
  ring


private theorem lifted_operator {d : ℕ} (B : CoefficientField d)
    (b : PDE.Vec d → PDE.Vec d) (V : TimeVelocity d → ℝ) (p : KineticPoint d) :
    transportedForwardOperator (zIndependentCoefficient B) b
      (fun q => V (q.time, q.position)) p = scalarParabolicOperator B 0 V
        (p.time, p.position) := by
  unfold transportedForwardOperator scalarParabolicOperator kineticTimeDerivative
    diffusedHessian scalarTimeDerivative scalarSpatialHessian kineticVelocityGradient
    scalarSpatialGradient kineticPositionGradient
  simp [PDE.classicalGradient, PDE.vecDot]

private theorem scalar_difference_operator {d : ℕ} (B : CoefficientField d)
    (U V : TimeVelocity d → ℝ) (p : TimeVelocity d)
    (hUt : DifferentiableAt ℝ (fun t => U (t, p.2)) p.1)
    (hVt : DifferentiableAt ℝ (fun t => V (t, p.2)) p.1)
    (hUy : ContDiffAt ℝ 2 (fun y => U (p.1, y)) p.2)
    (hVy : ContDiffAt ℝ 2 (fun y => V (p.1, y)) p.2) :
    scalarParabolicOperator B 0 (fun q => U q - V q) p =
      scalarParabolicOperator B 0 U p - scalarParabolicOperator B 0 V p := by
  have htime := deriv_fun_sub hUt hVt
  have hhess : scalarSpatialHessian (fun q => U q - V q) p =
      scalarSpatialHessian U p - scalarSpatialHessian V p := by
    have hneg := sliceHessian_const_mul (-1) hVy
    have hadd := sliceHessian_add hUy ((contDiffAt_const (c := (-1 : ℝ))).mul hVy)
    have heq : (fun y => U (p.1, y) - V (p.1, y)) =
        (fun y => U (p.1, y) + (-1) * V (p.1, y)) := by
      funext y
      ring
    change sliceHessian (fun y => U (p.1, y) - V (p.1, y)) p.2 = _
    rw [heq, hadd, hneg]
    simp only [neg_one_smul, sub_eq_add_neg]
    rfl
  unfold scalarParabolicOperator scalarTimeDerivative
  rw [htime, hhess]
  simp only [matrixContraction, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib,
    Pi.zero_apply, PDE.vecDot, zero_mul, Finset.sum_const_zero, add_zero]
  ring

private theorem lifted_difference_subsolution {d : ℕ} (B : CoefficientField d)
    (U V : TimeVelocity d → ℝ) (p : KineticPoint d)
    (hUt : DifferentiableAt ℝ (fun t => U (t, p.position)) p.time)
    (hVt : DifferentiableAt ℝ (fun t => V (t, p.position)) p.time)
    (hUy : ContDiffAt ℝ 2 (fun y => U (p.time, y)) p.position)
    (hVy : ContDiffAt ℝ 2 (fun y => V (p.time, y)) p.position)
    (hU : 0 ≤ scalarParabolicOperator B 0 U (p.time, p.position))
    (hV : scalarParabolicOperator B 0 V (p.time, p.position) = 0) :
    0 ≤ transportedForwardOperator (zIndependentCoefficient B) (fun _ => 0)
      (fun q => U (q.time, q.position) - V (q.time, q.position)) p := by
  have hlift := lifted_operator B (fun _ => 0) (fun x => U x - V x) p
  have hdiff := scalar_difference_operator B U V (p.time, p.position) hUt hVt hUy hVy
  rw [hlift, hdiff, hV, sub_zero]
  exact hU

private theorem comparison_at_center {d N : ℕ} (hN : 3 ≤ N)
    (lam Lam s H ρ : ℝ) (hs : 0 < s) (hsρ : s < ρ)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam) (hc : 0 < barrierC d N lam Lam)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (γ : ℝ → PDE.Vec d) (hγ : Continuous γ)
    (n : ℕ) (r : Fin (n + 2) → ℝ) (hr : StrictMono r)
    (hγpieces : ∀ i : Fin (n + 1), ContDiffOn ℝ 1 γ (Icc (r i.castSucc) (r i.succ)))
    (hspd : HasCurveSpeedOn H γ (r 0) (r (Fin.last (n + 1))))
    (F : BoundedBorel (PDE.Vec d)) (V : TimeVelocity d → ℝ)
    (hV : ParabolicProbe.IsClassicalScalarTerminalSolution (PDE.euclideanBall 0 ρ) γ
      (zIndependentCoefficient B) (r (Fin.last (n + 1))) F V)
    (hF : ∀ y, barrier N s (y - γ (r (Fin.last (n + 1)))) ≤ F y) :
    Real.exp (-barrierRate d N lam Lam s H * (r (Fin.last (n + 1)) - r 0)) ≤
      V (r 0, γ (r 0)) := by
  let τ := r (Fin.last (n + 1))
  let rate := barrierRate d N lam Lam s H
  let U := movingBarrier N s rate τ γ
  let W : KineticPoint d → ℝ := fun p => U (p.time, p.position) - V (p.time, p.position)
  have hρ : 0 < ρ := hs.trans hsρ
  have hopen : IsOpen (ParabolicProbe.scalarPastOpenCylinder (PDE.euclideanBall 0 ρ) γ τ) := by
    have heq : ParabolicProbe.scalarPastOpenCylinder (PDE.euclideanBall 0 ρ) γ τ =
        {p : TimeVelocity d | p.1 < τ ∧ PDE.vecNormSq (p.2 - γ p.1) < ρ ^ 2} := by
      ext p
      simp only [ParabolicProbe.scalarPastOpenCylinder, Set.mem_ofPred_eq,
        mem_movingDomain_euclideanBall_iff, add_zero]
    rw [heq]
    exact (isOpen_lt continuous_fst continuous_const).inter
      (isOpen_lt (PDE.contDiff_vecNormSq.continuous.comp
        (continuous_snd.sub (hγ.comp continuous_fst))) continuous_const)
  have hVc : ContinuousOn V
      (ParabolicProbe.scalarPastClosedCylinder (PDE.euclideanBall 0 ρ) γ τ) := hV.2.1
  have hVjet : ∀ i : Fin (n + 1), ∀ p ∈
      maximumOpenTube (PDE.euclideanBall 0 ρ) γ (r i.castSucc) (r i.succ),
      ContDiffAt ℝ 2 V (p.time, p.position) := by
    intro i p hp
    have hpt : p.time < τ := hp.1.2.trans_le (hr.monotone (Fin.le_last _))
    have hmem : (p.time, p.position) ∈
        ParabolicProbe.scalarPastOpenCylinder (PDE.euclideanBall 0 ρ) γ τ := ⟨hpt, hp.2⟩
    exact ((hV.2.2.1 _ hmem).contDiffAt (hopen.mem_nhds hmem)).of_le (by norm_num)
  have hγd : ∀ i : Fin (n + 1), ∀ p ∈
      maximumOpenTube (PDE.euclideanBall 0 ρ) γ (r i.castSucc) (r i.succ),
      DifferentiableAt ℝ γ p.time := by
    intro i p hp
    exact ((hγpieces i p.time ⟨hp.1.1.le, hp.1.2.le⟩).contDiffAt
      (Icc_mem_nhds hp.1.1 hp.1.2)).differentiableAt (by norm_num)
  have hUjet : ∀ i : Fin (n + 1), ∀ p ∈
      maximumOpenTube (PDE.euclideanBall 0 ρ) γ (r i.castSucc) (r i.succ),
      DifferentiableAt ℝ (fun t => U (t, p.position)) p.time ∧
      ContDiffAt ℝ 2 (fun y => U (p.time, y)) p.position := by
    intro i p hp
    refine ⟨(movingBarrier_time_derivative hN s rate τ p.time γ p.position
      (hγd i p hp)).differentiableAt, ?_⟩
    change ContDiffAt ℝ 2 (fun y => Real.exp (-rate * (τ - p.time)) *
      barrier N s (y - γ p.time)) p.position
    exact (contDiffAt_const (c := Real.exp (-rate * (τ - p.time)))).mul
      ((retention_barrier_contDiff hN s).contDiffAt.comp p.position
        (contDiffAt_id.sub (contDiffAt_const (c := γ p.time))))
  have hmax : ∀ p ∈ maximumClosedTube (PDE.euclideanBall 0 ρ) γ (r 0) τ, W p ≤ 0 := by
    apply movingDomain_maximumPrinciple (B := zIndependentCoefficient B)
      (drift := fun _ => 0) (Or.inl ⟨0, ρ, hρ, rfl⟩) n r hr hγ.continuousOn
    · have hUc : Continuous (fun p : KineticPoint d => U (p.time, p.position)) := by
        dsimp [U, movingBarrier]
        apply Continuous.mul
        · exact (continuous_const.mul (continuous_const.sub continuous_time)).rexp
        · exact (retention_barrier_contDiff hN s).continuous.comp
            (continuous_position.sub (hγ.comp continuous_time))
      exact hUc.continuousOn.sub (hVc.comp (continuous_time.prodMk continuous_position).continuousOn
        (fun p hp => ⟨hp.1.2, hp.2⟩))
    · exact Or.inl (fun p _ z => rfl)
    · intro i p hp
      have hj := hVjet i p hp
      have ht : DifferentiableAt ℝ (fun t => V (t, p.position)) p.time :=
        (hj.differentiableAt (by norm_num)).comp p.time (by fun_prop)
      have hy : ContDiffAt ℝ 2 (fun y => V (p.time, y)) p.position :=
        hj.comp p.position (contDiffAt_const.prodMk contDiffAt_id)
      exact ⟨(hUjet i p hp).1.sub ht, (hUjet i p hp).2.sub hy,
        differentiableAt_const (U (p.time, p.position) - V (p.time, p.position))⟩
    · intro i p hp
      exact (posDef_of_loewner_lower hlam (hB.2.2.2.2.1 p.time p.position)).posSemidef
    · intro i p hp
      have hj := hVjet i p hp
      have ht : DifferentiableAt ℝ (fun t => V (t, p.position)) p.time :=
        (hj.differentiableAt (by norm_num)).comp p.time (by fun_prop)
      have hy : ContDiffAt ℝ 2 (fun y => V (p.time, y)) p.position :=
        hj.comp p.position (contDiffAt_const.prodMk contDiffAt_id)
      have hspd' := hspd p.time
        ⟨(hr.monotone (Fin.zero_le _)).trans_lt hp.1.1,
          hp.1.2.trans_le (hr.monotone (Fin.le_last _))⟩ (hγd i p hp)
      have hsub := movingBarrier_subsolution hN lam Lam s H τ hs hlam hlamLam hc
        B hB γ (p.time, p.position) (hγd i p hp) hspd'
      have hsol := hV.2.2.2.1 (p.time, p.position)
        ⟨hp.1.2.trans_le (hr.monotone (Fin.le_last _)), hp.2⟩
      change scalarParabolicOperator B 0 V (p.time, p.position) = 0 at hsol
      change 0 ≤ scalarParabolicOperator B 0 U (p.time, p.position) at hsub
      exact lifted_difference_subsolution B U V p (hUjet i p hp).1 ht
        (hUjet i p hp).2 hy hsub hsol

    · intro p hp hpt
      have ht : V (p.time, p.position) = F p.position := hV.2.2.2.2.1 _
        ⟨hpt, by simpa only [hpt] using hp.2⟩
      change U (p.time, p.position) - V (p.time, p.position) ≤ 0
      rw [ht]
      dsimp [U, movingBarrier]
      simp only [hpt, τ, sub_self, mul_zero, Real.exp_zero, one_mul]
      exact sub_nonpos.mpr (hF p.position)
    · intro p hp hlat
      have hv0 : V (p.time, p.position) = 0 := hV.2.2.2.2.2 _ ⟨hp.1.2, hlat⟩
      have hsq := vecNormSq_eq_of_mem_frontier_movingDomain hlat
      simp only [add_zero] at hsq
      have hout : p.position - γ p.time ∉ PDE.euclideanBall 0 s := by
        change ¬ PDE.vecNormSq (p.position - γ p.time - 0) < s ^ 2
        rw [sub_zero, hsq]
        nlinarith
      have hψ := (retention_polynomial_barrier hN s hs).2.2.2.2 _ hout
      change U (p.time, p.position) - V (p.time, p.position) ≤ 0
      simp only [U, movingBarrier, hψ.1, mul_zero, hv0, sub_zero, le_refl]
  have hmem : (⟨r 0, γ (r 0), 0⟩ : KineticPoint d) ∈
      maximumClosedTube (PDE.euclideanBall 0 ρ) γ (r 0) τ := by
    refine ⟨⟨le_rfl, hr.monotone (Fin.zero_le _)⟩, subset_closure ?_⟩
    rw [mem_movingDomain_euclideanBall_iff]
    simp only [add_zero, sub_self]
    simpa [PDE.vecNormSq, PDE.vecDot] using sq_pos_of_pos hρ
  have h := hmax _ hmem
  have hψ0 := (retention_polynomial_barrier (d := d) hN s hs).2.2.1
  dsimp [W, U, movingBarrier] at h
  rw [sub_self, hψ0, mul_one] at h
  exact sub_nonpos.mp h


private theorem master_mass_eq_marginal_mass {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (hΩ : MeasurableSet Ω) (K : MovingFiberKernel Ω γ)
    (σ τ : ℝ) (hστ : σ ≤ τ) (v z : PDE.Vec d) (hv : v ∈ movingDomain Ω γ σ)
    (hfirst : (parabolicMarginalKernel K hΩ σ τ hστ) ⟨v, hv⟩ =
      (K.fiberFirstMarginal hΩ σ τ hστ) (evolutionStateOfPosition Ω γ σ ⟨v, hv⟩ z)) :
    (parabolicMarginalKernel K hΩ σ τ hστ ⟨v, hv⟩) univ =
      K.master (movingQuery σ τ hστ v z hv) univ := by
  have hmap := K.map_fiberFirstMarginal_eq_firstMarginal hΩ σ τ hστ
    (evolutionStateOfPosition Ω γ σ ⟨v, hv⟩ z)
  rw [← hfirst] at hmap
  have hq : evolutionQueryOfState Ω γ σ τ hστ
      (evolutionStateOfPosition Ω γ σ ⟨v, hv⟩ z) = movingQuery σ τ hστ v z hv := rfl
  rw [hq] at hmap
  have h := congrArg (fun μ : Measure (PDE.Vec d) => μ univ) hmap
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ,
    MovingFiberKernel.firstMarginal, ProbabilityTheory.Kernel.fst_apply,
    Measure.map_apply measurable_fst MeasurableSet.univ] at h
  simpa only [preimage_univ] using h

private theorem prelimit_of_partition {d N : ℕ} (hN : 3 ≤ N)
    (lam Lam s H ρ : ℝ) (hs : 0 < s) (hsρ : s < ρ)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam) (hc : 0 < barrierC d N lam Lam)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (γ : ℝ → PDE.Vec d) (hγ : Continuous γ)
    (n : ℕ) (r : Fin (n + 2) → ℝ) (hr : StrictMono r)
    (hγpieces : ∀ i : Fin (n + 1), ContDiffOn ℝ 1 γ (Icc (r i.castSucc) (r i.succ)))
    (hspd : HasCurveSpeedOn H γ (r 0) (r (Fin.last (n + 1))))
    (K : MovingFiberKernel (PDE.euclideanBall 0 ρ) γ)
    (hpar : HasParabolicMarginalBundle (PDE.euclideanBall 0 ρ) γ
      (PDE.isOpen_euclideanBall 0 ρ).measurableSet (zIndependentCoefficient B) K)
    (z : PDE.Vec d)
    (hv : γ (r 0) ∈ movingDomain (PDE.euclideanBall 0 ρ) γ (r 0)) :
    ENNReal.ofReal (Real.exp (-barrierRate d N lam Lam s H *
      (r (Fin.last (n + 1)) - r 0))) ≤
      K.master (movingQuery (r 0) (r (Fin.last (n + 1)))
        (hr.monotone (Fin.zero_le _)) (γ (r 0)) z hv) univ := by
  let τ := r (Fin.last (n + 1))
  have hρ : 0 < ρ := hs.trans hsρ
  have hC := PDE.isCompact_euclideanClosedBall (γ τ) hs.le
  have hopen := isOpen_movingDomain (PDE.isOpen_euclideanBall 0 ρ) (γ := γ) τ
  have hsub : PDE.euclideanClosedBall (γ τ) s ⊆
      movingDomain (PDE.euclideanBall 0 ρ) γ τ := by
    intro y hy
    have hball := PDE.euclideanClosedBall_subset_euclideanBall hs.le hsρ hy
    rw [mem_movingDomain_euclideanBall_iff]
    simpa only [add_zero, PDE.euclideanBall, PDE.euclideanSqDist,
      Set.mem_ofPred_eq] using hball
  obtain ⟨φ, hφ, hφc, hφsupp, hφbound, hφone⟩ := exists_smooth_cutoff hC hopen hsub
  let F : BoundedBorel (PDE.Vec d) :=
    ⟨φ, hφ.continuous.measurable, ⟨1, zero_le_one, fun y => by
      rw [abs_of_nonneg (hφbound y).1]
      exact (hφbound y).2⟩⟩
  obtain ⟨Q, hfirst, _hQid, _hQpos, _hQsub, _hQcomp, hrepr,
    _hmeas, _hend, _hcomp, hsolve⟩ := hpar (fun _ _ _ _ => rfl)
  obtain ⟨V, hV, hVeval, _hunique⟩ := hsolve τ F ⟨hφ, hφc, hφsupp⟩
  have hdom : ∀ y, barrier N s (y - γ τ) ≤ F y := by
    intro y
    by_cases hy : y - γ τ ∈ PDE.euclideanBall 0 s
    · have hc : y ∈ PDE.euclideanClosedBall (γ τ) s := by
        change PDE.vecNormSq (y - γ τ) ≤ s ^ 2
        change PDE.vecNormSq (y - γ τ - 0) < s ^ 2 at hy
        simpa only [sub_zero] using hy.le
      change barrier N s (y - γ τ) ≤ φ y
      rw [hφone y hc]
      exact ((retention_polynomial_barrier (d := d) hN s hs).2.1 _).2
    · rw [(retention_polynomial_barrier hN s hs).2.2.2.2 _ hy |>.1]
      exact (hφbound y).1
  have hcenter := comparison_at_center hN lam Lam s H ρ hs hsρ hlam hlamLam hc
    B hB γ hγ n r hr hγpieces hspd F V hV hdom
  have heval := hVeval (r 0) (hr.monotone (Fin.zero_le _)) ⟨γ (r 0), hv⟩
  rw [hrepr] at heval
  rw [heval] at hcenter
  apply (ENNReal.ofReal_le_ofReal hcenter).trans
  have hint := integral_le_measure (μ := parabolicMarginalKernel K
      (PDE.isOpen_euclideanBall 0 ρ).measurableSet (r 0) τ
        (hr.monotone (Fin.zero_le _)) ⟨γ (r 0), hv⟩)
    (s := univ) (f := fun y => (terminalPositionDatum F) y)
    (fun y _ => (hφbound y.1).2) (fun y hy => (hy (mem_univ y)).elim)
  rw [master_mass_eq_marginal_mass (PDE.isOpen_euclideanBall 0 ρ).measurableSet
    K (r 0) τ (hr.monotone (Fin.zero_le _)) (γ (r 0)) z hv
      (hfirst _ _ _ _ z)] at hint
  exact hint


private theorem endpoint_master_mass {d : ℕ} {Ω : Set (PDE.Vec d)}
    {γ : ℝ → PDE.Vec d} (hΩ : MeasurableSet Ω) (B : CoefficientField d)
    (K : MovingFiberKernel Ω γ)
    (hpar : HasParabolicMarginalBundle Ω γ hΩ (zIndependentCoefficient B) K)
    (σ : ℝ) (v z : PDE.Vec d) (hv : v ∈ movingDomain Ω γ σ) :
    K.master (movingQuery σ σ le_rfl v z hv) univ = 1 := by
  obtain ⟨_Q, hfirst, _hQid, _hQpos, _hQsub, _hQcomp, _hrepr,
    _hmeas, hend, _hcomp, _hsolve⟩ := hpar (fun _ _ _ _ => rfl)
  rw [← master_mass_eq_marginal_mass hΩ K σ σ le_rfl v z hv
    (hfirst σ σ le_rfl ⟨v, hv⟩ z), hend σ]
  simp

private theorem barrierC_pos_of_choice {d N : ℕ} (hN : 3 ≤ N) (lam Lam : ℝ)
    (hchoice : 2 * (N - 1 : ℕ) * lam > (d : ℝ) * Lam) :
    0 < barrierC d N lam Lam := by
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hp := mul_pos hNp
    (sub_pos.mpr hchoice : 0 < 2 * (N - 1 : ℕ) * lam - (d : ℝ) * Lam)
  unfold barrierC
  nlinarith [hp]

/-- Every interior barrier radius gives the source prelimit retention bound. -/
theorem moving_ball_retention_prelimit (d : ℕ) (hd : 1 ≤ d)
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam) :
      ∀ (m Lb : ℝ) (D : Set (PDE.Vec d)) (B : CoefficientField d)
        (b : PDE.Vec d → PDE.Vec d), SourceSetting lam Lam m Lb D B b →
      ∀ (σ τ H ρ : ℝ) (γ : ℝ → PDE.Vec d), σ ≤ τ → 0 < ρ →
        PiecewiseC1On γ σ τ → HasCurveSpeedOn H γ σ τ →
        (∀ r ∈ Icc σ τ, PDE.euclideanBall (γ r) ρ ⊆ D) →
      ∀ (S : TerminalOperatorFamily (PDE.euclideanBall 0 ρ) (clippedCurve γ σ τ))
        (K : MovingFiberKernel (PDE.euclideanBall 0 ρ) (clippedCurve γ σ τ)),
        RealizesTerminalEvolution (PDE.euclideanBall 0 ρ) (clippedCurve γ σ τ)
          (PDE.isOpen_euclideanBall 0 ρ).measurableSet (zIndependentCoefficient B) b S K →
        HasParabolicMarginalBundle (PDE.euclideanBall 0 ρ) (clippedCurve γ σ τ)
          (PDE.isOpen_euclideanBall 0 ρ).measurableSet (zIndependentCoefficient B) K →
      ∀ z, ∀ (hστ : σ ≤ τ)
        (hv : γ σ ∈ movingDomain (PDE.euclideanBall 0 ρ) (clippedCurve γ σ τ) σ),
      ∀ (N : ℕ), 3 ≤ N → 2 * (N - 1 : ℕ) * lam > (d : ℝ) * Lam →
      ∀ (s : ℝ), 0 < s → s < ρ →
        ENNReal.ofReal (Real.exp (-barrierRate d N lam Lam s H * (τ - σ))) ≤
          K.master (movingQuery σ τ hστ (γ σ) z hv) univ := by
  have _hd := hd
  intro m Lb D B b hsetting σ τ H ρ γ hστ hρ hpc hspd hfit S K hreal hpar
    z hστ' hv N hN hchoice s hs hsρ
  by_cases heq : σ = τ
  · subst τ
    rw [endpoint_master_mass (PDE.isOpen_euclideanBall 0 ρ).measurableSet
      B K hpar σ (γ σ) z hv]
    simp
  · have hστlt : σ < τ := lt_of_le_of_ne hστ heq
    obtain ⟨n, r, hr, hr0, hrlast, hpieces⟩ := hpc.2.resolve_left heq
    let δ := clippedCurve γ σ τ
    have hδcont : Continuous δ := continuous_clippedCurve hστ hpc.1
    have hδpieces : ∀ i : Fin (n + 1), ContDiffOn ℝ 1 δ
        (Icc (r i.castSucc) (r i.succ)) := by
      intro i
      apply (hpieces i).congr
      intro t ht
      apply clippedCurve_eq_of_mem
      constructor
      · rw [← hr0]
        exact (hr.monotone (Fin.zero_le _)).trans ht.1
      · rw [← hrlast]
        exact ht.2.trans (hr.monotone (Fin.le_last _))
    have hδspd : HasCurveSpeedOn H δ (r 0) (r (Fin.last (n + 1))) := by
      intro t ht hdiff
      have hti : t ∈ Ioo σ τ := by simpa only [hr0, hrlast] using ht
      have hev : δ =ᶠ[𝓝 t] γ := by
        filter_upwards [Ioo_mem_nhds hti.1 hti.2] with r hr'
        exact clippedCurve_eq_of_mem γ ⟨hr'.1.le, hr'.2.le⟩
      rw [hev.deriv_eq]
      exact hspd t hti (hev.differentiableAt_iff.mp hdiff)
    have hδ0 : δ (r 0) = γ σ := by
      rw [hr0]
      exact clippedCurve_eq_of_mem γ ⟨le_rfl, hστ⟩
    have hvδ : δ (r 0) ∈ movingDomain (PDE.euclideanBall 0 ρ) δ (r 0) := by
      rw [hδ0, hr0]
      exact hv
    have hbound := prelimit_of_partition hN lam Lam s H ρ hs hsρ hlam hlamLam
      (barrierC_pos_of_choice hN lam Lam hchoice) B hsetting.1 δ hδcont n r hr
      hδpieces hδspd K hpar z hvδ
    simpa only [hr0, hrlast, δ, clippedCurve_eq_of_mem γ ⟨le_rfl, hστ⟩] using hbound


/-- Passing the interior radius to the tube radius gives the exact source limiting rate. -/
theorem moving_ball_retention_at_radius (d : ℕ) (hd : 1 ≤ d)
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam) :
      ∀ (m Lb : ℝ) (D : Set (PDE.Vec d)) (B : CoefficientField d)
        (b : PDE.Vec d → PDE.Vec d), SourceSetting lam Lam m Lb D B b →
      ∀ (σ τ H ρ : ℝ) (γ : ℝ → PDE.Vec d), σ ≤ τ → 0 < ρ →
        PiecewiseC1On γ σ τ → HasCurveSpeedOn H γ σ τ →
        (∀ r ∈ Icc σ τ, PDE.euclideanBall (γ r) ρ ⊆ D) →
      ∀ (S : TerminalOperatorFamily (PDE.euclideanBall 0 ρ) (clippedCurve γ σ τ))
        (K : MovingFiberKernel (PDE.euclideanBall 0 ρ) (clippedCurve γ σ τ)),
        RealizesTerminalEvolution (PDE.euclideanBall 0 ρ) (clippedCurve γ σ τ)
          (PDE.isOpen_euclideanBall 0 ρ).measurableSet (zIndependentCoefficient B) b S K →
        HasParabolicMarginalBundle (PDE.euclideanBall 0 ρ) (clippedCurve γ σ τ)
          (PDE.isOpen_euclideanBall 0 ρ).measurableSet (zIndependentCoefficient B) K →
      ∀ z, ∀ (hστ : σ ≤ τ)
        (hv : γ σ ∈ movingDomain (PDE.euclideanBall 0 ρ) (clippedCurve γ σ τ) σ),
      ∀ (N : ℕ), 3 ≤ N → 2 * (N - 1 : ℕ) * lam > (d : ℝ) * Lam →
        ENNReal.ofReal (Real.exp (-barrierRate d N lam Lam ρ H * (τ - σ))) ≤
          K.master (movingQuery σ τ hστ (γ σ) z hv) univ := by
  intro m Lb D B b hsetting σ τ H ρ γ hστ hρ hpc hspd hfit S K hreal hpar
    z hστ' hv N hN hchoice
  have hpre := moving_ball_retention_prelimit d hd lam Lam hlam hlamLam
    m Lb D B b hsetting σ τ H ρ γ hστ hρ hpc hspd hfit S K hreal hpar
    z hστ' hv N hN hchoice
  have hcont : ContinuousAt
      (fun s => Real.exp (-barrierRate d N lam Lam s H * (τ - σ))) ρ := by
    unfold barrierRate
    fun_prop (disch := positivity)
  have hlim := ENNReal.tendsto_ofReal (hcont.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[<] ρ ≤ 𝓝 ρ))
  apply le_of_tendsto hlim
  have hpos : ∀ᶠ s in 𝓝[<] ρ, 0 < s :=
    (lt_mem_nhds hρ).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpos, self_mem_nhdsWithin] with s hs hsρ
  exact hpre s hs hsρ


/-- The exact source prelimit comparison surface for the supplied joint evolution. -/
theorem retention_comparison_prelimit (d : ℕ) (hd : 1 ≤ d)
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam) :
      ∀ (m Lb : ℝ) (D : Set (PDE.Vec d)) (B : CoefficientField d)
        (b : PDE.Vec d → PDE.Vec d), SourceSetting lam Lam m Lb D B b →
      ∀ (σ τ H ρ : ℝ) (γ : ℝ → PDE.Vec d), σ ≤ τ → 0 < ρ →
        PiecewiseC1On γ σ τ → HasCurveSpeedOn H γ σ τ →
        (∀ r ∈ Icc σ τ, PDE.euclideanBall (γ r) ρ ⊆ D) →
      ∀ (S : TerminalOperatorFamily (PDE.euclideanBall 0 ρ) (clippedCurve γ σ τ))
        (K : MovingFiberKernel (PDE.euclideanBall 0 ρ) (clippedCurve γ σ τ)),
        RealizesTerminalEvolution (PDE.euclideanBall 0 ρ) (clippedCurve γ σ τ)
          (PDE.isOpen_euclideanBall 0 ρ).measurableSet (zIndependentCoefficient B) b S K →
        HasParabolicMarginalBundle (PDE.euclideanBall 0 ρ) (clippedCurve γ σ τ)
          (PDE.isOpen_euclideanBall 0 ρ).measurableSet (zIndependentCoefficient B) K →
      ∀ z, ∀ (hστ : σ ≤ τ)
        (hv : γ σ ∈ movingDomain (PDE.euclideanBall 0 ρ) (clippedCurve γ σ τ) σ),
      ∀ (N : ℕ), 3 ≤ N → 2 * (N - 1 : ℕ) * lam > (d : ℝ) * Lam →
      ∀ (s : ℝ), 0 < s → s < ρ →
        ENNReal.ofReal (Real.exp (-barrierRate d N lam Lam s H * (τ - σ))) ≤
          K.master (movingQuery σ τ hστ (γ σ) z hv) univ := by
  exact moving_ball_retention_prelimit d hd lam Lam hlam hlamLam

end HypoellipticAleksandrov.KineticAleksandrov.Decay

module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.Retention
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.MinorantScaling
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonRadial
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierGeometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Scalar polynomial comparison for the minorant mass floor

The retention barrier is compared directly to the supplied scalar solution.
This avoids assuming existence of a separate normalized joint evolution.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Decay

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter MeasureTheory
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped Topology MatrixOrder

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


/-- The stationary scalar retention barrier gives the normalized mass-floor rate. -/
theorem minorant_scalar_barrier_floor {d N : ℕ} (hN : 3 ≤ N)
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hc : 0 < barrierC d N lam Lam) (B : CoefficientField d)
    (hB : IsSectionTwoCoefficient lam Lam B)
    (F : BoundedBorel (PDE.Vec d)) (V : TimeVelocity d → ℝ)
    (hV : ParabolicProbe.IsClassicalScalarTerminalSolution (PDE.euclideanBall 0 4)
      stationary (zIndependentCoefficient B) 0 F V)
    (hF : ∀ y, barrier N 3 y ≤ F y) :
    Real.exp (-(2 * N * d * Lam) / 9) ≤ V (-1, 0) := by
  let r : Fin (0 + 2) → ℝ := ![-1, 0]
  have hr : StrictMono r := by
    intro i j hij
    have hijv : i.val < j.val := hij
    have hi : i = 0 := by apply Fin.ext; change i.val = 0; omega
    have hj : j = 1 := by apply Fin.ext; change j.val = 1; omega
    subst i j
    norm_num [r]
  have hpieces : ∀ i : Fin (0 + 1), ContDiffOn ℝ 1
      (stationary : ℝ → PDE.Vec d) (Icc (r i.castSucc) (r i.succ)) :=
    fun _ => contDiffOn_const
  have hspd : HasCurveSpeedOn 0 (stationary : ℝ → PDE.Vec d) (r 0)
      (r (Fin.last (0 + 1))) := by
    intro t _ _
    change PDE.vecEuclideanNorm (deriv (fun _ : ℝ => (0 : PDE.Vec d)) t) ≤ 0
    rw [deriv_const]
    simp [PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot]
  have h := comparison_at_center hN lam Lam 3 0 4 (by norm_num) (by norm_num)
    hlam hlamLam hc B hB stationary continuous_const 0 r hr hpieces hspd F V hV
    (by simpa only [stationary, sub_zero] using hF)
  change Real.exp (-barrierRate d N lam Lam 3 0 * (0 - (-1))) ≤ V (-1, 0) at h
  norm_num [barrierRate, neg_div] at h ⊢
  exact h

end HypoellipticAleksandrov.KineticAleksandrov.Decay

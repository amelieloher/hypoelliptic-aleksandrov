module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceCanonical
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.MinorantScaling
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.MaxPrinciple
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonCalculus

/-! # Scalar terminal comparison on a velocity ball

The comparison lemma is an internal maximum-principle tool for the exponential
short-time barrier. Continuity passes the initial time face.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay

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


/-- A smooth supersolution dominates the supplied scalar terminal solution on a ball. -/
theorem ball_terminal_comparison {d : ℕ} {lam Lam σ τ R : ℝ}
    (v₀ : PDE.Vec d) (hR : 0 < R) (hστ : σ < τ) (hlam : 0 < lam)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (F : BoundedBorel (PDE.Vec d)) (V U : TimeVelocity d → ℝ)
    (hV : ParabolicProbe.IsClassicalScalarTerminalSolution (PDE.euclideanBall v₀ R)
      stationary (zIndependentCoefficient B) τ F V)
    (hUc : ContinuousOn U (scalarParabolicClosedCylinder σ τ
      (PDE.euclideanBall v₀ R)))
    (hUj : ∀ p ∈ scalarParabolicOpenCylinder σ τ (PDE.euclideanBall v₀ R),
      ContDiffAt ℝ 2 U p)
    (hUs : ∀ p ∈ scalarParabolicOpenCylinder σ τ (PDE.euclideanBall v₀ R),
      scalarParabolicOperator B 0 U p ≤ 0)
    (hterm : ∀ v ∈ closure (PDE.euclideanBall v₀ R), F v ≤ U (τ, v))
    (hlat : ∀ p ∈ scalarParabolicLateralFace σ τ (PDE.euclideanBall v₀ R),
      0 ≤ U p) :
    ∀ v ∈ closure (PDE.euclideanBall v₀ R), V (σ, v) ≤ U (σ, v) := by
  let J := PDE.euclideanBall v₀ R
  let W : KineticPoint d → ℝ := fun p => V (p.time, p.position) - U (p.time, p.position)
  let r : Fin 2 → ℝ := ![σ, τ]
  have hr : StrictMono r := (Fin.strictMono_iff_lt_succ).mpr (by
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact hστ)
  have hopen : IsOpen (ParabolicProbe.scalarPastOpenCylinder J stationary τ) := by
    have he : ParabolicProbe.scalarPastOpenCylinder J stationary τ = Iio τ ×ˢ J := by
      ext p
      simp only [ParabolicProbe.scalarPastOpenCylinder, mem_ofPred_eq,
        movingDomain_stationary, mem_prod, mem_Iio]
    rw [he]
    exact isOpen_Iio.prod (isOpen_of_isAdmissibleEvolutionDomain (localBall_admissible v₀ hR))
  have hVc : ContinuousOn V (ParabolicProbe.scalarPastClosedCylinder J stationary τ) := hV.2.1
  have hVj : ∀ p ∈ scalarParabolicOpenCylinder σ τ J, ContDiffAt ℝ 2 V p := by
    intro p hp
    have hm : p ∈ ParabolicProbe.scalarPastOpenCylinder J stationary τ :=
      ⟨hp.1.2, by simpa only [movingDomain_stationary] using hp.2⟩
    exact ((hV.2.2.1 p hm).contDiffAt (hopen.mem_nhds hm)).of_le (by norm_num)
  have hmax : ∀ p ∈ maximumClosedTube J stationary σ τ, W p ≤ 0 := by
    apply movingDomain_maximumPrinciple (B := zIndependentCoefficient B)
      (drift := fun _ => 0) (Or.inl ⟨v₀, R, hR, rfl⟩) 0 r hr
    · exact continuous_const.continuousOn
    · have hc := hVc.comp (continuous_time.prodMk continuous_position).continuousOn
        (fun (p : KineticPoint d)
          (hp : p ∈ maximumClosedTube J stationary σ τ) => ⟨hp.1.2, hp.2⟩)
      exact hc.sub (hUc.comp (continuous_time.prodMk continuous_position).continuousOn
        (fun (p : KineticPoint d)
          (hp : p ∈ maximumClosedTube J stationary σ τ) =>
          ⟨hp.1, by simpa only [movingDomain_stationary] using hp.2⟩))
    · exact Or.inl (fun p _ z => rfl)
    · intro i p hp
      have hi : i = 0 := Fin.eq_zero i
      subst i
      have hm : (p.time, p.position) ∈ scalarParabolicOpenCylinder σ τ J :=
        ⟨hp.1, by simpa only [movingDomain_stationary] using hp.2⟩
      have hv := hVj _ hm
      have hu := hUj _ hm
      exact ⟨(hv.differentiableAt (by norm_num)).comp p.time (by fun_prop) |>.sub
        ((hu.differentiableAt (by norm_num)).comp p.time (by fun_prop)),
        (hv.comp p.position (contDiffAt_const.prodMk contDiffAt_id)).sub
          (hu.comp p.position (contDiffAt_const.prodMk contDiffAt_id)),
        differentiableAt_const (V (p.time, p.position) - U (p.time, p.position))⟩
    · intro i p hp
      exact (posDef_of_loewner_lower hlam (hB.2.2.2.2.1 p.time p.position)).posSemidef
    · intro i p hp
      have hi : i = 0 := Fin.eq_zero i
      subst i
      have hm : (p.time, p.position) ∈ scalarParabolicOpenCylinder σ τ J :=
        ⟨hp.1, by simpa only [movingDomain_stationary] using hp.2⟩
      have hv := hVj _ hm
      have hu := hUj _ hm
      change 0 ≤ transportedForwardOperator (zIndependentCoefficient B) (fun _ => 0)
        (fun q => V (q.time, q.position) - U (q.time, q.position)) p
      rw [lifted_operator B (fun _ => 0) (fun q => V q - U q) p,
        scalar_difference_operator B V U (p.time, p.position)
        ((hv.differentiableAt (by norm_num)).comp p.time (by fun_prop))
        ((hu.differentiableAt (by norm_num)).comp p.time (by fun_prop))
        (hv.comp p.position (contDiffAt_const.prodMk contDiffAt_id))
        (hu.comp p.position (contDiffAt_const.prodMk contDiffAt_id))]
      have hsol := hV.2.2.2.1 (p.time, p.position)
        ⟨hp.1.2, hp.2⟩
      change scalarParabolicOperator B 0 V (p.time, p.position) = 0 at hsol
      rw [hsol, zero_sub]
      exact neg_nonneg.mpr (hUs _ hm)
    · intro p hp hpt
      have hptτ : p.time = τ := hpt
      have ht := hV.2.2.2.2.1 (p.time, p.position)
        ⟨hptτ, by simpa only [movingDomain_stationary] using hp.2⟩
      change V (p.time, p.position) - U (p.time, p.position) ≤ 0
      rw [ht]
      apply sub_nonpos.mpr
      rw [show p.time = τ from hpt]
      exact hterm _ (by simpa only [movingDomain_stationary] using hp.2)
    · intro p hp hfront
      have ht := hV.2.2.2.2.2 (p.time, p.position) ⟨hp.1.2, hfront⟩
      change V (p.time, p.position) - U (p.time, p.position) ≤ 0
      rw [ht, zero_sub]
      exact neg_nonpos.mpr (hlat _ ⟨hp.1, by
        simpa only [movingDomain_stationary] using hfront⟩)
  intro v hv
  have he := hmax ⟨σ, v, 0⟩ ⟨⟨le_rfl, hστ.le⟩, by
    simpa only [movingDomain_stationary] using hv⟩
  exact sub_nonpos.mp he

/-- A smooth subsolution lies below the supplied scalar terminal solution on a ball. -/
theorem ball_terminal_lower_comparison {d : ℕ} {lam Lam σ τ R : ℝ}
    (v₀ : PDE.Vec d) (hR : 0 < R) (hστ : σ < τ) (hlam : 0 < lam)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (F : BoundedBorel (PDE.Vec d)) (V U : TimeVelocity d → ℝ)
    (hV : ParabolicProbe.IsClassicalScalarTerminalSolution (PDE.euclideanBall v₀ R)
      stationary (zIndependentCoefficient B) τ F V)
    (hUc : ContinuousOn U (scalarParabolicClosedCylinder σ τ
      (PDE.euclideanBall v₀ R)))
    (hUj : ∀ p ∈ scalarParabolicOpenCylinder σ τ (PDE.euclideanBall v₀ R),
      ContDiffAt ℝ 2 U p)
    (hUs : ∀ p ∈ scalarParabolicOpenCylinder σ τ (PDE.euclideanBall v₀ R),
      0 ≤ scalarParabolicOperator B 0 U p)
    (hterm : ∀ v ∈ closure (PDE.euclideanBall v₀ R), U (τ, v) ≤ F v)
    (hlat : ∀ p ∈ scalarParabolicLateralFace σ τ (PDE.euclideanBall v₀ R),
      U p ≤ 0) :
    ∀ v ∈ closure (PDE.euclideanBall v₀ R), U (σ, v) ≤ V (σ, v) := by
  let J := PDE.euclideanBall v₀ R
  let W : KineticPoint d → ℝ := fun p => U (p.time, p.position) - V (p.time, p.position)
  let r : Fin 2 → ℝ := ![σ, τ]
  have hr : StrictMono r := (Fin.strictMono_iff_lt_succ).mpr (by
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact hστ)
  have hopen : IsOpen (ParabolicProbe.scalarPastOpenCylinder J stationary τ) := by
    have he : ParabolicProbe.scalarPastOpenCylinder J stationary τ = Iio τ ×ˢ J := by
      ext p
      simp only [ParabolicProbe.scalarPastOpenCylinder, mem_ofPred_eq,
        movingDomain_stationary, mem_prod, mem_Iio]
    rw [he]
    exact isOpen_Iio.prod (isOpen_of_isAdmissibleEvolutionDomain (localBall_admissible v₀ hR))
  have hVc : ContinuousOn V (ParabolicProbe.scalarPastClosedCylinder J stationary τ) := hV.2.1
  have hVj : ∀ p ∈ scalarParabolicOpenCylinder σ τ J, ContDiffAt ℝ 2 V p := by
    intro p hp
    have hm : p ∈ ParabolicProbe.scalarPastOpenCylinder J stationary τ :=
      ⟨hp.1.2, by simpa only [movingDomain_stationary] using hp.2⟩
    exact ((hV.2.2.1 p hm).contDiffAt (hopen.mem_nhds hm)).of_le (by norm_num)
  have hmax : ∀ p ∈ maximumClosedTube J stationary σ τ, W p ≤ 0 := by
    apply movingDomain_maximumPrinciple (B := zIndependentCoefficient B)
      (drift := fun _ => 0) (Or.inl ⟨v₀, R, hR, rfl⟩) 0 r hr
    · exact continuous_const.continuousOn
    · have hc := hVc.comp (continuous_time.prodMk continuous_position).continuousOn
        (fun (p : KineticPoint d)
          (hp : p ∈ maximumClosedTube J stationary σ τ) => ⟨hp.1.2, hp.2⟩)
      exact (hUc.comp (continuous_time.prodMk continuous_position).continuousOn
        (fun (p : KineticPoint d)
          (hp : p ∈ maximumClosedTube J stationary σ τ) =>
          ⟨hp.1, by simpa only [movingDomain_stationary] using hp.2⟩)).sub hc
    · exact Or.inl (fun p _ z => rfl)
    · intro i p hp
      have hi : i = 0 := Fin.eq_zero i
      subst i
      have hm : (p.time, p.position) ∈ scalarParabolicOpenCylinder σ τ J :=
        ⟨hp.1, by simpa only [movingDomain_stationary] using hp.2⟩
      have hv := hVj _ hm
      have hu := hUj _ hm
      exact ⟨(hu.differentiableAt (by norm_num)).comp p.time (by fun_prop) |>.sub
        ((hv.differentiableAt (by norm_num)).comp p.time (by fun_prop)),
        (hu.comp p.position (contDiffAt_const.prodMk contDiffAt_id)).sub
          (hv.comp p.position (contDiffAt_const.prodMk contDiffAt_id)),
        differentiableAt_const (U (p.time, p.position) - V (p.time, p.position))⟩
    · intro i p hp
      exact (posDef_of_loewner_lower hlam (hB.2.2.2.2.1 p.time p.position)).posSemidef
    · intro i p hp
      have hi : i = 0 := Fin.eq_zero i
      subst i
      have hm : (p.time, p.position) ∈ scalarParabolicOpenCylinder σ τ J :=
        ⟨hp.1, by simpa only [movingDomain_stationary] using hp.2⟩
      have hv := hVj _ hm
      have hu := hUj _ hm
      change 0 ≤ transportedForwardOperator (zIndependentCoefficient B) (fun _ => 0)
        (fun q => U (q.time, q.position) - V (q.time, q.position)) p
      rw [lifted_operator B (fun _ => 0) (fun q => U q - V q) p,
        scalar_difference_operator B U V (p.time, p.position)
        ((hu.differentiableAt (by norm_num)).comp p.time (by fun_prop))
        ((hv.differentiableAt (by norm_num)).comp p.time (by fun_prop))
        (hu.comp p.position (contDiffAt_const.prodMk contDiffAt_id))
        (hv.comp p.position (contDiffAt_const.prodMk contDiffAt_id))]
      have hsol := hV.2.2.2.1 (p.time, p.position)
        ⟨hp.1.2, hp.2⟩
      change scalarParabolicOperator B 0 V (p.time, p.position) = 0 at hsol
      rw [hsol, sub_zero]
      exact hUs _ hm
    · intro p hp hpt
      have hptτ : p.time = τ := hpt
      have ht := hV.2.2.2.2.1 (p.time, p.position)
        ⟨hptτ, by simpa only [movingDomain_stationary] using hp.2⟩
      change U (p.time, p.position) - V (p.time, p.position) ≤ 0
      rw [ht]
      apply sub_nonpos.mpr
      rw [show p.time = τ from hpt]
      exact hterm _ (by simpa only [movingDomain_stationary] using hp.2)
    · intro p hp hfront
      have ht := hV.2.2.2.2.2 (p.time, p.position) ⟨hp.1.2, hfront⟩
      change U (p.time, p.position) - V (p.time, p.position) ≤ 0
      rw [ht, sub_zero]
      exact (hlat _ ⟨hp.1, by
        simpa only [movingDomain_stationary] using hfront⟩)
  intro v hv
  have he := hmax ⟨σ, v, 0⟩ ⟨⟨le_rfl, hστ.le⟩, by
    simpa only [movingDomain_stationary] using hv⟩
  exact sub_nonpos.mp he

end HypoellipticAleksandrov.KineticAleksandrov.LocalA

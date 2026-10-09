module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.OccupationScalingBorel
public import HypoellipticAleksandrov.Parabolic.ContDiffOnTwoToScalarC12
public import HypoellipticAleksandrov.Parabolic.KrylovEstimate.ScalarAffine

/-! # Scaling classical scalar terminal solutions on the whole space -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic SectionTwo Scaling Set

private theorem pastOpen_wholeSpace {d : ℕ} (τ : ℝ) :
    ParabolicProbe.scalarPastOpenCylinder (wholeSpace d) (fun _ => (0 : PDE.Vec d)) τ =
      {q : TimeVelocity d | q.1 < τ} := by
  ext q
  simp only [ParabolicProbe.scalarPastOpenCylinder, movingDomain_wholeSpace,
    mem_univ, and_true]

private theorem pastClosed_wholeSpace {d : ℕ} (τ : ℝ) :
    ParabolicProbe.scalarPastClosedCylinder (wholeSpace d) (fun _ => (0 : PDE.Vec d)) τ =
      {q : TimeVelocity d | q.1 ≤ τ} := by
  ext q
  simp only [ParabolicProbe.scalarPastClosedCylinder, movingDomain_wholeSpace,
    closure_univ, mem_univ, and_true]

/-- Classical scalar solutions pull back by the literal source radius scaling. -/
theorem occupation_scalarTerminal_pullback {d : ℕ} (σ₀ τ : ℝ)
    (r : {r : ℝ // 0 < r}) (B : CoefficientField d)
    (F : BoundedBorel (PDE.Vec d)) (V : TimeVelocity d → ℝ)
    (hV : ParabolicProbe.IsClassicalScalarTerminalSolution (wholeSpace d)
      (fun _ => (0 : PDE.Vec d)) (zIndependentCoefficient B) (σ₀ + r.1 ^ 2 * τ) F V) :
    ParabolicProbe.IsClassicalScalarTerminalSolution (wholeSpace d)
      (fun _ => (0 : PDE.Vec d))
      (zIndependentCoefficient (scaledCoefficient B σ₀ 0 r)) τ
      (occupation_borelComap (fun v => r.1 • v)
        (continuous_const_smul r.1).measurable F)
      (V ∘ parabolicAffine σ₀ 0 r.1) := by
  have hmapO : MapsTo (parabolicAffine σ₀ (0 : PDE.Vec d) r.1)
      (ParabolicProbe.scalarPastOpenCylinder (wholeSpace d) (fun _ => 0) τ)
      (ParabolicProbe.scalarPastOpenCylinder (wholeSpace d) (fun _ => 0)
        (σ₀ + r.1 ^ 2 * τ)) := by
    intro q hq
    rw [pastOpen_wholeSpace] at hq ⊢
    change σ₀ + r.1 ^ 2 * q.1 < σ₀ + r.1 ^ 2 * τ
    simpa only [add_comm] using
      add_lt_add_left (mul_lt_mul_of_pos_left hq (sq_pos_of_pos r.2)) σ₀
  have hmapC : MapsTo (parabolicAffine σ₀ (0 : PDE.Vec d) r.1)
      (ParabolicProbe.scalarPastClosedCylinder (wholeSpace d) (fun _ => 0) τ)
      (ParabolicProbe.scalarPastClosedCylinder (wholeSpace d) (fun _ => 0)
        (σ₀ + r.1 ^ 2 * τ)) := by
    intro q hq
    rw [pastClosed_wholeSpace] at hq ⊢
    change σ₀ + r.1 ^ 2 * q.1 ≤ σ₀ + r.1 ^ 2 * τ
    simpa only [add_comm] using
      add_le_add_left (mul_le_mul_of_nonneg_left hq (sq_nonneg r.1)) σ₀
  have hopen : IsOpen (ParabolicProbe.scalarPastOpenCylinder (wholeSpace d)
      (fun _ => (0 : PDE.Vec d)) (σ₀ + r.1 ^ 2 * τ)) := by
    rw [pastOpen_wholeSpace]
    exact isOpen_lt continuous_fst continuous_const
  have hreg := isScalarC12On_of_isOpen_contDiffOn_two hopen
    (hV.2.2.1.of_le (by simp))
  obtain ⟨-, hjet⟩ := KrylovEstimate.scalarC12On_affine_pullback hopen V hreg σ₀ 0 r.2
  refine ⟨?_, hV.2.1.comp
    (contDiff_infty_parabolicAffine σ₀ 0 r.1).continuous.continuousOn hmapC,
    hV.2.2.1.comp
      ((contDiff_infty_parabolicAffine σ₀ 0 r.1).of_le (by simp)).contDiffOn hmapO,
    ?_, ?_, ?_⟩
  · obtain ⟨C, hC, hb⟩ := hV.1
    exact ⟨C, hC, fun q hq => hb _ (hmapC hq)⟩
  · intro q hq
    obtain ⟨ht, hh⟩ := hjet q (hmapO hq)
    have he := hV.2.2.2.1 (parabolicAffine σ₀ 0 r.1 q) (hmapO hq)
    unfold scalarParabolicOperator at he ⊢
    rw [ht, hh, matrixContraction_smul_right]
    simp only [Pi.zero_apply, PDE.vecDot, zero_mul, Finset.sum_const_zero, add_zero] at he ⊢
    change r.1 ^ 2 * scalarTimeDerivative V (parabolicAffine σ₀ 0 r.1 q) +
      r.1 ^ 2 * matrixContraction (B (σ₀ + r.1 ^ 2 * q.1) (0 + r.1 • q.2))
        (scalarSpatialHessian V (parabolicAffine σ₀ 0 r.1 q)) = 0
    change scalarTimeDerivative V (parabolicAffine σ₀ 0 r.1 q) +
      matrixContraction (B (σ₀ + r.1 ^ 2 * q.1) (0 + r.1 • q.2))
        (scalarSpatialHessian V (parabolicAffine σ₀ 0 r.1 q)) = 0 at he
    rw [← mul_add, he, mul_zero]
  · intro q hq
    have ht : q.1 = τ := hq.1
    have hterm : parabolicAffine σ₀ (0 : PDE.Vec d) r.1 q ∈
        ParabolicProbe.scalarTerminalClosure (wholeSpace d) (fun _ => 0)
          (σ₀ + r.1 ^ 2 * τ) := by
      exact ⟨by change σ₀ + r.1 ^ 2 * q.1 = _; rw [ht],
        by simp [movingDomain_wholeSpace]⟩
    have hh := hV.2.2.2.2.1 _ hterm
    simpa only [Function.comp_apply, occupation_borelComap_apply, parabolicAffine,
      zero_add] using hh
  · intro q hq
    have hf := hq.2
    simp only [movingDomain_wholeSpace, frontier_univ, mem_empty_iff_false] at hf

/-- Inverse-radius pullback preserves smooth compact scalar terminal data. -/
theorem occupation_scalarDatum_inverse {d : ℕ} (σ₀ τ : ℝ)
    (r : {r : ℝ // 0 < r}) (F : BoundedBorel (PDE.Vec d))
    (hF : ParabolicProbe.IsSmoothCompactScalarTerminalDatum (wholeSpace d)
      (fun _ => (0 : PDE.Vec d)) τ F) :
    ParabolicProbe.IsSmoothCompactScalarTerminalDatum (wholeSpace d)
      (fun _ => (0 : PDE.Vec d)) (σ₀ + r.1 ^ 2 * τ)
      (occupation_borelComap (fun v => r.1⁻¹ • v)
        (continuous_const_smul r.1⁻¹).measurable F) := by
  refine ⟨?_, ?_, ?_⟩
  · exact hF.1.comp (by fun_prop)
  · have hc : HasCompactSupport (F : PDE.Vec d → ℝ) := hF.2.1
    exact hc.comp_homeomorph (Homeomorph.smulOfNeZero r.1⁻¹ (inv_ne_zero r.2.ne'))
  · intro v _
    simp only [movingDomain_wholeSpace, mem_univ]

/-- Pulling the inverse datum back by the forward radius recovers the given datum. -/
theorem occupation_scalarDatum_cancel {d : ℕ} (r : {r : ℝ // 0 < r})
    (F : BoundedBorel (PDE.Vec d)) :
    occupation_borelComap (fun v => r.1 • v) (continuous_const_smul r.1).measurable
      (occupation_borelComap (fun v => r.1⁻¹ • v)
        (continuous_const_smul r.1⁻¹).measurable F) = F := by
  ext v
  simp only [occupation_borelComap_apply, smul_smul, inv_mul_cancel₀ r.2.ne', one_smul]

/-- Inverse radius and time origin undo coefficient rescaling. -/
theorem occupation_inverse_scaledCoefficient {d : ℕ} (σ₀ : ℝ)
    (r : {r : ℝ // 0 < r}) (B : CoefficientField d) :
    scaledCoefficient (scaledCoefficient B σ₀ 0 r) (-σ₀ / r.1 ^ 2) 0
      ⟨r.1⁻¹, inv_pos.mpr r.2⟩ = B := by
  funext σ v
  unfold scaledCoefficient
  congr 1
  · dsimp only
    rw [inv_pow]
    field_simp [r.2.ne']
    ring
  · simp only [zero_add, smul_smul, mul_inv_cancel₀ r.2.ne', one_smul]

/-- The inverse time origin sends the original terminal time back to the scaled one. -/
theorem occupation_inverse_terminalTime (σ₀ τ : ℝ) (r : {r : ℝ // 0 < r}) :
    -σ₀ / r.1 ^ 2 + (r.1⁻¹) ^ 2 * (σ₀ + r.1 ^ 2 * τ) = τ := by
  rw [inv_pow]
  field_simp [r.2.ne']
  ring

/-- An arbitrary scaled classical solution pushes back to the original coefficient. -/
theorem occupation_scalarTerminal_inverse {d : ℕ} (σ₀ τ : ℝ)
    (r : {r : ℝ // 0 < r}) (B : CoefficientField d)
    (F : BoundedBorel (PDE.Vec d)) (W : TimeVelocity d → ℝ)
    (hW : ParabolicProbe.IsClassicalScalarTerminalSolution (wholeSpace d)
      (fun _ => (0 : PDE.Vec d))
      (zIndependentCoefficient (scaledCoefficient B σ₀ 0 r)) τ F W) :
    ParabolicProbe.IsClassicalScalarTerminalSolution (wholeSpace d)
      (fun _ => (0 : PDE.Vec d)) (zIndependentCoefficient B) (σ₀ + r.1 ^ 2 * τ)
      (occupation_borelComap (fun v => r.1⁻¹ • v)
        (continuous_const_smul r.1⁻¹).measurable F)
      (W ∘ parabolicAffine (-σ₀ / r.1 ^ 2) 0 r.1⁻¹) := by
  have ht := occupation_inverse_terminalTime σ₀ τ r
  have hW' : ParabolicProbe.IsClassicalScalarTerminalSolution (wholeSpace d)
      (fun _ => (0 : PDE.Vec d))
      (zIndependentCoefficient (scaledCoefficient B σ₀ 0 r))
      (-σ₀ / r.1 ^ 2 + (r.1⁻¹) ^ 2 * (σ₀ + r.1 ^ 2 * τ)) F W := by
    rw [ht]
    exact hW
  have hh := occupation_scalarTerminal_pullback (-σ₀ / r.1 ^ 2)
    (σ₀ + r.1 ^ 2 * τ) ⟨r.1⁻¹, inv_pos.mpr r.2⟩
    (scaledCoefficient B σ₀ 0 r) F W hW'
  rw [occupation_inverse_scaledCoefficient] at hh
  exact hh

/-- Inverse spacetime radius scaling cancels the forward affine map. -/
theorem occupation_inverse_forward {d : ℕ} (σ₀ : ℝ) (r : {r : ℝ // 0 < r})
    (q : TimeVelocity d) :
    parabolicAffine (-σ₀ / r.1 ^ 2) 0 r.1⁻¹ (parabolicAffine σ₀ 0 r.1 q) = q := by
  apply Prod.ext
  · change -σ₀ / r.1 ^ 2 + r.1⁻¹ ^ 2 * (σ₀ + r.1 ^ 2 * q.1) = q.1
    exact occupation_inverse_terminalTime σ₀ q.1 r
  · ext j
    change 0 + r.1⁻¹ * (0 + r.1 * q.2 j) = q.2 j
    simp only [zero_add, ← mul_assoc, inv_mul_cancel₀ r.2.ne', one_mul]

/-- A scalar terminal existence and uniqueness clause transports with the same operator family. -/
theorem occupation_scalarTerminalClause_scale {d : ℕ} (σ₀ : ℝ)
    (r : {r : ℝ // 0 < r}) (B : CoefficientField d)
    (Q : ParabolicOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (hQ : ∀ τ F, ParabolicProbe.IsSmoothCompactScalarTerminalDatum (wholeSpace d)
      (fun _ => (0 : PDE.Vec d)) τ F →
      ∃ V : TimeVelocity d → ℝ,
        ParabolicProbe.IsClassicalScalarTerminalSolution (wholeSpace d)
          (fun _ => (0 : PDE.Vec d)) (zIndependentCoefficient B) τ F V ∧
        (∀ σ hστ y, V (σ, y.1) = Q σ τ hστ (terminalPositionDatum F) y) ∧
        (∀ W : TimeVelocity d → ℝ,
          ParabolicProbe.IsClassicalScalarTerminalSolution (wholeSpace d)
            (fun _ => (0 : PDE.Vec d)) (zIndependentCoefficient B) τ F W →
          EqOn W V (ParabolicProbe.scalarPastClosedCylinder (wholeSpace d)
            (fun _ => (0 : PDE.Vec d)) τ))) :
    ∀ τ F, ParabolicProbe.IsSmoothCompactScalarTerminalDatum (wholeSpace d)
      (fun _ => (0 : PDE.Vec d)) τ F →
      ∃ V : TimeVelocity d → ℝ,
        ParabolicProbe.IsClassicalScalarTerminalSolution (wholeSpace d)
          (fun _ => (0 : PDE.Vec d))
          (zIndependentCoefficient (scaledCoefficient B σ₀ 0 r)) τ F V ∧
        (∀ σ hστ y, V (σ, y.1) =
          occupation_pushParabolicFamily
            (KineticAffineScaling.ofRadius σ₀ 0 0 (identityDrift d) r) Q σ τ hστ
            (terminalPositionDatum F) y) ∧
        (∀ W : TimeVelocity d → ℝ,
          ParabolicProbe.IsClassicalScalarTerminalSolution (wholeSpace d)
            (fun _ => (0 : PDE.Vec d))
            (zIndependentCoefficient (scaledCoefficient B σ₀ 0 r)) τ F W →
          EqOn W V (ParabolicProbe.scalarPastClosedCylinder (wholeSpace d)
            (fun _ => (0 : PDE.Vec d)) τ)) := by
  intro τ F hF
  let F0 := occupation_borelComap (fun v => r.1⁻¹ • v)
    (continuous_const_smul r.1⁻¹).measurable F
  obtain ⟨V, hV, hVQ, huniq⟩ := hQ (σ₀ + r.1 ^ 2 * τ) F0
    (occupation_scalarDatum_inverse σ₀ τ r F hF)
  have hVt := occupation_scalarTerminal_pullback σ₀ τ r B F0 V hV
  rw [occupation_scalarDatum_cancel] at hVt
  refine ⟨V ∘ parabolicAffine σ₀ 0 r.1, hVt, ?_, ?_⟩
  · intro σ hστ y
    let Φ := KineticAffineScaling.ofRadius σ₀ 0 0 (identityDrift d) r
    have hf : terminalPositionDatum (τ := σ₀ + r.1 ^ 2 * τ) F0 =
        occupation_borelComap (occupation_positionEquiv Φ τ).symm
          (occupation_positionEquiv Φ τ).symm.measurable (terminalPositionDatum F) := by
      ext x
      change F (r.1⁻¹ • x.1) = F (Φ.positionInv x.1)
      simp only [Φ, KineticAffineScaling.positionInv, KineticAffineScaling.ofRadius, sub_zero]
    have hh := hVQ (Φ.time σ) (Φ.time_le_iff.mpr hστ) (occupation_positionEquiv Φ σ y)
    rw [hf] at hh
    exact hh
  · intro W hW q hq
    have hWi := occupation_scalarTerminal_inverse σ₀ τ r B F W hW
    have heq := huniq (W ∘ parabolicAffine (-σ₀ / r.1 ^ 2) 0 r.1⁻¹) hWi
      (show parabolicAffine σ₀ 0 r.1 q ∈
        ParabolicProbe.scalarPastClosedCylinder (wholeSpace d) (fun _ => 0)
          (σ₀ + r.1 ^ 2 * τ) from by
        rw [pastClosed_wholeSpace] at hq ⊢
        change σ₀ + r.1 ^ 2 * q.1 ≤ σ₀ + r.1 ^ 2 * τ
        linarith only [mul_le_mul_of_nonneg_left hq (sq_nonneg r.1)])
    simpa only [Function.comp_apply, occupation_inverse_forward] using heq

end HypoellipticAleksandrov.KineticAleksandrov.Occupation

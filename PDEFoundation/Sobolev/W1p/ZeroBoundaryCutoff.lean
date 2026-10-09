module

public import PDEFoundation.Sobolev.W1p.ConvexApprox.Density
public import PDEFoundation.Sobolev.W1p.Cutoff
public import PDEFoundation.Sobolev.W1p.Truncation
public import PDEFoundation.Sobolev.W1p.ZeroBoundary

/-!
# Compactly supported multipliers have zero boundary values

This file combines finite-exponent smooth density on bounded open convex
domains with multiplication by globally smooth compactly supported functions.
The quantitative-cutoff theorem is a direct corollary of this common bridge.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE

open Filter MeasureTheory

namespace W1pFunction

variable {d : ℕ} {U inner outer : Set (Vec d)}
variable {p : ℝ≥0∞} {K : ℝ}

/-- The zero Sobolev function has a constant zero supported smooth approximation. -/
noncomputable def zeroSupportedSmoothApproximation [Fact (1 ≤ p)] :
    (0 : W1pFunction U p).SupportedSmoothApproximation :=
  { approx := fun _ => 0
    approx_smooth := fun _ => contDiff_zero_fun
    approx_hasCompactSupport := fun _ => HasCompactSupport.zero
    approx_tsupport_subset := fun _ => by simp only [tsupport_zero, Set.empty_subset]
    tendsto_value := by
      simpa only [zero_toFun, sub_self, eLpNorm_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
    tendsto_grad := fun i => by
      have hZero :
          (fun n : ℕ =>
            eLpNorm
              (fun x =>
                (fderiv ℝ (0 : Vec d → ℝ) x) (basisVec i) -
                  (0 : W1pFunction U p).grad x i)
              p (volumeOn U)) = fun _ => 0 := by
        funext n
        calc
          eLpNorm
              (fun x =>
                (fderiv ℝ (fun _ : Vec d => (0 : ℝ)) x) (basisVec i) -
                  (0 : W1pFunction U p).grad x i)
              p (volumeOn U) =
              eLpNorm (0 : Vec d → ℝ) p (volumeOn U) := by
            apply eLpNorm_congr_ae
            exact Eventually.of_forall fun x => by
              change (fderiv ℝ (0 : Vec d → ℝ) x) (basisVec i) - 0 = 0
              rw [fderiv_zero]
              simp only [Pi.zero_apply, zero_apply, sub_zero]
          _ = 0 := eLpNorm_zero
      simpa only [hZero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0)) }

/-- A globally smooth multiplier supported in `U` turns a finite-exponent
Sobolev representative into one with a supported smooth approximation. -/
noncomputable def supportedSmoothApproximation_mulContDiffHasCompactSupport
    (hU : IsOpenBoundedConvexDomain U) (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφCompact : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) :
    letI : Fact (1 ≤ p) := ⟨hp⟩
    (u.mulContDiffHasCompactSupport hφ hφCompact).SupportedSmoothApproximation := by
  letI : Fact (1 ≤ p) := ⟨hp⟩
  by_cases htsupport : tsupport φ = ∅
  · have hφZero : φ = 0 := tsupport_eq_empty_iff.mp htsupport
    have hMulZero : u.mulContDiffHasCompactSupport hφ hφCompact = 0 := by
      have hGradientZero : classicalGradient (0 : Vec d → ℝ) = 0 := by
        funext x i
        rw [classicalGradient_apply, fderiv_zero]
        rfl
      apply W1pFunction.ext
      · rw [mulContDiffHasCompactSupport_toFun, hφZero, zero_toFun]
        funext x
        simp only [Pi.zero_apply, zero_mul]
      · rw [mulContDiffHasCompactSupport_grad, hφZero, hGradientZero, zero_grad]
        funext x
        ext i
        simp only [Pi.zero_apply, zero_smul, smul_zero, Pi.add_apply, add_zero]
    simpa only [hMulZero] using (zeroSupportedSmoothApproximation (U := U) (p := p))
  · let x0 : Vec d := Classical.choose (Set.nonempty_iff_ne_empty.mpr htsupport)
    have hx0 : x0 ∈ tsupport φ :=
      Classical.choose_spec (Set.nonempty_iff_ne_empty.mpr htsupport)
    have hx0U : x0 ∈ U := hφU hx0
    have hnhds : ∃ r : ℝ, 0 < r ∧ Metric.ball x0 r ⊆ U :=
      Metric.mem_nhds_iff.mp (hU.isOpen.mem_nhds hx0U)
    let r : ℝ := Classical.choose hnhds / 2
    have hr : 0 < r := by
      dsimp only [r]
      exact half_pos (Classical.choose_spec hnhds).1
    have hball : Metric.closedBall x0 r ⊆ U := by
      apply (Metric.closedBall_subset_ball (half_lt_self (Classical.choose_spec hnhds).1)).trans
      exact (Classical.choose_spec hnhds).2
    let v : ℕ → W1pFunction U p :=
      convexApproxSmoothW1p hU hp u x0 hr
    refine
      { approx := fun n => φ * (v n).toFun
        approx_smooth := fun n => hφ.mul
          (contDiff_convexApproxSmoothW1p_toFun hU hp u x0 hr n)
        approx_hasCompactSupport := fun n => by
          simpa only [Pi.mul_apply, mul_comm] using hφCompact.mul_left
            (f := (v n).toFun)
        approx_tsupport_subset := fun n =>
          (tsupport_mul_subset_left (f := φ) (g := (v n).toFun)).trans hφU
        tendsto_value := ?_
        tendsto_grad := ?_ }
    · have hRaw :
          Tendsto
            (fun n =>
              eLpNormOn U p
                ((v n - u).mulContDiffHasCompactSupport hφ hφCompact).toFun)
            atTop (𝓝 0) := by
        let C : ℝ≥0∞ := eLpNormOn U ∞ φ
        have hCFinite : C ≠ ∞ := by
          dsimp only [C]
          exact ((hφ.continuous.memLp_of_hasCompactSupport hφCompact).restrict U).eLpNorm_lt_top.ne
        have hConv :=
          tendsto_convexApproxSmoothW1p_toFun_eLpNorm_sub hU hp hpTop u hball hr
        have hUpper :
            Tendsto
              (fun n => C * eLpNormOn U p (fun x => (v n).toFun x - u.toFun x))
              atTop (𝓝 0) := by
          have h := ENNReal.Tendsto.const_mul hConv (Or.inr hCFinite)
          rw [mul_zero] at h
          exact h
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
          tendsto_const_nhds hUpper (Eventually.of_forall fun _ => zero_le) ?_
        exact Eventually.of_forall fun n => by
          exact
            (v n - u).eLpNormOn_mulContDiffMemLpTop_toFun_le
              hφ
              ((hφ.continuous.memLp_of_hasCompactSupport hφCompact).restrict U)
              (fun i => by
                have hContinuous : Continuous (fun x => classicalGradient φ x i) := by
                  simpa only [classicalGradient_apply] using
                    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
                have hCompact : HasCompactSupport (fun x => classicalGradient φ x i) := by
                  simpa only [classicalGradient_apply] using
                    hφCompact.fderiv_apply (𝕜 := ℝ) (basisVec i)
                exact (hContinuous.memLp_of_hasCompactSupport hCompact).restrict U)
      refine hRaw.congr' ?_
      filter_upwards with n
      apply congrArg (fun f => eLpNorm f p (volumeOn U))
      funext x
      simp only [v, mulContDiffHasCompactSupport_toFun, sub_toFun,
        Pi.mul_apply, Pi.sub_apply]
      ring
    · intro i
      have hValue :=
        tendsto_convexApproxSmoothW1p_toFun_eLpNorm_sub hU hp hpTop u hball hr
      have hGradient :=
        tendsto_convexApproxSmoothW1p_grad_coord_eLpNorm_sub
          hU hp hpTop u hball hr i
      have hφTop : MemLpOn U ∞ φ :=
        (hφ.continuous.memLp_of_hasCompactSupport hφCompact).restrict U
      have hDφTop : ∀ j : Fin d, MemLpOn U ∞
          (fun x => classicalGradient φ x j) := by
        intro j
        have hContinuous : Continuous (fun x => classicalGradient φ x j) := by
          simpa only [classicalGradient_apply] using
            (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
        have hCompact : HasCompactSupport (fun x => classicalGradient φ x j) := by
          simpa only [classicalGradient_apply] using
            hφCompact.fderiv_apply (𝕜 := ℝ) (basisVec j)
        exact (hContinuous.memLp_of_hasCompactSupport hCompact).restrict U
      have hUpper :
          Tendsto
            (fun n =>
              eLpNormOn U ∞ φ *
                  eLpNormOn U p (fun x => (v n).grad x i - u.grad x i) +
                eLpNormOn U ∞ (fun x => classicalGradient φ x i) *
                  eLpNormOn U p (fun x => (v n).toFun x - u.toFun x))
            atTop (𝓝 0) := by
        have hφFinite : eLpNormOn U ∞ φ ≠ ∞ := hφTop.eLpNorm_lt_top.ne
        have hDφFinite : eLpNormOn U ∞ (fun x => classicalGradient φ x i) ≠ ∞ :=
          (hDφTop i).eLpNorm_lt_top.ne
        have h := (ENNReal.Tendsto.const_mul hGradient (Or.inr hφFinite)).add
          (ENNReal.Tendsto.const_mul hValue (Or.inr hDφFinite))
        rw [mul_zero, mul_zero, add_zero] at h
        exact h
      have hRaw :
          Tendsto
            (fun n => eLpNormOn U p
              (fun x => ((v n - u).mulContDiffHasCompactSupport hφ hφCompact).grad x i))
            atTop (𝓝 0) := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
          tendsto_const_nhds hUpper (Eventually.of_forall fun _ => zero_le) ?_
        exact Eventually.of_forall fun n =>
          (v n - u).eLpNormOn_mulContDiffMemLpTop_grad_coord_le hφ hφTop hDφTop i
      refine hRaw.congr' ?_
      filter_upwards with n
      apply congrArg (fun f => eLpNorm f p (volumeOn U))
      funext x
      rw [fderiv_mul
        (hφ.differentiable (by simp) x)
        ((contDiff_convexApproxSmoothW1p_toFun hU hp u x0 hr n).differentiable
          (by simp) x)]
      simp only [v, mulContDiffHasCompactSupport_grad, sub_toFun, sub_grad,
        Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        add_apply, smul_apply]
      rw [← classicalGradient_apply, ← classicalGradient_apply]
      have hGrad :
          classicalGradient (convexApproxSmoothW1p hU hp u x0 hr n).toFun =
            (convexApproxSmoothW1p hU hp u x0 hr n).grad := by
        rw [convexApproxSmoothW1p_toFun]
        exact (convexApproxSmoothW1p_grad hU hp u x0 hr n).symm
      rw [hGrad]
      ring

/-- A globally smooth multiplier supported in `U` sends a finite-exponent
Sobolev representative to the closed zero-boundary graph. -/
theorem mulContDiffHasCompactSupport_mem_w10pGraph
    (hU : IsOpenBoundedConvexDomain U) (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφCompact : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) :
    letI : Fact (1 ≤ p) := ⟨hp⟩
    (u.mulContDiffHasCompactSupport hφ hφCompact).toW1pGraph ∈
      (w10pGraphClosedSubmodule (p := p) hU.isOpen).toSubmodule := by
  let : Fact (1 ≤ p) := ⟨hp⟩
  exact
    (u.mulContDiffHasCompactSupport hφ hφCompact).mem_w10pGraph_of_supportedSmoothApproximation
      hU.isOpen
      (u.supportedSmoothApproximation_mulContDiffHasCompactSupport
        hU hp hpTop hφ hφCompact hφU)

/-- A quantitative smooth cutoff supported in `U` sends a finite-exponent
Sobolev representative to the closed zero-boundary graph. -/
theorem mulCutoff_mem_w10pGraph
    (hU : IsOpenBoundedConvexDomain U) (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p)
    (η : QuantitativeSmoothCutoff inner outer K) (houter : outer ⊆ U) :
    letI : Fact (1 ≤ p) := ⟨hp⟩
    (u.mulCutoff η hp).toW1pGraph ∈
      (w10pGraphClosedSubmodule (p := p) hU.isOpen).toSubmodule := by
  let : Fact (1 ≤ p) := ⟨hp⟩
  change (u.mulContDiffHasCompactSupport η.smooth η.hasCompactSupport).toW1pGraph ∈ _
  exact u.mulContDiffHasCompactSupport_mem_w10pGraph
    hU hp hpTop η.smooth η.hasCompactSupport (η.tsupport_subset.trans houter)

/-- The squared-cutoff positive part belongs to the closed zero-boundary
graph, with literal representative `η^2 (u - k)_+`. -/
theorem mulCutoff_sq_positivePartSubConst_mem_w10pGraph
    (hU : IsOpenBoundedConvexDomain U) (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p) (k : ℝ)
    (η : QuantitativeSmoothCutoff inner outer K) (houter : outer ⊆ U) :
    letI : Fact (1 ≤ p) := ⟨hp⟩
    ((u.positivePartSubConst hU hp hpTop k).mulCutoff η.sq hp).toW1pGraph ∈
      (w10pGraphClosedSubmodule (p := p) hU.isOpen).toSubmodule := by
  exact (u.positivePartSubConst hU hp hpTop k).mulCutoff_mem_w10pGraph
    hU hp hpTop η.sq houter

/-- The squared-cutoff positive part has the literal expected value
representative. -/
@[simp]
theorem mulCutoff_sq_positivePartSubConst_toFun
    (hU : IsOpenBoundedConvexDomain U) (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p) (k : ℝ)
    (η : QuantitativeSmoothCutoff inner outer K) :
    ((u.positivePartSubConst hU hp hpTop k).mulCutoff η.sq hp).toFun =
      fun x => η x ^ 2 * max (u.toFun x - k) 0 := by
  rw [mulCutoff_sq_toFun, positivePartSubConst_toFun]

/-- The squared-cutoff positive part has the exact product-rule gradient
representative. -/
theorem mulCutoff_sq_positivePartSubConst_grad
    (hU : IsOpenBoundedConvexDomain U) (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p) (k : ℝ)
    (η : QuantitativeSmoothCutoff inner outer K) :
    ((u.positivePartSubConst hU hp hpTop k).mulCutoff η.sq hp).grad =
      fun x =>
        η x ^ 2 • {y | k < u.toFun y}.indicator u.grad x +
          (2 * η x * max (u.toFun x - k) 0) •
            classicalGradient η.toFun x := by
  rw [mulCutoff_sq_grad, positivePartSubConst_toFun,
    positivePartSubConst_grad]

end W1pFunction

end PDE

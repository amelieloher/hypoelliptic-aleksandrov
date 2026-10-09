module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeDualPairing
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklov

/-!
# Local convergence of reverse-time Steklov dual pairings

This module combines the local Bochner Steklov approximation with
the reverse-time `V*`--`V` pairing.  It makes no fixed-time representative,
trace, weak-derivative, or energy assertion.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

private theorem memLp_on_Icc_of_reverseTimeLp
    {E : Type*} [NormedAddCommGroup E]
    (T : ℝ) (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T))
    {a b : ℝ} (ha : 0 < a) (hb : b < T) :
    MemLp (f : ℝ → E) (2 : ℝ≥0∞) (volume.restrict (Icc a b)) := by
  have hK : Icc a b ⊆ Ioo 0 T := by
    intro t ht
    exact ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
  simpa only [reverseTimeVolume, reverseTimeOpenInterval,
    Measure.restrict_restrict_of_subset hK] using (Lp.memLp f).restrict (Icc a b)

private theorem memLp_on_Icc_of_continuous
    {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E) (hf : Continuous f) (a b : ℝ) :
    MemLp f (2 : ℝ≥0∞) (volume.restrict (Icc a b)) := by
  refine (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr ?_
  exact (hf.norm.pow 2).integrableOn_Icc

private theorem sqNorm_integral_eq_norm_sq_toLp
    {E : Type*} [NormedAddCommGroup E]
    {μ : Measure ℝ} (F : ℝ → E) (hF : MemLp F (2 : ℝ≥0∞) μ) :
    ∫ t, ‖F t‖ ^ 2 ∂μ = ‖hF.toLp F‖ ^ 2 := by
  rw [Lp.norm_def, eLpNorm_congr_ae hF.coeFn_toLp,
    hF.eLpNorm_eq_integral_rpow_norm]
  · simp
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun _ => sq_nonneg _) _)]
    exact (Real.rpow_inv_natCast_pow
      (integral_nonneg fun _ => sq_nonneg _) (by norm_num)).symm
  · norm_num
  · simp

private theorem sqrt_sqNorm_integral_triangle
    {E : Type*} [NormedAddCommGroup E]
    {μ : Measure ℝ} (x y : ℝ → E)
    (hx : MemLp x (2 : ℝ≥0∞) μ) (hy : MemLp y (2 : ℝ≥0∞) μ) :
    √(∫ t, ‖x t‖ ^ 2 ∂μ) ≤
      √(∫ t, ‖x t - y t‖ ^ 2 ∂μ) + √(∫ t, ‖y t‖ ^ 2 ∂μ) := by
  let hxy := hx.sub hy
  have hEq : hx.toLp x = hxy.toLp (x - y) + hy.toLp y := by
    apply Lp.ext
    filter_upwards [hx.coeFn_toLp, hxy.coeFn_toLp, hy.coeFn_toLp,
      Lp.coeFn_add (hxy.toLp (x - y)) (hy.toLp y)] with t h1 h2 h3 h4
    rw [h4, Pi.add_apply, h1, h2, h3]
    simp only [Pi.sub_apply]
    abel
  have hxySq : ∫ t, ‖x t - y t‖ ^ 2 ∂μ = ‖hxy.toLp (x - y)‖ ^ 2 := by
    simpa only [Pi.sub_apply] using sqNorm_integral_eq_norm_sq_toLp (x - y) hxy
  rw [sqNorm_integral_eq_norm_sq_toLp x hx, hxySq,
    sqNorm_integral_eq_norm_sq_toLp y hy, hEq]
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using
    norm_add_le (hxy.toLp (x - y)) (hy.toLp y)

private theorem integral_mul_norm_le_sqrt_mul_sqrt
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {μ : Measure ℝ} (f : ℝ → E) (g : ℝ → F)
    (hf : MemLp f (2 : ℝ≥0∞) μ) (hg : MemLp g (2 : ℝ≥0∞) μ) :
    ∫ t, ‖f t‖ * ‖g t‖ ∂μ ≤
      √(∫ t, ‖f t‖ ^ 2 ∂μ) * √(∫ t, ‖g t‖ ^ 2 ∂μ) := by
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two
    (μ := μ) (f := fun t => ‖f t‖) (g := fun t => ‖g t‖)
    (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall fun _ => norm_nonneg _)
    (by simpa only [ENNReal.ofReal_ofNat] using hf.norm)
    (by simpa only [ENNReal.ofReal_ofNat] using hg.norm)
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  simpa only [Real.rpow_two] using hholder

private theorem tendsto_integral_abs_bilin_of_sqNorm
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : F →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ f : F, ∀ e : E, ‖B f e‖ ≤ ‖f‖ * ‖e‖)
    (μ : Measure ℝ) (u : ℝ → E) (g : ℝ → F)
    (uh : ℝ → ℝ → E) (gh : ℝ → ℝ → F)
    (hu : MemLp u (2 : ℝ≥0∞) μ) (hg : MemLp g (2 : ℝ≥0∞) μ)
    (hraw : Integrable (fun t => B (g t) (u t)) μ)
    (huh : ∀ᶠ h : ℝ in 𝓝[>] 0, MemLp (uh h) (2 : ℝ≥0∞) μ)
    (hgh : ∀ᶠ h : ℝ in 𝓝[>] 0, MemLp (gh h) (2 : ℝ≥0∞) μ)
    (hU : Tendsto (fun h : ℝ => ∫ t, ‖uh h t - u t‖ ^ 2 ∂μ)
      (𝓝[>] 0) (𝓝 0))
    (hG : Tendsto (fun h : ℝ => ∫ t, ‖gh h t - g t‖ ^ 2 ∂μ)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun h : ℝ => ∫ t, |B (gh h t) (uh h t) - B (g t) (u t)| ∂μ)
      (𝓝[>] 0) (𝓝 0) := by
  have hUsqrt : Tendsto (fun h : ℝ =>
      √(∫ t, ‖uh h t - u t‖ ^ 2 ∂μ)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.sqrt_zero] using hU.sqrt
  have hGsqrt : Tendsto (fun h : ℝ =>
      √(∫ t, ‖gh h t - g t‖ ^ 2 ∂μ)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.sqrt_zero] using hG.sqrt
  rcases hUsqrt.isBoundedUnder_le.eventually_le with ⟨C, hC⟩
  have hUhBound : ∀ᶠ h : ℝ in 𝓝[>] 0,
      √(∫ t, ‖uh h t‖ ^ 2 ∂μ) ≤ C + √(∫ t, ‖u t‖ ^ 2 ∂μ) := by
    filter_upwards [huh, hC] with h huh hC
    exact (sqrt_sqNorm_integral_triangle (uh h) u huh hu).trans
      (add_le_add_left hC _)
  have hUhNormBound : IsBoundedUnder (· ≤ ·) (𝓝[>] 0)
      (norm ∘ fun h : ℝ => √(∫ t, ‖uh h t‖ ^ 2 ∂μ)) :=
    isBoundedUnder_of_eventually_le (hUhBound.mono fun h hh => by
      simpa only [Function.comp_apply, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)] using hh)
  have hfirst : Tendsto (fun h : ℝ =>
      √(∫ t, ‖gh h t - g t‖ ^ 2 ∂μ) * √(∫ t, ‖uh h t‖ ^ 2 ∂μ))
      (𝓝[>] 0) (𝓝 0) :=
    hGsqrt.zero_mul_isBoundedUnder_le hUhNormBound
  have hconst : Tendsto (fun _ : ℝ => √(∫ t, ‖g t‖ ^ 2 ∂μ))
      (𝓝[>] 0) (𝓝 (√(∫ t, ‖g t‖ ^ 2 ∂μ)) : Filter ℝ) :=
    tendsto_const_nhds
  have hsecond : Tendsto (fun h : ℝ =>
      √(∫ t, ‖g t‖ ^ 2 ∂μ) * √(∫ t, ‖uh h t - u t‖ ^ 2 ∂μ))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [mul_zero] using hconst.mul hUsqrt
  apply squeeze_zero'
  · filter_upwards with h
    exact integral_nonneg fun _ => abs_nonneg _
  · filter_upwards [huh, hgh] with h huh hgh
    have hdu : MemLp (fun t => uh h t - u t) (2 : ℝ≥0∞) μ := huh.sub hu
    have hdg : MemLp (fun t => gh h t - g t) (2 : ℝ≥0∞) μ := hgh.sub hg
    have hpairs : Integrable (fun t => B (gh h t) (uh h t)) μ :=
      memLp_one_iff_integrable.mp (B.memLp_of_bilin 1 hgh huh)
    have hleft : Integrable (fun t => |B (gh h t) (uh h t) - B (g t) (u t)|) μ := by
      simpa only [Real.norm_eq_abs, Pi.sub_def] using (hpairs.sub hraw).norm
    have hterm1 : Integrable (fun t => ‖gh h t - g t‖ * ‖uh h t‖) μ :=
      hdg.norm.integrable_mul huh.norm
    have hterm2 : Integrable (fun t => ‖g t‖ * ‖uh h t - u t‖) μ :=
      hg.norm.integrable_mul hdu.norm
    have hpoint : ∀ t : ℝ,
        |B (gh h t) (uh h t) - B (g t) (u t)| ≤
          ‖gh h t - g t‖ * ‖uh h t‖ + ‖g t‖ * ‖uh h t - u t‖ := by
      intro t
      change ‖B (gh h t) (uh h t) - B (g t) (u t)‖ ≤ _
      calc
        ‖B (gh h t) (uh h t) - B (g t) (u t)‖ =
            ‖B (gh h t - g t) (uh h t) + B (g t) (uh h t - u t)‖ := by
              congr 1
              rw [B.map_sub, ContinuousLinearMap.sub_apply, (B (g t)).map_sub]
              ring
        _ ≤ ‖B (gh h t - g t) (uh h t)‖ + ‖B (g t) (uh h t - u t)‖ := norm_add_le _ _
        _ ≤ ‖gh h t - g t‖ * ‖uh h t‖ + ‖g t‖ * ‖uh h t - u t‖ :=
          add_le_add (hB _ _) (hB _ _)
    have hmono := integral_mono hleft (hterm1.add hterm2) hpoint
    have hholder1 := integral_mul_norm_le_sqrt_mul_sqrt
      (fun t => gh h t - g t) (fun t => uh h t) hdg huh
    have hholder2 := integral_mul_norm_le_sqrt_mul_sqrt
      g (fun t => uh h t - u t) hg hdu
    calc
      (∫ t, |B (gh h t) (uh h t) - B (g t) (u t)| ∂μ) ≤
          ∫ t, ‖gh h t - g t‖ * ‖uh h t‖ + ‖g t‖ * ‖uh h t - u t‖ ∂μ := hmono
      _ = (∫ t, ‖gh h t - g t‖ * ‖uh h t‖ ∂μ) +
          ∫ t, ‖g t‖ * ‖uh h t - u t‖ ∂μ := integral_add hterm1 hterm2
      _ ≤ √(∫ t, ‖gh h t - g t‖ ^ 2 ∂μ) * √(∫ t, ‖uh h t‖ ^ 2 ∂μ) +
          √(∫ t, ‖g t‖ ^ 2 ∂μ) * √(∫ t, ‖uh h t - u t‖ ^ 2 ∂μ) :=
        add_le_add hholder1 hholder2
  · simpa only [add_zero] using hfirst.add hsecond

private noncomputable def h10DualEvaluation
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) :
    H10HilbertGraphDual hΩ →L[ℝ] H10HilbertGraph hΩ →L[ℝ] ℝ :=
  ContinuousLinearMap.flip (ContinuousLinearMap.apply ℝ ℝ)

private theorem h10DualEvaluation_apply
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (g : H10HilbertGraphDual hΩ) (u : H10HilbertGraph hΩ) :
    h10DualEvaluation hΩ g u = g u := by
  rfl

private theorem h10DualEvaluation_le
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (g : H10HilbertGraphDual hΩ) (u : H10HilbertGraph hΩ) :
    ‖h10DualEvaluation hΩ g u‖ ≤ ‖g‖ * ‖u‖ := by
  simpa only [h10DualEvaluation_apply] using g.le_opNorm u

private theorem tendsto_forwardSteklov_sqNorm_integral_on_Icc_restrict
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < T) :
    Tendsto (fun h : ℝ => ∫ t,
      ‖reverseTimeForwardSteklov T h f t - f t‖ ^ 2 ∂(volume.restrict (Icc a b)))
      (𝓝[>] 0) (𝓝 0) := by
  exact tendsto_forwardSteklov_sqNorm_integral_on_Icc T f ha hab hb

private theorem tendsto_backwardSteklov_sqNorm_integral_on_Icc_restrict
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < T) :
    Tendsto (fun h : ℝ => ∫ t,
      ‖reverseTimeBackwardSteklov T h f t - f t‖ ^ 2 ∂(volume.restrict (Icc a b)))
      (𝓝[>] 0) (𝓝 0) := by
  exact tendsto_backwardSteklov_sqNorm_integral_on_Icc T f ha hab hb

private theorem tendsto_h10DualPairing_of_sqNorm
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (μ : Measure ℝ)
    (u : ℝ → H10HilbertGraph hΩ) (g : ℝ → H10HilbertGraphDual hΩ)
    (uh : ℝ → ℝ → H10HilbertGraph hΩ)
    (gh : ℝ → ℝ → H10HilbertGraphDual hΩ)
    (hu : MemLp u (2 : ℝ≥0∞) μ) (hg : MemLp g (2 : ℝ≥0∞) μ)
    (hraw : Integrable (fun t => (g t) (u t)) μ)
    (huh : ∀ᶠ h : ℝ in 𝓝[>] 0, MemLp (uh h) (2 : ℝ≥0∞) μ)
    (hgh : ∀ᶠ h : ℝ in 𝓝[>] 0, MemLp (gh h) (2 : ℝ≥0∞) μ)
    (hU : Tendsto (fun h : ℝ => ∫ t, ‖uh h t - u t‖ ^ 2 ∂μ)
      (𝓝[>] 0) (𝓝 0))
    (hG : Tendsto (fun h : ℝ => ∫ t, ‖gh h t - g t‖ ^ 2 ∂μ)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun h : ℝ => ∫ t,
      |(gh h t) (uh h t) - (g t) (u t)| ∂μ)
      (𝓝[>] 0) (𝓝 0) := by
  simpa only [h10DualEvaluation_apply] using
    tendsto_integral_abs_bilin_of_sqNorm (B := h10DualEvaluation hΩ)
      (hB := h10DualEvaluation_le hΩ)
      μ u g uh gh hu hg hraw huh hgh hU hG

private noncomputable def forwardPrimalAverage
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (u : ReverseTimeL2V hΩ T) : ℝ → ℝ → H10HilbertGraph hΩ :=
  fun h t => reverseTimeForwardSteklov T h u t

private noncomputable def forwardDualAverage
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (g : ReverseTimeL2VStar hΩ T) : ℝ → ℝ → H10HilbertGraphDual hΩ :=
  fun h t => reverseTimeForwardSteklov T h g t

private noncomputable def forwardPairingErrorIntegral
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (a b h : ℝ) : ℝ :=
  ∫ t in Icc a b,
    |(forwardDualAverage hΩ T g h t) (forwardPrimalAverage hΩ T u h t) - (g t) (u t)|

private noncomputable def backwardPrimalAverage
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (u : ReverseTimeL2V hΩ T) : ℝ → ℝ → H10HilbertGraph hΩ :=
  fun h t => reverseTimeBackwardSteklov T h u t

private noncomputable def backwardDualAverage
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (g : ReverseTimeL2VStar hΩ T) : ℝ → ℝ → H10HilbertGraphDual hΩ :=
  fun h t => reverseTimeBackwardSteklov T h g t

private noncomputable def backwardPairingErrorIntegral
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (a b h : ℝ) : ℝ :=
  ∫ t in Icc a b,
    |(backwardDualAverage hΩ T g h t) (backwardPrimalAverage hΩ T u h t) - (g t) (u t)|

private theorem tendsto_forwardSteklov_dualPairing_integral_on_Icc_raw
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < T) :
    Filter.Tendsto (forwardPairingErrorIntegral hΩ T u g a b)
      (𝓝[>] 0) (𝓝 0) := by
  let μ : Measure ℝ := volume.restrict (Icc a b)
  let uh := forwardPrimalAverage hΩ T u
  let gh := forwardDualAverage hΩ T g
  have hK : Icc a b ⊆ Ioo 0 T := by
    intro t ht
    exact ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
  have hu : MemLp (u : ℝ → H10HilbertGraph hΩ) (2 : ℝ≥0∞) μ := by
    simpa only [μ] using memLp_on_Icc_of_reverseTimeLp T u ha hb
  have hg : MemLp (g : ℝ → H10HilbertGraphDual hΩ) (2 : ℝ≥0∞) μ := by
    simpa only [μ] using memLp_on_Icc_of_reverseTimeLp T g ha hb
  have hraw : Integrable (fun t => (g t) (u t)) μ := by
    dsimp only [μ, reverseTimeVolume, reverseTimeOpenInterval]
    rw [← Measure.restrict_restrict_of_subset hK]
    exact (integrable_reverseTimeDualPairing hΩ T u g).restrict
  have huh : ∀ᶠ h : ℝ in 𝓝[>] 0,
      MemLp (uh h) (2 : ℝ≥0∞) μ := by
    filter_upwards [show ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h from self_mem_nhdsWithin]
      with h hh
    change MemLp (reverseTimeForwardSteklov T h u) (2 : ℝ≥0∞) μ
    simpa only [μ] using memLp_on_Icc_of_continuous
      (reverseTimeForwardSteklov T h u)
      (continuous_reverseTimeForwardSteklov T h hh u) a b
  have hgh : ∀ᶠ h : ℝ in 𝓝[>] 0,
      MemLp (gh h) (2 : ℝ≥0∞) μ := by
    filter_upwards [show ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h from self_mem_nhdsWithin]
      with h hh
    change MemLp (reverseTimeForwardSteklov T h g) (2 : ℝ≥0∞) μ
    simpa only [μ] using memLp_on_Icc_of_continuous
      (reverseTimeForwardSteklov T h g)
      (continuous_reverseTimeForwardSteklov T h hh g) a b
  have hU := tendsto_forwardSteklov_sqNorm_integral_on_Icc_restrict T u ha hab hb
  have hG := tendsto_forwardSteklov_sqNorm_integral_on_Icc_restrict T g ha hab hb
  change Tendsto (fun h : ℝ => ∫ t,
      |(gh h t) (uh h t) -
        (g t) (u t)| ∂μ) (𝓝[>] 0) (𝓝 0)
  exact tendsto_h10DualPairing_of_sqNorm hΩ μ
    (u : ℝ → H10HilbertGraph hΩ) (g : ℝ → H10HilbertGraphDual hΩ)
    uh gh
    hu hg hraw huh hgh hU hG

private theorem tendsto_backwardSteklov_dualPairing_integral_on_Icc_raw
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < T) :
    Filter.Tendsto (backwardPairingErrorIntegral hΩ T u g a b)
      (𝓝[>] 0) (𝓝 0) := by
  let μ : Measure ℝ := volume.restrict (Icc a b)
  let uh := backwardPrimalAverage hΩ T u
  let gh := backwardDualAverage hΩ T g
  have hK : Icc a b ⊆ Ioo 0 T := by
    intro t ht
    exact ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
  have hu : MemLp (u : ℝ → H10HilbertGraph hΩ) (2 : ℝ≥0∞) μ := by
    simpa only [μ] using memLp_on_Icc_of_reverseTimeLp T u ha hb
  have hg : MemLp (g : ℝ → H10HilbertGraphDual hΩ) (2 : ℝ≥0∞) μ := by
    simpa only [μ] using memLp_on_Icc_of_reverseTimeLp T g ha hb
  have hraw : Integrable (fun t => (g t) (u t)) μ := by
    dsimp only [μ, reverseTimeVolume, reverseTimeOpenInterval]
    rw [← Measure.restrict_restrict_of_subset hK]
    exact (integrable_reverseTimeDualPairing hΩ T u g).restrict
  have huh : ∀ᶠ h : ℝ in 𝓝[>] 0,
      MemLp (uh h) (2 : ℝ≥0∞) μ := by
    filter_upwards [show ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h from self_mem_nhdsWithin]
      with h hh
    change MemLp (reverseTimeBackwardSteklov T h u) (2 : ℝ≥0∞) μ
    simpa only [μ] using memLp_on_Icc_of_continuous
      (reverseTimeBackwardSteklov T h u)
      (continuous_reverseTimeBackwardSteklov T h hh u) a b
  have hgh : ∀ᶠ h : ℝ in 𝓝[>] 0,
      MemLp (gh h) (2 : ℝ≥0∞) μ := by
    filter_upwards [show ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h from self_mem_nhdsWithin]
      with h hh
    change MemLp (reverseTimeBackwardSteklov T h g) (2 : ℝ≥0∞) μ
    simpa only [μ] using memLp_on_Icc_of_continuous
      (reverseTimeBackwardSteklov T h g)
      (continuous_reverseTimeBackwardSteklov T h hh g) a b
  have hU := tendsto_backwardSteklov_sqNorm_integral_on_Icc_restrict T u ha hab hb
  have hG := tendsto_backwardSteklov_sqNorm_integral_on_Icc_restrict T g ha hab hb
  change Tendsto (fun h : ℝ => ∫ t,
      |(gh h t) (uh h t) -
        (g t) (u t)| ∂μ) (𝓝[>] 0) (𝓝 0)
  exact tendsto_h10DualPairing_of_sqNorm hΩ μ
    (u : ℝ → H10HilbertGraph hΩ) (g : ℝ → H10HilbertGraphDual hΩ)
    uh gh
    hu hg hraw huh hgh hU hG

/-- Forward Steklov dual pairings converge locally in `L¹` on a strict
reverse-time interior interval. -/
theorem tendsto_forwardSteklov_dualPairing_integral_on_Icc
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < T) :
    Filter.Tendsto
      (fun h : ℝ => ∫ t in Set.Icc a b,
        |(reverseTimeForwardSteklov T h g t)
            (reverseTimeForwardSteklov T h u t) - (g t) (u t)|)
      (𝓝[>] 0) (𝓝 0) :=
  by
    have hresult := tendsto_forwardSteklov_dualPairing_integral_on_Icc_raw hΩ T u g ha hab hb
    unfold forwardPairingErrorIntegral forwardDualAverage forwardPrimalAverage at hresult
    exact hresult

/-- Backward Steklov dual pairings converge locally in `L¹` on a strict
reverse-time interior interval. -/
theorem tendsto_backwardSteklov_dualPairing_integral_on_Icc
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < T) :
    Filter.Tendsto
      (fun h : ℝ => ∫ t in Set.Icc a b,
        |(reverseTimeBackwardSteklov T h g t)
            (reverseTimeBackwardSteklov T h u t) - (g t) (u t)|)
      (𝓝[>] 0) (𝓝 0) :=
  by
    have hresult := tendsto_backwardSteklov_dualPairing_integral_on_Icc_raw hΩ T u g ha hab hb
    unfold backwardPairingErrorIntegral backwardDualAverage backwardPrimalAverage at hresult
    exact hresult

end HypoellipticAleksandrov.Parabolic.Dirichlet

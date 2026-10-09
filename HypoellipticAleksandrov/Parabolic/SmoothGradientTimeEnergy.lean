module

public import HypoellipticAleksandrov.Parabolic.LocalizedGradientDivergence
public import HypoellipticAleksandrov.Parabolic.Derivatives
public import HypoellipticAleksandrov.Measure.TimeVelocity
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Smooth gradient time-energy identity

This file develops the compact-support directional integration-by-parts
infrastructure for the smooth gradient time-energy identity.
-/

@[expose] public section

noncomputable section

open Function MeasureTheory Set
open scoped BigOperators Topology

namespace HypoellipticAleksandrov.Parabolic.WeakGradientTimeEnergy

private theorem integral_mul_fderiv_apply_eq_neg_of_right_compact
    {d : ℕ} (q : TimeVelocity d)
    (f g : TimeVelocity d → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgCompact : HasCompactSupport g) :
    (∫ z, f z * fderiv ℝ g z q
      ∂(volume : Measure (TimeVelocity d))) =
      -∫ z, fderiv ℝ f z q * g z
        ∂(volume : Measure (TimeVelocity d)) := by
  have hfCont : Continuous f := hf.continuous
  have hgCont : Continuous g := hg.continuous
  have hdfCont : Continuous (fun z => fderiv ℝ f z q) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdgCont : Continuous (fun z => fderiv ℝ g z q) :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdgCompact : HasCompactSupport (fun z => fderiv ℝ g z q) :=
    hgCompact.fderiv_apply ℝ q
  have hdfg : Integrable (fun z => fderiv ℝ f z q * g z) :=
    (hdfCont.mul hgCont).integrable_of_hasCompactSupport hgCompact.mul_left
  have hfdg : Integrable (fun z => f z * fderiv ℝ g z q) :=
    (hfCont.mul hdgCont).integrable_of_hasCompactSupport hdgCompact.mul_left
  have hfg : Integrable (fun z => f z * g z) :=
    (hfCont.mul hgCont).integrable_of_hasCompactSupport hgCompact.mul_left
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    hdfg hfdg hfg (fun x _ => hf.differentiable (by simp) x)
      (fun x _ => hg.differentiable (by simp) x)

private theorem integral_restrict_eq_integral_of_eq_zero_off
    {d : ℕ} (S : Set (TimeVelocity d)) (hS : MeasurableSet S)
    (f : TimeVelocity d → ℝ) (hoff : ∀ z ∉ S, f z = 0) :
    (∫ z in S, f z ∂volume) = ∫ z, f z ∂volume := by
  rw [← integral_indicator hS]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    by_cases hz : z ∈ S
    · simp [hz]
    · simp [hz, hoff z hz]

private theorem fderiv_timeVelocityCutoff
    {d : ℕ} (ζ : ℝ → ℝ) (η : PDE.Vec d → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun z : TimeVelocity d => ζ z.1 * η z.2 ^ 2) := by
  exact (hζ.comp (contDiff_fst (𝕜 := ℝ))).mul
    ((hη.comp (contDiff_snd (𝕜 := ℝ))).pow 2)

private theorem timeVelocityCutoff_hasCompactSupport
    {d : ℕ} (ζ : ℝ → ℝ) (η : PDE.Vec d → ℝ)
    (hζCompact : HasCompactSupport ζ)
    (hηCompact : HasCompactSupport η) :
    HasCompactSupport (fun z : TimeVelocity d => ζ z.1 * η z.2 ^ 2) := by
  have hprod : IsCompact (tsupport ζ ×ˢ tsupport η) :=
    hζCompact.isCompact.prod hηCompact.isCompact
  apply HasCompactSupport.of_support_subset_isCompact hprod
  intro z hz
  have hzζ : ζ z.1 ≠ 0 := by
    intro hzero
    exact hz (by simp [hzero])
  have hzη : η z.2 ≠ 0 := by
    intro hzero
    exact hz (by simp [hzero])
  exact ⟨subset_tsupport ζ (Function.mem_support.mpr hzζ),
    subset_tsupport η (Function.mem_support.mpr hzη)⟩

private theorem fderiv_fderiv_apply_comm
    {d : ℕ} (r : TimeVelocity d → ℝ)
    (hr : ContDiff ℝ (⊤ : ℕ∞) r)
    (z p q : TimeVelocity d) :
    fderiv ℝ (fun x => fderiv ℝ r x p) z q =
      fderiv ℝ (fun x => fderiv ℝ r x q) z p := by
  have hgrad : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ r) :=
    (contDiff_infty_iff_fderiv.mp hr).2
  have heval (a b : TimeVelocity d) :
      fderiv ℝ (fun x => fderiv ℝ r x a) z b =
        fderiv ℝ (fderiv ℝ r) z b a := by
    rw [fderiv_clm_apply
      (hgrad.differentiable (by simp) z)
      (differentiableAt_const (c := a))]
    rw [fderiv_const_apply]
    simp
  rw [heval p q, heval q p]
  have hrz : ContDiffAt ℝ (⊤ : ℕ∞) r z := hr.contDiffAt
  have hrzTwo : ContDiffAt ℝ 2 r z :=
    hrz.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  exact (hrzTwo.isSymmSndFDerivAt (by norm_num)).eq q p

private theorem velocity_time_mixed_comm
    {d : ℕ} (r : TimeVelocity d → ℝ)
    (hr : ContDiff ℝ (⊤ : ℕ∞) r)
    (i : Fin d) (z : TimeVelocity d) :
    fderiv ℝ (timeDerivative r) z (0, Pi.single i 1) =
      fderiv ℝ (fun x => velocityGradient r x i) z (1, 0) := by
  unfold timeDerivative velocityGradient
  exact fderiv_fderiv_apply_comm r hr z (1, 0) (0, Pi.single i 1)

private theorem velocityGradient_component_contDiff
    {d : ℕ} (r : TimeVelocity d → ℝ)
    (hr : ContDiff ℝ (⊤ : ℕ∞) r) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => velocityGradient r z i) := by
  unfold velocityGradient
  exact (contDiff_infty_iff_fderiv.mp hr).2.clm_apply contDiff_const

private theorem weightedVelocityGradient_contDiff
    {d : ℕ} (r : TimeVelocity d → ℝ)
    (hr : ContDiff ℝ (⊤ : ℕ∞) r)
    (η : PDE.Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun z : TimeVelocity d =>
        ζ z.1 * η z.2 ^ 2 * velocityGradient r z i) := by
  exact (fderiv_timeVelocityCutoff ζ η hζ hη).mul
    (velocityGradient_component_contDiff r hr i)

private theorem weightedVelocityGradient_hasCompactSupport
    {d : ℕ} (r : TimeVelocity d → ℝ)
    (η : PDE.Vec d → ℝ) (hηCompact : HasCompactSupport η)
    (ζ : ℝ → ℝ) (hζCompact : HasCompactSupport ζ)
    (i : Fin d) :
    HasCompactSupport
      (fun z : TimeVelocity d =>
        ζ z.1 * η z.2 ^ 2 * velocityGradient r z i) := by
  exact (timeVelocityCutoff_hasCompactSupport ζ η hζCompact hηCompact).mul_right

private theorem fderiv_timeVelocityCutoff_spatial
    {d : ℕ} (η : PDE.Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (i : Fin d) (z : TimeVelocity d) :
    fderiv ℝ (fun x : TimeVelocity d => ζ x.1 * η x.2 ^ 2) z
        (0, Pi.single i 1) =
      ζ z.1 * (2 * η z.2 * spatialPartial i η z.2) := by
  have hζDiff : DifferentiableAt ℝ (fun x : TimeVelocity d => ζ x.1) z :=
    (hζ.comp (contDiff_fst (𝕜 := ℝ))).differentiable (by simp) z
  have hηDiff : DifferentiableAt ℝ (fun x : TimeVelocity d => η x.2) z :=
    (hη.comp (contDiff_snd (𝕜 := ℝ))).differentiable (by simp) z
  rw [show (fun x : TimeVelocity d => ζ x.1 * η x.2 ^ 2) =
      (fun x => ζ x.1) * (fun x => η x.2) ^ 2 by rfl]
  rw [fderiv_mul hζDiff (hηDiff.pow 2)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  change ζ z.1 * fderiv ℝ (fun x : TimeVelocity d => η x.2 ^ 2) z
      (0, Pi.single i 1) + η z.2 ^ 2 *
      fderiv ℝ (fun x : TimeVelocity d => ζ x.1) z (0, Pi.single i 1) = _
  rw [fderiv_fun_pow 2 hηDiff]
  have hζzero : fderiv ℝ (fun x : TimeVelocity d => ζ x.1) z
      (0, Pi.single i 1) = 0 := by
    change fderiv ℝ (ζ ∘ Prod.fst) z (0, Pi.single i 1) = 0
    rw [fderiv_comp z (hζ.differentiable (by simp) z.1)
      (differentiableAt_fst (𝕜 := ℝ))]
    rw [fderiv_fst]
    simp
  have hηeval : fderiv ℝ (fun x : TimeVelocity d => η x.2) z
      (0, Pi.single i 1) = spatialPartial i η z.2 := by
    change fderiv ℝ (η ∘ Prod.snd) z (0, Pi.single i 1) = _
    rw [fderiv_comp z (hη.differentiable (by simp) z.2)
      (differentiableAt_snd (𝕜 := ℝ))]
    rw [fderiv_snd]
    rfl
  rw [hζzero]
  simp only [ContinuousLinearMap.smul_apply, Nat.reduceSub, pow_one,
    nsmul_eq_mul, Nat.cast_ofNat]
  rw [hηeval]
  simp only [smul_eq_mul]
  ring

private theorem fderiv_velocityGradient_component_spatial
    {d : ℕ} (r : TimeVelocity d → ℝ)
    (hr : ContDiff ℝ (⊤ : ℕ∞) r)
    (i : Fin d) (z : TimeVelocity d) :
    fderiv ℝ (fun x => velocityGradient r x i) z (0, Pi.single i 1) =
      velocityHessian r z i i := by
  unfold velocityGradient velocityHessian
  have hgrad : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ r) :=
    (contDiff_infty_iff_fderiv.mp hr).2
  rw [fderiv_clm_apply
    (hgrad.differentiable (by simp) z)
    (differentiableAt_const (c := ((0, Pi.single i 1) : TimeVelocity d)))]
  rw [fderiv_const_apply]
  simp

private theorem fderiv_weightedVelocityGradient_spatial
    {d : ℕ} (r : TimeVelocity d → ℝ)
    (hr : ContDiff ℝ (⊤ : ℕ∞) r)
    (η : PDE.Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (i : Fin d) (z : TimeVelocity d) :
    fderiv ℝ (fun x : TimeVelocity d =>
      ζ x.1 * η x.2 ^ 2 * velocityGradient r x i) z
        (0, Pi.single i 1) =
      ζ z.1 *
        (2 * η z.2 * spatialPartial i η z.2 * velocityGradient r z i +
          η z.2 ^ 2 * velocityHessian r z i i) := by
  let c : TimeVelocity d → ℝ := fun x => ζ x.1 * η x.2 ^ 2
  let v : TimeVelocity d → ℝ := fun x => velocityGradient r x i
  have hc : DifferentiableAt ℝ c z :=
    (fderiv_timeVelocityCutoff ζ η hζ hη).differentiable (by simp) z
  have hv : DifferentiableAt ℝ v z :=
    (velocityGradient_component_contDiff r hr i).differentiable (by simp) z
  change fderiv ℝ (c * v) z (0, Pi.single i 1) = _
  rw [fderiv_mul hc hv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, c, v]
  rw [fderiv_timeVelocityCutoff_spatial η hη ζ hζ i z,
    fderiv_velocityGradient_component_spatial r hr i z]
  ring

private theorem fderiv_timeVelocityCutoff_time
    {d : ℕ} (η : PDE.Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (z : TimeVelocity d) :
    fderiv ℝ (fun x : TimeVelocity d => ζ x.1 * η x.2 ^ 2) z (1, 0) =
      _root_.deriv ζ z.1 * η z.2 ^ 2 := by
  have hζDiff : DifferentiableAt ℝ (fun x : TimeVelocity d => ζ x.1) z :=
    (hζ.comp (contDiff_fst (𝕜 := ℝ))).differentiable (by simp) z
  have hηDiff : DifferentiableAt ℝ (fun x : TimeVelocity d => η x.2) z :=
    (hη.comp (contDiff_snd (𝕜 := ℝ))).differentiable (by simp) z
  rw [show (fun x : TimeVelocity d => ζ x.1 * η x.2 ^ 2) =
      (fun x => ζ x.1) * (fun x => η x.2) ^ 2 by rfl]
  rw [fderiv_mul hζDiff (hηDiff.pow 2)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  change ζ z.1 * fderiv ℝ (fun x : TimeVelocity d => η x.2 ^ 2) z (1, 0) +
      η z.2 ^ 2 * fderiv ℝ (fun x : TimeVelocity d => ζ x.1) z (1, 0) = _
  rw [fderiv_fun_pow 2 hηDiff]
  have hηzero : fderiv ℝ (fun x : TimeVelocity d => η x.2) z (1, 0) = 0 := by
    change fderiv ℝ (η ∘ Prod.snd) z (1, 0) = 0
    rw [fderiv_comp z (hη.differentiable (by simp) z.2)
      (differentiableAt_snd (𝕜 := ℝ)), fderiv_snd]
    simp
  have hζeval : fderiv ℝ (fun x : TimeVelocity d => ζ x.1) z (1, 0) =
      _root_.deriv ζ z.1 := by
    change fderiv ℝ (ζ ∘ Prod.fst) z (1, 0) = _
    rw [fderiv_comp z (hζ.differentiable (by simp) z.1)
      (differentiableAt_fst (𝕜 := ℝ)), fderiv_fst]
    rfl
  rw [hζeval]
  simp only [ContinuousLinearMap.smul_apply, Nat.reduceSub, pow_one,
    nsmul_eq_mul, Nat.cast_ofNat, hηzero, mul_zero, smul_zero, zero_add]
  ring

private theorem fderiv_weightedVelocityGradient_sq_time
    {d : ℕ} (r : TimeVelocity d → ℝ)
    (hr : ContDiff ℝ (⊤ : ℕ∞) r)
    (η : PDE.Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (i : Fin d) (z : TimeVelocity d) :
    fderiv ℝ (fun x : TimeVelocity d =>
      ζ x.1 * η x.2 ^ 2 * velocityGradient r x i ^ 2) z (1, 0) =
      _root_.deriv ζ z.1 * η z.2 ^ 2 * velocityGradient r z i ^ 2 +
        2 * ζ z.1 * η z.2 ^ 2 *
          fderiv ℝ (fun x => velocityGradient r x i) z (1, 0) *
            velocityGradient r z i := by
  let c : TimeVelocity d → ℝ := fun x => ζ x.1 * η x.2 ^ 2
  let v : TimeVelocity d → ℝ := fun x => velocityGradient r x i
  have hc : DifferentiableAt ℝ c z :=
    (fderiv_timeVelocityCutoff ζ η hζ hη).differentiable (by simp) z
  have hv : DifferentiableAt ℝ v z :=
    (velocityGradient_component_contDiff r hr i).differentiable (by simp) z
  change fderiv ℝ (c * v ^ 2) z (1, 0) = _
  rw [fderiv_mul hc (hv.pow 2)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, c, v]
  change c z * fderiv ℝ (fun x => v x ^ 2) z (1, 0) +
      v z ^ 2 * fderiv ℝ c z (1, 0) = _
  rw [fderiv_fun_pow 2 hv, fderiv_timeVelocityCutoff_time η hη ζ hζ z]
  simp only [ContinuousLinearMap.smul_apply, Nat.reduceSub, pow_one,
    nsmul_eq_mul, Nat.cast_ofNat, smul_eq_mul, c, v]
  ring

private theorem timeDerivative_contDiff
    {d : ℕ} (r : TimeVelocity d → ℝ)
    (hr : ContDiff ℝ (⊤ : ℕ∞) r) :
    ContDiff ℝ (⊤ : ℕ∞) (timeDerivative r) := by
  unfold timeDerivative
  exact (contDiff_infty_iff_fderiv.mp hr).2.clm_apply contDiff_const

private theorem global_coordinate_timeEnergy
    {d : ℕ} (r : TimeVelocity d → ℝ)
    (hr : ContDiff ℝ (⊤ : ℕ∞) r)
    (η : PDE.Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηCompact : HasCompactSupport η)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζCompact : HasCompactSupport ζ)
    (i : Fin d) :
    2 * (∫ z : TimeVelocity d,
      timeDerivative r z *
        (-(ζ z.1 *
          (2 * η z.2 * spatialPartial i η z.2 * velocityGradient r z i +
            η z.2 ^ 2 * velocityHessian r z i i))) ∂volume) =
      -(∫ z : TimeVelocity d,
        _root_.deriv ζ z.1 * η z.2 ^ 2 * velocityGradient r z i ^ 2
          ∂volume) := by
  let w : TimeVelocity d → ℝ := fun z => ζ z.1 * η z.2 ^ 2
  let v : TimeVelocity d → ℝ := fun z => velocityGradient r z i
  let g : TimeVelocity d → ℝ := fun z => w z * v z
  have hgSmooth : ContDiff ℝ (⊤ : ℕ∞) g :=
    weightedVelocityGradient_contDiff r hr η hη ζ hζ i
  have hgCompact : HasCompactSupport g :=
    weightedVelocityGradient_hasCompactSupport r η hηCompact ζ hζCompact i
  have hspatial := integral_mul_fderiv_apply_eq_neg_of_right_compact
    ((0, Pi.single i 1) : TimeVelocity d) (timeDerivative r) g
    (timeDerivative_contDiff r hr) hgSmooth hgCompact
  have hwSmooth : ContDiff ℝ (⊤ : ℕ∞) w :=
    fderiv_timeVelocityCutoff ζ η hζ hη
  have hwCompact : HasCompactSupport w :=
    timeVelocityCutoff_hasCompactSupport ζ η hζCompact hηCompact
  have hvSmooth : ContDiff ℝ (⊤ : ℕ∞) v :=
    velocityGradient_component_contDiff r hr i
  have htime := integral_mul_fderiv_apply_eq_neg_of_right_compact
    ((1, 0) : TimeVelocity d) (fun z => v z ^ 2) w
    (hvSmooth.pow 2) hwSmooth hwCompact
  have hspatial' :
      (∫ z : TimeVelocity d,
        timeDerivative r z *
          (ζ z.1 *
            (2 * η z.2 * spatialPartial i η z.2 * velocityGradient r z i +
              η z.2 ^ 2 * velocityHessian r z i i)) ∂volume) =
        -(∫ z : TimeVelocity d,
          fderiv ℝ (timeDerivative r) z (0, Pi.single i 1) *
            (ζ z.1 * η z.2 ^ 2 * velocityGradient r z i) ∂volume) := by
    simpa only [g, w, v, fderiv_weightedVelocityGradient_spatial r hr η hη ζ hζ i]
      using hspatial
  have htime' :
      (∫ z : TimeVelocity d,
        velocityGradient r z i ^ 2 *
          (_root_.deriv ζ z.1 * η z.2 ^ 2) ∂volume) =
        -(∫ z : TimeVelocity d,
          (2 * ζ z.1 * η z.2 ^ 2 *
            fderiv ℝ (fun x => velocityGradient r x i) z (1, 0) *
              velocityGradient r z i) ∂volume) := by
    calc
      (∫ z, velocityGradient r z i ^ 2 *
          (_root_.deriv ζ z.1 * η z.2 ^ 2) ∂volume) =
          ∫ z, (fun x => v x ^ 2) z * fderiv ℝ w z (1, 0) ∂volume := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => by
          dsimp [w, v]
          rw [fderiv_timeVelocityCutoff_time η hη ζ hζ z]
      _ = -(∫ z, fderiv ℝ (fun x => v x ^ 2) z (1, 0) * w z ∂volume) := htime
      _ = -(∫ z, 2 * ζ z.1 * η z.2 ^ 2 *
          fderiv ℝ (fun x => velocityGradient r x i) z (1, 0) *
            velocityGradient r z i ∂volume) := by
        congr 1
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => by
          dsimp [w, v]
          rw [fderiv_fun_pow 2 (hvSmooth.differentiable (by simp) z)]
          simp only [ContinuousLinearMap.smul_apply, Nat.reduceSub, pow_one,
            nsmul_eq_mul, Nat.cast_ofNat, smul_eq_mul]
          ring
  have hleftNeg :
      (∫ z : TimeVelocity d,
        timeDerivative r z *
          -(ζ z.1 *
            (2 * η z.2 * spatialPartial i η z.2 * velocityGradient r z i +
              η z.2 ^ 2 * velocityHessian r z i i)) ∂volume) =
        -(∫ z : TimeVelocity d,
          timeDerivative r z *
            (ζ z.1 *
              (2 * η z.2 * spatialPartial i η z.2 * velocityGradient r z i +
                η z.2 ^ 2 * velocityHessian r z i i)) ∂volume) := by
    rw [← integral_neg]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by ring
  rw [hleftNeg, hspatial', neg_neg]
  have hmixed (z : TimeVelocity d) :
      fderiv ℝ (timeDerivative r) z (0, Pi.single i 1) =
        fderiv ℝ (fun x => velocityGradient r x i) z (1, 0) :=
    velocity_time_mixed_comm r hr i z
  have hpair :
      (∫ z : TimeVelocity d,
        fderiv ℝ (timeDerivative r) z (0, Pi.single i 1) *
          (ζ z.1 * η z.2 ^ 2 * velocityGradient r z i) ∂volume) =
        ∫ z : TimeVelocity d,
          ζ z.1 * η z.2 ^ 2 *
            fderiv ℝ (fun x => velocityGradient r x i) z (1, 0) *
              velocityGradient r z i ∂volume := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by
      dsimp only
      rw [hmixed z]
      ring
  rw [hpair]
  have htimeNorm :
      (∫ z : TimeVelocity d,
        velocityGradient r z i ^ 2 *
          (_root_.deriv ζ z.1 * η z.2 ^ 2) ∂volume) =
        -(2 * ∫ z : TimeVelocity d,
          ζ z.1 * η z.2 ^ 2 *
            fderiv ℝ (fun x => velocityGradient r x i) z (1, 0) *
              velocityGradient r z i ∂volume) := by
    calc
      _ = -(∫ z : TimeVelocity d, 2 *
          (ζ z.1 * η z.2 ^ 2 *
            fderiv ℝ (fun x => velocityGradient r x i) z (1, 0) *
              velocityGradient r z i) ∂volume) := by
        rw [htime']
        congr 1
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => by ring
      _ = _ := by rw [integral_const_mul]
  calc
    2 * ∫ z, ζ z.1 * η z.2 ^ 2 *
        fderiv ℝ (fun x => velocityGradient r x i) z (1, 0) *
          velocityGradient r z i ∂volume =
        -(∫ z, velocityGradient r z i ^ 2 *
          (_root_.deriv ζ z.1 * η z.2 ^ 2) ∂volume) := by linarith
    _ = -(∫ z, _root_.deriv ζ z.1 * η z.2 ^ 2 *
        velocityGradient r z i ^ 2 ∂volume) := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by ring

private theorem global_timeEnergy
    {d : ℕ} (r : TimeVelocity d → ℝ)
    (hr : ContDiff ℝ (⊤ : ℕ∞) r)
    (η : PDE.Vec d → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηCompact : HasCompactSupport η)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζCompact : HasCompactSupport ζ) :
    2 * (∫ z : TimeVelocity d,
      ζ z.1 * timeDerivative r z *
        localizedGradientDivergence η
          (fun z i => velocityGradient r z i)
          (fun z i j => velocityHessian r z i j) z ∂volume) =
      -(∫ z : TimeVelocity d,
        _root_.deriv ζ z.1 * η z.2 ^ 2 *
          ∑ i : Fin d, velocityGradient r z i ^ 2 ∂volume) := by
  let L : Fin d → TimeVelocity d → ℝ := fun i z =>
    timeDerivative r z *
      -(ζ z.1 *
        (2 * η z.2 * spatialPartial i η z.2 * velocityGradient r z i +
          η z.2 ^ 2 * velocityHessian r z i i))
  let R : Fin d → TimeVelocity d → ℝ := fun i z =>
    _root_.deriv ζ z.1 * η z.2 ^ 2 * velocityGradient r z i ^ 2
  have hLInt (i : Fin d) : Integrable (L i) := by
    let g : TimeVelocity d → ℝ := fun z =>
      ζ z.1 * η z.2 ^ 2 * velocityGradient r z i
    have hgSmooth : ContDiff ℝ (⊤ : ℕ∞) g :=
      weightedVelocityGradient_contDiff r hr η hη ζ hζ i
    have hgCompact : HasCompactSupport g :=
      weightedVelocityGradient_hasCompactSupport r η hηCompact ζ hζCompact i
    have hdgCompact : HasCompactSupport
        (fun z => fderiv ℝ g z (0, Pi.single i 1)) :=
      hgCompact.fderiv_apply ℝ (0, Pi.single i 1)
    have hbase : Integrable (fun z : TimeVelocity d =>
        timeDerivative r z * fderiv ℝ g z (0, Pi.single i 1)) :=
      ((timeDerivative_contDiff r hr).continuous.mul
        ((hgSmooth.continuous_fderiv (by simp)).clm_apply
          continuous_const)).integrable_of_hasCompactSupport
          hdgCompact.mul_left
    refine hbase.neg.congr (Filter.Eventually.of_forall fun z => ?_)
    dsimp [L, g]
    rw [fderiv_weightedVelocityGradient_spatial r hr η hη ζ hζ i]
    ring
  have hRInt (i : Fin d) : Integrable (R i) := by
    let w : TimeVelocity d → ℝ := fun z => ζ z.1 * η z.2 ^ 2
    let v : TimeVelocity d → ℝ := fun z => velocityGradient r z i
    have hwSmooth : ContDiff ℝ (⊤ : ℕ∞) w :=
      fderiv_timeVelocityCutoff ζ η hζ hη
    have hwCompact : HasCompactSupport w :=
      timeVelocityCutoff_hasCompactSupport ζ η hζCompact hηCompact
    have hvSmooth : ContDiff ℝ (⊤ : ℕ∞) v :=
      velocityGradient_component_contDiff r hr i
    have hdwCompact : HasCompactSupport (fun z => fderiv ℝ w z (1, 0)) :=
      hwCompact.fderiv_apply ℝ (1, 0)
    have hbase : Integrable (fun z : TimeVelocity d =>
        v z ^ 2 * fderiv ℝ w z (1, 0)) :=
      ((hvSmooth.pow 2).continuous.mul
        ((hwSmooth.continuous_fderiv (by simp)).clm_apply
          continuous_const)).integrable_of_hasCompactSupport
          hdwCompact.mul_left
    refine hbase.congr (Filter.Eventually.of_forall fun z => ?_)
    dsimp [R, w, v]
    rw [fderiv_timeVelocityCutoff_time η hη ζ hζ z]
    ring
  calc
    2 * (∫ z : TimeVelocity d,
        ζ z.1 * timeDerivative r z *
          localizedGradientDivergence η
            (fun z i => velocityGradient r z i)
            (fun z i j => velocityHessian r z i j) z ∂volume) =
        2 * ∫ z : TimeVelocity d, ∑ i : Fin d, L i z ∂volume := by
      apply congrArg (fun x : ℝ => 2 * x)
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        simp only [localizedGradientDivergence, L]
        rw [← Finset.sum_neg_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
    _ = ∑ i : Fin d, 2 * ∫ z : TimeVelocity d, L i z ∂volume := by
      rw [integral_finset_sum Finset.univ (fun i _ => hLInt i), Finset.mul_sum]
    _ = ∑ i : Fin d, -(∫ z : TimeVelocity d, R i z ∂volume) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact global_coordinate_timeEnergy r hr η hη hηCompact ζ hζ hζCompact i
    _ = -(∑ i : Fin d, ∫ z : TimeVelocity d, R i z ∂volume) := by
      rw [Finset.sum_neg_distrib]
    _ = -(∫ z : TimeVelocity d, ∑ i : Fin d, R i z ∂volume) := by
      rw [integral_finset_sum Finset.univ (fun i _ => hRInt i)]
    _ = -(∫ z : TimeVelocity d,
        _root_.deriv ζ z.1 * η z.2 ^ 2 *
          ∑ i : Fin d, velocityGradient r z i ^ 2 ∂volume) := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        simp only [R, Finset.mul_sum]

/-- Smooth compactly supported gradient time-energy identity on a literal
product cylinder. -/
theorem smoothGradient_timeEnergy
    {d : ℕ} (s₀ s₁ : ℝ)
    (O : Set (PDE.Vec d)) (hO : IsOpen O)
    (r : TimeVelocity d → ℝ)
    (hr : ContDiff ℝ (⊤ : ℕ∞) r)
    (η : PDE.Vec d → ℝ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηcompact : HasCompactSupport η)
    (hηsupport : tsupport η ⊆ O)
    (ζ : ℝ → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζcompact : HasCompactSupport ζ)
    (hζsupport : tsupport ζ ⊆ Set.Ioo s₀ s₁) :
    2 * (∫ z in Set.Ioo s₀ s₁ ×ˢ O,
        ζ z.1 * timeDerivative r z *
          localizedGradientDivergence η
            (fun z i => velocityGradient r z i)
            (fun z i j => velocityHessian r z i j) z
        ∂volume) =
      -(∫ z in Set.Ioo s₀ s₁ ×ˢ O,
        _root_.deriv ζ z.1 * η z.2 ^ 2 *
          ∑ i : Fin d, velocityGradient r z i ^ 2
        ∂volume) := by
  let S : Set (TimeVelocity d) := Set.Ioo s₀ s₁ ×ˢ O
  have hS : MeasurableSet S := measurableSet_Ioo.prod hO.measurableSet
  let F : TimeVelocity d → ℝ := fun z =>
    ζ z.1 * timeDerivative r z *
      localizedGradientDivergence η
        (fun z i => velocityGradient r z i)
        (fun z i j => velocityHessian r z i j) z
  let G : TimeVelocity d → ℝ := fun z =>
    _root_.deriv ζ z.1 * η z.2 ^ 2 *
      ∑ i : Fin d, velocityGradient r z i ^ 2
  have hFoff : ∀ z ∉ S, F z = 0 := by
    intro z hz
    by_cases ht : z.1 ∈ Set.Ioo s₀ s₁
    · have hv : z.2 ∉ O := by
        intro hv
        exact hz ⟨ht, hv⟩
      have hnot : z.2 ∉ tsupport η := fun hmem => hv (hηsupport hmem)
      have hzero : η z.2 = 0 := image_eq_zero_of_notMem_tsupport hnot
      simp [F, localizedGradientDivergence, hzero]
    · have hnot : z.1 ∉ tsupport ζ := fun hmem => ht (hζsupport hmem)
      have hzero : ζ z.1 = 0 := image_eq_zero_of_notMem_tsupport hnot
      simp [F, hzero]
  have hGoff : ∀ z ∉ S, G z = 0 := by
    intro z hz
    by_cases ht : z.1 ∈ Set.Ioo s₀ s₁
    · have hv : z.2 ∉ O := by
        intro hv
        exact hz ⟨ht, hv⟩
      have hnot : z.2 ∉ tsupport η := fun hmem => hv (hηsupport hmem)
      have hzero : η z.2 = 0 := image_eq_zero_of_notMem_tsupport hnot
      simp [G, hzero]
    · have hnot : z.1 ∉ tsupport ζ := fun hmem => ht (hζsupport hmem)
      have hzero : _root_.deriv ζ z.1 = 0 := by
        rw [← fderiv_apply_one_eq_deriv, fderiv_of_notMem_tsupport ℝ hnot]
        rfl
      simp [G, hzero]
  have hFrestrict : (∫ z in S, F z ∂volume) = ∫ z, F z ∂volume :=
    integral_restrict_eq_integral_of_eq_zero_off S hS F hFoff
  have hGrestrict : (∫ z in S, G z ∂volume) = ∫ z, G z ∂volume :=
    integral_restrict_eq_integral_of_eq_zero_off S hS G hGoff
  change 2 * (∫ z in S, F z ∂volume) = -(∫ z in S, G z ∂volume)
  rw [hFrestrict, hGrestrict]
  exact global_timeEnergy r hr η hη hηcompact ζ hζ hζcompact

end HypoellipticAleksandrov.Parabolic.WeakGradientTimeEnergy

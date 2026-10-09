module

public import PDEFoundation.Measure.FiniteVectorConvergence
public import PDEFoundation.Measure.LpTendsto
public import PDEFoundation.Measure.NormalizedLpTendsto
public import PDEFoundation.Sobolev.W1p.ConvexApprox.Convergence
public import PDEFoundation.Sobolev.W1p.EuclideanGradient
public import PDEFoundation.Sobolev.W1p.Mean
public import PDEFoundation.Sobolev.W1p.Smooth

/-!
# Smooth density on bounded open convex domains

This file packages convex approximation as a sequence of smooth
`W1pFunction`s and records its exact convergence properties for every finite
exponent `p ≥ 1`.

The native gradient remains `Vec d`-valued. Coordinatewise convergence is
exported for compatibility, while the public gradient norm is the exact
Euclidean norm obtained through the internal Hilbert lift. Finite coordinate
sums occur only inside the convergence majorant supplied by
`PDEFoundation.Measure.FiniteVectorConvergence`.

Centering is performed against `normalizedVolumeOn U`, so convergence of
arithmetic means and centered values includes the endpoint `p = 1`.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE

open Filter MeasureTheory

namespace W1pFunction

variable {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}

/-- The smooth `W^{1,p}` representative obtained from the standard convex
approximation kernel and scale. -/
noncomputable def convexApproxSmoothW1p
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (u : W1pFunction U p)
    (x0 : Vec d) {r : ℝ} (hr : 0 < r)
    (n : ℕ) : W1pFunction U p :=
  W1pFunction.ofContDiffOnIsOpenBoundedConvexDomain hU
    ((contDiff_convexApproxSmoothRepresentative
      (U := U)
      (ρ := unitConvexApproxKernel (d := d))
      (u := u.toFun) (p := p)
      (x0 := x0) (r := r)
      (ε := unitConvexApproxScale n)
      hU.measurableSet
      (isConvexApproxKernel_unitConvexApproxKernel
        (d := d))
      hp u.memLp hr
      (unitConvexApproxScale_pos n)).of_le (by simp))

@[simp]
theorem convexApproxSmoothW1p_toFun
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (u : W1pFunction U p)
    (x0 : Vec d) {r : ℝ} (hr : 0 < r)
    (n : ℕ) :
    (convexApproxSmoothW1p hU hp u x0 hr n).toFun =
      convexApproxSmoothRepresentative U
        (unitConvexApproxKernel (d := d))
        u.toFun x0 r (unitConvexApproxScale n) :=
  rfl

@[simp]
theorem convexApproxSmoothW1p_grad
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (u : W1pFunction U p)
    (x0 : Vec d) {r : ℝ} (hr : 0 < r)
    (n : ℕ) :
    (convexApproxSmoothW1p hU hp u x0 hr n).grad =
      classicalGradient
        (convexApproxSmoothRepresentative U
          (unitConvexApproxKernel (d := d))
          u.toFun x0 r (unitConvexApproxScale n)) :=
  rfl

@[simp]
theorem convexApproxSmoothW1p_grad_apply
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (u : W1pFunction U p)
    (x0 : Vec d) {r : ℝ} (hr : 0 < r)
    (n : ℕ) (x : Vec d) (i : Fin d) :
    (convexApproxSmoothW1p hU hp u x0 hr n).grad x i =
      (fderiv ℝ
        (convexApproxSmoothRepresentative U
          (unitConvexApproxKernel (d := d))
          u.toFun x0 r (unitConvexApproxScale n)) x)
        (basisVec i) := by
  rw [convexApproxSmoothW1p_grad,
    classicalGradient_apply]

/-- Every member of the convex approximation sequence has a globally smooth
value representative. -/
theorem contDiff_convexApproxSmoothW1p_toFun
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (u : W1pFunction U p)
    (x0 : Vec d) {r : ℝ} (hr : 0 < r)
    (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (convexApproxSmoothW1p hU hp u x0 hr n).toFun := by
  rw [convexApproxSmoothW1p_toFun]
  exact
    contDiff_convexApproxSmoothRepresentative
      hU.measurableSet
      (isConvexApproxKernel_unitConvexApproxKernel
        (d := d))
      hp u.memLp hr (unitConvexApproxScale_pos n)

/-- The values of the smooth convex approximants converge in
`L^p(U)` for every finite `p ≥ 1`. -/
theorem tendsto_convexApproxSmoothW1p_toFun_eLpNorm_sub
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p)
    {x0 : Vec d} {r : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) :
    Tendsto
      (fun n =>
        eLpNorm
          (fun x =>
            (convexApproxSmoothW1p hU hp u x0 hr n).toFun x -
              u.toFun x)
          p (volumeOn U))
      atTop (𝓝 0) := by
  let ρ : Vec d → ℝ :=
    unitConvexApproxKernel (d := d)
  have hρ : IsConvexApproxKernel ρ := by
    simpa only [ρ] using
      isConvexApproxKernel_unitConvexApproxKernel
        (d := d)
  have hScaleOne :
      ∀ᶠ n : ℕ in atTop,
        unitConvexApproxScale n < 1 :=
    (((tendsto_order.1
      tendsto_unitConvexApproxScale_zero).2
        1 zero_lt_one).mono fun _ hn => hn)
  have hRaw :
      Tendsto
        (fun n =>
          eLpNorm
            (fun x =>
              convexApproxSmoothing ρ u.toFun x0 r
                  (unitConvexApproxScale n) x -
                u.toFun x)
            p (volumeOn U))
        atTop (𝓝 0) := by
    simpa only [ρ, unitConvexApproxSequence] using
      tendsto_eLpNorm_sub_zero_unitConvexApproxSequence_of_memLpOn
        hU hp hpTop u.memLp hball hr
  have hRepresentative :
      Tendsto
        (fun n =>
          eLpNorm
            (fun x =>
              convexApproxSmoothRepresentative U ρ u.toFun
                  x0 r (unitConvexApproxScale n) x -
                u.toFun x)
            p (volumeOn U))
        atTop (𝓝 0) := by
    refine hRaw.congr' ?_
    filter_upwards [hScaleOne] with n hScale
    apply eLpNorm_congr_ae
    filter_upwards
      [ae_restrict_mem hU.measurableSet] with x hx
    rw [
      convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
        (u := u.toFun) hU hρ hx hball hr
        (unitConvexApproxScale_pos n) hScale]
  simpa only [convexApproxSmoothW1p_toFun, ρ] using
    hRepresentative

/-- Every coordinate of the weak gradient of the smooth convex approximants
converges in `L^p(U)`. -/
theorem tendsto_convexApproxSmoothW1p_grad_coord_eLpNorm_sub
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p)
    {x0 : Vec d} {r : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) (i : Fin d) :
    Tendsto
      (fun n =>
        eLpNorm
          (fun x =>
            (convexApproxSmoothW1p hU hp u x0 hr n).grad x i -
              u.grad x i)
          p (volumeOn U))
      atTop (𝓝 0) := by
  let ρ : Vec d → ℝ :=
    unitConvexApproxKernel (d := d)
  have hρ : IsConvexApproxKernel ρ := by
    simpa only [ρ] using
      isConvexApproxKernel_unitConvexApproxKernel
        (d := d)
  have hScaleOne :
      ∀ᶠ n : ℕ in atTop,
        unitConvexApproxScale n < 1 :=
    (((tendsto_order.1
      tendsto_unitConvexApproxScale_zero).2
        1 zero_lt_one).mono fun _ hn => hn)
  have hRaw :
      Tendsto
        (fun n =>
          eLpNorm
            (fun x =>
              (1 - unitConvexApproxScale n) *
                  convexApproxSmoothing ρ
                    (fun y => u.grad y i)
                    x0 r (unitConvexApproxScale n) x -
                u.grad x i)
            p (volumeOn U))
        atTop (𝓝 0) := by
    simpa only [ρ, unitConvexApproxSequence] using
      tendsto_eLpNorm_sub_zero_one_sub_mul_unitConvexApproxSequence_of_memLpOn
        hU hp hpTop (u.grad_memLp i) hball hr
  have hRepresentative :
      Tendsto
        (fun n =>
          eLpNorm
            (fun x =>
              (fderiv ℝ
                (convexApproxSmoothRepresentative U ρ u.toFun
                  x0 r (unitConvexApproxScale n)) x)
                  (basisVec i) -
                u.grad x i)
            p (volumeOn U))
        atTop (𝓝 0) := by
    refine hRaw.congr' ?_
    filter_upwards [hScaleOne] with n hScale
    apply eLpNorm_congr_ae
    have hBridge :=
      ae_eq_fderiv_convexApproxSmoothRepresentative_apply_basisVec
        (U := U) (ρ := ρ) (u := u.toFun)
        (gi := fun y => u.grad y i)
        (i := i) (p := p)
        hU hρ hp u.memLp (u.grad_memLp i)
        (u.hasWeakPartialDerivOn i)
        hball hr (unitConvexApproxScale_pos n) hScale
    filter_upwards
      [hBridge, ae_restrict_mem hU.measurableSet] with
      x hxBridge hxU
    rw [hxBridge]
    rw [
      convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
        (u := fun y => u.grad y i)
        hU hρ hxU hball hr
        (unitConvexApproxScale_pos n) hScale]
  simpa only [convexApproxSmoothW1p_grad_apply, ρ] using
    hRepresentative

/-- The exact Euclidean magnitude of the gradient difference converges to
zero in `L^p(U)`. The finite coordinate sum is used only inside the proof as a
majorant. -/
theorem
    tendsto_convexApproxSmoothW1p_grad_euclidean_eLpNorm_sub
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p)
    {x0 : Vec d} {r : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) :
    Tendsto
      (fun n =>
        eLpNorm
          (fun x =>
            vecEuclideanNorm
              ((convexApproxSmoothW1p hU hp u x0 hr n).grad x -
                u.grad x))
          p (volumeOn U))
      atTop (𝓝 0) := by
  apply
    tendsto_eLpNorm_vecEuclideanNorm_sub_zero_of_coordinate
      (F := fun n x =>
        (convexApproxSmoothW1p hU hp u x0 hr n).grad x)
      (G := u.grad) hp
  · intro n i
    have hApproxMeas :=
      ((convexApproxSmoothW1p hU hp u x0 hr n).grad_memLp i).aestronglyMeasurable
    exact
      hApproxMeas.sub (u.grad_memLp i).aestronglyMeasurable
  · intro i
    exact
      tendsto_convexApproxSmoothW1p_grad_coord_eLpNorm_sub
        hU hp hpTop u hball hr i

/-- Hilbert-lift form of exact Euclidean-gradient difference convergence.
The lift is internal; its norm is definitionally bridged back to
`vecEuclideanNorm`. -/
theorem
    tendsto_convexApproxSmoothW1p_grad_hilbert_eLpNorm_sub
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p)
    {x0 : Vec d} {r : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) :
    Tendsto
      (fun n =>
        eLpNorm
          (toHilbertVecField
            (fun x =>
              (convexApproxSmoothW1p hU hp u x0 hr n).grad x -
                u.grad x))
          p (volumeOn U))
      atTop (𝓝 0) := by
  have hEq : ∀ n,
      eLpNorm
          (toHilbertVecField
            (fun x =>
              (convexApproxSmoothW1p hU hp u x0 hr n).grad x - u.grad x))
          p (volumeOn U) =
        eLpNorm
          (fun x => vecEuclideanNorm
            ((convexApproxSmoothW1p hU hp u x0 hr n).grad x - u.grad x))
          p (volumeOn U) :=
    fun n => eLpNorm_toHilbertVecField_eq _ _ _
      (aemeasurable_pi_iff.2 fun i =>
        (((convexApproxSmoothW1p hU hp u x0 hr n).grad_memLp i).aestronglyMeasurable.sub
          (u.grad_memLp i).aestronglyMeasurable).aemeasurable).aestronglyMeasurable
  simpa only [hEq] using
    tendsto_convexApproxSmoothW1p_grad_euclidean_eLpNorm_sub
      hU hp hpTop u hball hr

private theorem toHilbertVecField_sub
    (F G : Vec d → Vec d) :
    toHilbertVecField F - toHilbertVecField G =
      toHilbertVecField (fun x => F x - G x) := by
  funext x
  ext i
  rfl

/-- The `L^p` norms of the Hilbert lifts of the gradients converge. This is
the normed-space bridge used to obtain exact Euclidean-gradient norm
convergence. -/
theorem
    tendsto_convexApproxSmoothW1p_grad_hilbert_eLpNorm
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p)
    {x0 : Vec d} {r : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) :
    Tendsto
      (fun n =>
        eLpNorm
          (toHilbertVecField
            (convexApproxSmoothW1p hU hp u x0 hr n).grad)
          p (volumeOn U))
      atTop
      (𝓝
        (eLpNorm (toHilbertVecField u.grad)
          p (volumeOn U))) := by
  let ψ : ℕ → W1pFunction U p :=
    convexApproxSmoothW1p hU hp u x0 hr
  let F : ℕ → Vec d → HilbertVec d :=
    fun n => toHilbertVecField (ψ n).grad
  let f : Vec d → HilbertVec d :=
    toHilbertVecField u.grad
  have hFMem :
      ∀ n, MemLp (F n) p (volumeOn U) := by
    intro n
    exact
      gradMemLpOn_iff_memLp_toHilbertVecField.mp
        (ψ n).gradMemLp
  have hfMem :
      MemLp f p (volumeOn U) :=
    gradMemLpOn_iff_memLp_toHilbertVecField.mp
      u.gradMemLp
  have hDifference :
      Tendsto
        (fun n =>
          eLpNorm (F n - f) p (volumeOn U))
        atTop (𝓝 0) := by
    have hLifted :=
      tendsto_convexApproxSmoothW1p_grad_hilbert_eLpNorm_sub
        hU hp hpTop u hball hr
    refine hLifted.congr' ?_
    exact
      Eventually.of_forall fun n => by
        change
          eLpNorm
              (toHilbertVecField
                (fun x => (ψ n).grad x - u.grad x))
              p (volumeOn U) =
            eLpNorm
              (toHilbertVecField (ψ n).grad -
                toHilbertVecField u.grad)
              p (volumeOn U)
        rw [toHilbertVecField_sub]
  have hNorm :=
    tendsto_eLpNorm_of_tendsto_sub
      hp
      (fun n => (hFMem n).aestronglyMeasurable)
      hfMem.aestronglyMeasurable
      hfMem.eLpNorm_ne_top
      hDifference
  simpa only [F, f, ψ] using hNorm

/-- The exact Euclidean-gradient `L^p` norms of the smooth approximants
converge to that of the original Sobolev representative. -/
theorem
    tendsto_convexApproxSmoothW1p_grad_euclidean_eLpNorm
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p)
    {x0 : Vec d} {r : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) :
    Tendsto
      (fun n =>
        eLpNorm
          (fun x =>
            vecEuclideanNorm
              ((convexApproxSmoothW1p hU hp u x0 hr n).grad x))
          p (volumeOn U))
      atTop
      (𝓝
        (eLpNorm
          (fun x => vecEuclideanNorm (u.grad x))
          p (volumeOn U))) := by
  have hGradMeas : ∀ v : W1pFunction U p,
      AEStronglyMeasurable v.grad (volumeOn U) := fun v =>
    (aemeasurable_pi_iff.2 fun i =>
      (v.grad_memLp i).aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  simpa only [eLpNorm_toHilbertVecField_eq _ _ _ (hGradMeas _)] using
    tendsto_convexApproxSmoothW1p_grad_hilbert_eLpNorm
      hU hp hpTop u hball hr

/-- The normalized exact Euclidean magnitude of the gradient difference
converges to zero. -/
theorem
    tendsto_convexApproxSmoothW1p_grad_euclidean_eLpMeanNorm_sub
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p)
    {x0 : Vec d} {r : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r)
    (hUPos : 0 < volume U) :
    Tendsto
      (fun n =>
        eLpMeanNormOn U p
          (fun x =>
            vecEuclideanNorm
              ((convexApproxSmoothW1p hU hp u x0 hr n).grad x -
                u.grad x)))
      atTop (𝓝 0) := by
  let F : ℕ → Vec d → ℝ :=
    fun n x =>
      vecEuclideanNorm
        ((convexApproxSmoothW1p hU hp u x0 hr n).grad x -
          u.grad x)
  have hRaw :
      Tendsto
        (fun n => eLpNormOn U p (F n - 0))
        atTop (𝓝 0) := by
    simpa only [F, eLpNormOn, Pi.sub_apply,
      Pi.zero_apply, sub_zero] using
      tendsto_convexApproxSmoothW1p_grad_euclidean_eLpNorm_sub
        hU hp hpTop u hball hr
  have hNormalized :=
    tendsto_eLpMeanNormOn_sub_zero_of_tendsto_eLpNormOn_sub_zero
      hUPos hU.volume_lt_top hRaw
  simpa only [F, Pi.sub_apply, Pi.zero_apply, sub_zero] using
    hNormalized

/-- The normalized exact Euclidean-gradient `L^p` norms converge. The proof
uses the same explicit volume factor on both the approximating and limiting
unnormalized norms. -/
theorem
    tendsto_convexApproxSmoothW1p_grad_euclidean_eLpMeanNorm
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p)
    {x0 : Vec d} {r : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r)
    (hUPos : 0 < volume U) :
    Tendsto
      (fun n =>
        eLpMeanNormOn U p
          (fun x =>
            vecEuclideanNorm
              ((convexApproxSmoothW1p hU hp u x0 hr n).grad x)))
      atTop
      (𝓝
        (eLpMeanNormOn U p
          (fun x => vecEuclideanNorm (u.grad x)))) := by
  let C : ℝ≥0∞ :=
    (volume U)⁻¹ ^ (1 / p).toReal
  have hCTop : C ≠ ∞ := by
    dsimp only [C]
    exact
      (ENNReal.rpow_lt_top_of_nonneg
        (by positivity)
        (ENNReal.inv_ne_top.mpr hUPos.ne')).ne
  have hRaw :=
    tendsto_convexApproxSmoothW1p_grad_euclidean_eLpNorm
      hU hp hpTop u hball hr
  have hScaled :=
    ENNReal.Tendsto.const_mul
      (a := C) hRaw (Or.inr hCTop)
  simpa only [C,
    eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn
      hU.volume_lt_top,
    eLpNormOn] using hScaled

/-- Value convergence with respect to normalized volume. -/
theorem tendsto_convexApproxSmoothW1p_toFun_eLpMeanNorm_sub
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p)
    {x0 : Vec d} {r : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r)
    (hUPos : 0 < volume U) :
    Tendsto
      (fun n =>
        eLpMeanNormOn U p
          ((convexApproxSmoothW1p hU hp u x0 hr n).toFun -
            u.toFun))
      atTop (𝓝 0) := by
  have hRaw :
      Tendsto
        (fun n =>
          eLpNormOn U p
            ((convexApproxSmoothW1p hU hp u x0 hr n).toFun -
              u.toFun))
        atTop (𝓝 0) := by
    simpa only [eLpNormOn, Pi.sub_apply] using!
      tendsto_convexApproxSmoothW1p_toFun_eLpNorm_sub
        hU hp hpTop u hball hr
  exact
    tendsto_eLpMeanNormOn_sub_zero_of_tendsto_eLpNormOn_sub_zero
      hUPos hU.volume_lt_top hRaw

/-- Arithmetic means of the smooth convex approximants converge for every
finite `p ≥ 1`, including `p = 1`. -/
theorem tendsto_convexApproxSmoothW1p_integralAverage
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p)
    {x0 : Vec d} {r : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r)
    (hUPos : 0 < volume U) :
    Tendsto
      (fun n =>
        integralAverage U
          (convexApproxSmoothW1p hU hp u x0 hr n).toFun)
      atTop
      (𝓝 (integralAverage U u.toFun)) := by
  let ψ : ℕ → W1pFunction U p :=
    convexApproxSmoothW1p hU hp u x0 hr
  let μ : Measure (Vec d) :=
    normalizedVolumeOn U
  let : IsFiniteMeasure (volumeOn U) :=
    hU.isFiniteMeasure_volumeOn
  let : IsProbabilityMeasure μ :=
    isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top
      hUPos hU.volume_lt_top
  have hψMeas :
      ∀ n, AEStronglyMeasurable (ψ n).toFun μ := by
    intro n
    simpa only [μ, normalizedVolumeOn] using
      (ψ n).memLp.aestronglyMeasurable.smul_measure
        ((volume U)⁻¹)
  have huIntegrable :
      Integrable u.toFun μ := by
    simpa only [μ, normalizedVolumeOn] using
      (u.memLp.integrable hp).smul_measure
        (ENNReal.inv_ne_top.mpr hUPos.ne')
  have hNormalized :
      Tendsto
        (fun n =>
          eLpNorm ((ψ n).toFun - u.toFun) p μ)
        atTop (𝓝 0) := by
    simpa only [ψ, μ, eLpMeanNormOn] using
      tendsto_convexApproxSmoothW1p_toFun_eLpMeanNorm_sub
        hU hp hpTop u hball hr hUPos
  have hIntegral :=
    tendsto_integral_of_tendsto_eLpNorm_sub
      hp hψMeas huIntegrable hNormalized
  simpa only [ψ, μ,
    integral_normalizedVolumeOn_eq_integralAverage] using
    hIntegral

/-- Subtracting the arithmetic mean preserves normalized `L^p` convergence
of the smooth convex approximants, including at `p = 1`. -/
theorem
    tendsto_convexApproxSmoothW1p_centered_eLpMeanNorm_sub
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p)
    {x0 : Vec d} {r : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r)
    (hUPos : 0 < volume U) :
    Tendsto
      (fun n =>
        eLpMeanNormOn U p
          (fun x =>
            ((convexApproxSmoothW1p hU hp u x0 hr n).toFun x -
                integralAverage U
                  (convexApproxSmoothW1p hU hp u x0 hr n).toFun) -
              (u.toFun x - integralAverage U u.toFun)))
      atTop (𝓝 0) := by
  let ψ : ℕ → W1pFunction U p :=
    convexApproxSmoothW1p hU hp u x0 hr
  let μ : Measure (Vec d) :=
    normalizedVolumeOn U
  let : IsFiniteMeasure (volumeOn U) :=
    hU.isFiniteMeasure_volumeOn
  let : IsProbabilityMeasure μ :=
    isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top
      hUPos hU.volume_lt_top
  have hψMeas :
      ∀ n, AEStronglyMeasurable (ψ n).toFun μ := by
    intro n
    simpa only [μ, normalizedVolumeOn] using
      (ψ n).memLp.aestronglyMeasurable.smul_measure
        ((volume U)⁻¹)
  have huIntegrable :
      Integrable u.toFun μ := by
    simpa only [μ, normalizedVolumeOn] using
      (u.memLp.integrable hp).smul_measure
        (ENNReal.inv_ne_top.mpr hUPos.ne')
  have hNormalized :
      Tendsto
        (fun n =>
          eLpNorm ((ψ n).toFun - u.toFun) p μ)
        atTop (𝓝 0) := by
    simpa only [ψ, μ, eLpMeanNormOn] using
      tendsto_convexApproxSmoothW1p_toFun_eLpMeanNorm_sub
        hU hp hpTop u hball hr hUPos
  have hCentered :=
    tendsto_eLpNorm_centered_sub_zero
      hp hpTop hψMeas huIntegrable hNormalized
  simpa only [ψ, μ, eLpMeanNormOn,
    integral_normalizedVolumeOn_eq_integralAverage] using
    hCentered

/-- The normalized `L^p` norms of the centered smooth values converge to the
normalized norm of the centered Sobolev value. -/
theorem tendsto_convexApproxSmoothW1p_centered_eLpMeanNorm
    (hU : IsOpenBoundedConvexDomain U)
    (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    (u : W1pFunction U p)
    {x0 : Vec d} {r : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r)
    (hUPos : 0 < volume U) :
    Tendsto
      (fun n =>
        eLpMeanNormOn U p
          (fun x =>
            (convexApproxSmoothW1p hU hp u x0 hr n).toFun x -
              integralAverage U
                (convexApproxSmoothW1p hU hp u x0 hr n).toFun))
      atTop
      (𝓝
        (eLpMeanNormOn U p
          (fun x =>
            u.toFun x - integralAverage U u.toFun))) := by
  let ψ : ℕ → W1pFunction U p :=
    convexApproxSmoothW1p hU hp u x0 hr
  let μ : Measure (Vec d) :=
    normalizedVolumeOn U
  let centered : ℕ → Vec d → ℝ :=
    fun n x =>
      (ψ n).toFun x -
        integralAverage U (ψ n).toFun
  let centeredLimit : Vec d → ℝ :=
    fun x =>
      u.toFun x - integralAverage U u.toFun
  let : IsProbabilityMeasure μ :=
    isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top
      hUPos hU.volume_lt_top
  have hψMeas :
      ∀ n, AEStronglyMeasurable (ψ n).toFun μ := by
    intro n
    simpa only [μ, normalizedVolumeOn] using
      (ψ n).memLp.aestronglyMeasurable.smul_measure
        ((volume U)⁻¹)
  have hCenteredMeas :
      ∀ n, AEStronglyMeasurable (centered n) μ := by
    intro n
    exact
      (hψMeas n).sub aestronglyMeasurable_const
  have huMemNormalized :
      MemLp u.toFun p μ := by
    simpa only [μ, normalizedVolumeOn] using
      u.memLp.smul_measure
        (ENNReal.inv_ne_top.mpr hUPos.ne')
  have hCenteredLimitMem :
      MemLp centeredLimit p μ := by
    exact
      huMemNormalized.sub
        (memLp_const
          (μ := μ) (p := p)
          (c := integralAverage U u.toFun))
  have hCenteredDifference :
      Tendsto
        (fun n =>
          eLpNorm (centered n - centeredLimit) p μ)
        atTop (𝓝 0) := by
    simpa only [ψ, μ, centered, centeredLimit,
      eLpMeanNormOn, Pi.sub_apply] using!
      tendsto_convexApproxSmoothW1p_centered_eLpMeanNorm_sub
        hU hp hpTop u hball hr hUPos
  have hNorm :=
    tendsto_eLpNorm_of_tendsto_sub
      hp hCenteredMeas
      hCenteredLimitMem.aestronglyMeasurable
      hCenteredLimitMem.eLpNorm_ne_top
      hCenteredDifference
  simpa only [ψ, μ, centered, centeredLimit,
    eLpMeanNormOn] using hNorm

end W1pFunction

end PDE

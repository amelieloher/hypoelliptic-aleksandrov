module

public import PDEFoundation.Sobolev.W1p.ConvexApprox.WeakDerivSmoothing

/-!
# Continuity of convex-domain smoothing

This file closes the weak-derivative smoothing chain by identifying the
classical coordinate derivatives of the smooth representative almost
everywhere. It also records the elementary continuity, support, and
integrability facts used by pointwise bounds and `L^p` convergence.

The separate classical-input differentiation-under-the-integral theory is not
part of this foundational module.
-/

@[expose] public section

open scoped Pointwise Convolution

namespace PDE

/-- The classical coordinate derivative of the smooth representative agrees
almost everywhere with the correspondingly smoothed weak derivative, including
the exact affine factor `1 - ε`. -/
theorem ae_eq_fderiv_convexApproxSmoothRepresentative_apply_basisVec
    {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    {i : Fin d} {u gi ρ : Vec d → ℝ} {p : ENNReal}
    (hρ : IsConvexApproxKernel ρ) (hp : 1 ≤ p)
    (huMem : MemLpOn U p u) (hgiMem : MemLpOn U p gi)
    (huWeak : HasWeakPartialDerivOn U i u gi)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) (hε : 0 < ε) (hεOne : ε < 1) :
    (fun x =>
        (fderiv ℝ
          (convexApproxSmoothRepresentative U ρ u x0 r ε) x)
          (basisVec i)) =ᵐ[MeasureTheory.volume.restrict U]
      fun x =>
        (1 - ε) *
          convexApproxSmoothRepresentative U ρ gi x0 r ε x := by
  have huLoc :
      MeasureTheory.LocallyIntegrableOn
        u U MeasureTheory.volume :=
    MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
      (huMem.locallyIntegrable hp)
  have hgiLoc :
      MeasureTheory.LocallyIntegrableOn
        gi U MeasureTheory.volume :=
    MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
      (hgiMem.locallyIntegrable hp)
  have huSmooth :
      ContDiff ℝ (⊤ : ℕ∞)
        (convexApproxSmoothRepresentative U ρ u x0 r ε) :=
    contDiff_convexApproxSmoothRepresentative
      hU.measurableSet hρ hp huMem hr hε
  have hgiSmooth :
      ContDiff ℝ (⊤ : ℕ∞)
        (convexApproxSmoothRepresentative U ρ gi x0 r ε) :=
    contDiff_convexApproxSmoothRepresentative
      hU.measurableSet hρ hp hgiMem hr hε
  have hClassicalWeak :
      HasWeakPartialDerivOn U i
        (convexApproxSmoothRepresentative U ρ u x0 r ε)
        (fun x =>
          (fderiv ℝ
            (convexApproxSmoothRepresentative U ρ u x0 r ε) x)
            (basisVec i)) :=
    HasWeakPartialDerivOn.of_contDiff
      (U := U) (i := i)
      (f := convexApproxSmoothRepresentative U ρ u x0 r ε)
      (huSmooth.of_le (by simp))
  have hSmoothedWeak :
      HasWeakPartialDerivOn U i
        (convexApproxSmoothRepresentative U ρ u x0 r ε)
        (fun x =>
          (1 - ε) *
            convexApproxSmoothRepresentative U ρ gi x0 r ε x) :=
    HasWeakPartialDerivOn.convexApproxSmoothRepresentative
      (i := i) hU huLoc hgiLoc huWeak hρ
      hball hr hε hεOne
  have hClassicalContinuous :
      Continuous
        (fun x =>
          (fderiv ℝ
            (convexApproxSmoothRepresentative U ρ u x0 r ε) x)
            (basisVec i)) := by
    simpa only using
      (huSmooth.continuous_fderiv (by simp)).clm_apply
        continuous_const
  have hSmoothedContinuous :
      Continuous
        (fun x =>
          (1 - ε) *
            convexApproxSmoothRepresentative U ρ gi x0 r ε x) := by
    simpa only using!
      continuous_const.mul hgiSmooth.continuous
  have hClassicalLoc :
      MeasureTheory.LocallyIntegrableOn
        (fun x =>
          (fderiv ℝ
            (convexApproxSmoothRepresentative U ρ u x0 r ε) x)
            (basisVec i))
        U MeasureTheory.volume :=
    hClassicalContinuous.continuousOn.locallyIntegrableOn
      hU.measurableSet
  have hSmoothedLoc :
      MeasureTheory.LocallyIntegrableOn
        (fun x =>
          (1 - ε) *
            convexApproxSmoothRepresentative U ρ gi x0 r ε x)
        U MeasureTheory.volume :=
    hSmoothedContinuous.continuousOn.locallyIntegrableOn
      hU.measurableSet
  exact
    HasWeakPartialDerivOn.ae_eq
      hU.isOpen hClassicalLoc hSmoothedLoc
      hClassicalWeak hSmoothedWeak

theorem continuous_convexApproxSample_right
    {d : ℕ} (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    Continuous
      (fun z : Vec d =>
        convexApproxSample x0 z r ε x) := by
  unfold convexApproxSample
  fun_prop

theorem continuous_convexApproxSample_prod
    {d : ℕ} (x0 : Vec d) (r ε : ℝ) :
    Continuous
      (fun xz : Vec d × Vec d =>
        convexApproxSample x0 xz.2 r ε xz.1) := by
  unfold convexApproxSample
  fun_prop

theorem continuous_convexApproxIntegrand_right
    {d : ℕ} {ρ u : Vec d → ℝ}
    (hρ : Continuous ρ) (hu : Continuous u)
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    Continuous
      (fun z =>
        convexApproxIntegrand ρ u x0 r ε x z) := by
  simpa only [convexApproxIntegrand] using!
    hρ.mul
      (hu.comp
        (continuous_convexApproxSample_right x0 r ε x))

theorem continuous_convexApproxIntegrand_left
    {d : ℕ} {ρ u : Vec d → ℝ}
    (hu : Continuous u) (x0 z : Vec d)
    (r ε : ℝ) :
    Continuous
      (fun x =>
        convexApproxIntegrand ρ u x0 r ε x z) := by
  simpa only [convexApproxIntegrand] using!
    continuous_const.mul
      (hu.comp (continuous_convexApproxSample x0 z r ε))

theorem continuous_convexApproxIntegrand_prod
    {d : ℕ} {ρ u : Vec d → ℝ}
    (hρ : Continuous ρ) (hu : Continuous u)
    (x0 : Vec d) (r ε : ℝ) :
    Continuous
      (fun xz : Vec d × Vec d =>
        convexApproxIntegrand
          ρ u x0 r ε xz.1 xz.2) := by
  have hρProd :
      Continuous
        (fun xz : Vec d × Vec d => ρ xz.2) :=
    hρ.comp continuous_snd
  have huProd :
      Continuous
        (fun xz : Vec d × Vec d =>
          u (convexApproxSample
            x0 xz.2 r ε xz.1)) :=
    hu.comp
      (continuous_convexApproxSample_prod x0 r ε)
  simpa only [convexApproxIntegrand] using!
    hρProd.mul huProd

theorem tsupport_convexApproxIntegrand_subset
    {d : ℕ} {ρ u : Vec d → ℝ}
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    tsupport
        (fun z =>
          convexApproxIntegrand ρ u x0 r ε x z) ⊆
      tsupport ρ := by
  simpa only [convexApproxIntegrand] using
    (tsupport_mul_subset_left
      (f := ρ)
      (g := fun z =>
        u (convexApproxSample x0 z r ε x)))

theorem hasCompactSupport_convexApproxIntegrand
    {d : ℕ} {ρ u : Vec d → ℝ}
    (hρ : HasCompactSupport ρ)
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    HasCompactSupport
      (fun z =>
        convexApproxIntegrand ρ u x0 r ε x z) := by
  simpa only [convexApproxIntegrand] using!
    (hρ.mul_right :
      HasCompactSupport
        (fun z =>
          ρ z *
            u (convexApproxSample x0 z r ε x)))

theorem integrable_convexApproxIntegrand
    {d : ℕ} {ρ u : Vec d → ℝ}
    (hρ : Continuous ρ)
    (hρCompact : HasCompactSupport ρ)
    (hu : Continuous u)
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    MeasureTheory.Integrable
      (fun z =>
        convexApproxIntegrand ρ u x0 r ε x z) :=
  (continuous_convexApproxIntegrand_right
      hρ hu x0 r ε x).integrable_of_hasCompactSupport
    (hasCompactSupport_convexApproxIntegrand
      hρCompact x0 r ε x)

theorem continuous_convexApproxDifferenceIntegrand
    {d : ℕ} {ρ u : Vec d → ℝ}
    (hρ : Continuous ρ) (hu : Continuous u)
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    Continuous
      (fun z =>
        ρ z *
          (u (convexApproxSample x0 z r ε x) - u x)) :=
  hρ.mul
    ((hu.comp
      (continuous_convexApproxSample_right
        x0 r ε x)).sub continuous_const)

theorem hasCompactSupport_convexApproxDifferenceIntegrand
    {d : ℕ} {ρ u : Vec d → ℝ}
    (hρCompact : HasCompactSupport ρ)
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    HasCompactSupport
      (fun z =>
        ρ z *
          (u (convexApproxSample x0 z r ε x) - u x)) := by
  simpa only using!
    (hρCompact.mul_right :
      HasCompactSupport
        (fun z =>
          ρ z *
            (u (convexApproxSample x0 z r ε x) - u x)))

theorem integrable_convexApproxDifferenceIntegrand
    {d : ℕ} {ρ u : Vec d → ℝ}
    (hρ : Continuous ρ)
    (hρCompact : HasCompactSupport ρ)
    (hu : Continuous u)
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    MeasureTheory.Integrable
      (fun z =>
        ρ z *
          (u (convexApproxSample x0 z r ε x) - u x)) :=
  (continuous_convexApproxDifferenceIntegrand
      hρ hu x0 r ε x).integrable_of_hasCompactSupport
    (hasCompactSupport_convexApproxDifferenceIntegrand
      hρCompact x0 r ε x)

theorem continuous_convexApproxWeightedOscillation
    {d : ℕ} {ρ u : Vec d → ℝ}
    (hρ : Continuous ρ) (hu : Continuous u)
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    Continuous
      (fun z =>
        ρ z *
          |u (convexApproxSample x0 z r ε x) - u x|) :=
  hρ.mul
    (((hu.comp
      (continuous_convexApproxSample_right
        x0 r ε x)).sub continuous_const).abs)

theorem hasCompactSupport_convexApproxWeightedOscillation
    {d : ℕ} {ρ u : Vec d → ℝ}
    (hρCompact : HasCompactSupport ρ)
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    HasCompactSupport
      (fun z =>
        ρ z *
          |u (convexApproxSample x0 z r ε x) - u x|) := by
  simpa only using!
    (hρCompact.mul_right :
      HasCompactSupport
        (fun z =>
          ρ z *
            |u (convexApproxSample x0 z r ε x) - u x|))

theorem integrable_convexApproxWeightedOscillation
    {d : ℕ} {ρ u : Vec d → ℝ}
    (hρ : Continuous ρ)
    (hρCompact : HasCompactSupport ρ)
    (hu : Continuous u)
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    MeasureTheory.Integrable
      (fun z =>
        ρ z *
          |u (convexApproxSample x0 z r ε x) - u x|) :=
  (continuous_convexApproxWeightedOscillation
      hρ hu x0 r ε x).integrable_of_hasCompactSupport
    (hasCompactSupport_convexApproxWeightedOscillation
      hρCompact x0 r ε x)

theorem integrable_convexApproxKernelMulConst
    {d : ℕ} {ρ : Vec d → ℝ}
    (hρ : Continuous ρ)
    (hρCompact : HasCompactSupport ρ)
    (c : ℝ) :
    MeasureTheory.Integrable
      (fun z => ρ z * c) := by
  have hContinuous :
      Continuous (fun z => ρ z * c) :=
    hρ.mul continuous_const
  have hCompact :
      HasCompactSupport (fun z => ρ z * c) := by
    simpa only using!
      (hρCompact.mul_right :
        HasCompactSupport (fun z => ρ z * c))
  exact
    hContinuous.integrable_of_hasCompactSupport hCompact

theorem continuous_convexApproxSmoothing
    {d : ℕ} {ρ u : Vec d → ℝ}
    (hρ : Continuous ρ)
    (hρCompact : HasCompactSupport ρ)
    (hu : Continuous u)
    (x0 : Vec d) (r ε : ℝ) :
    Continuous
      (convexApproxSmoothing ρ u x0 r ε) := by
  have hIntegrand :
      Continuous
        (Function.uncurry
          (fun x z =>
            convexApproxIntegrand ρ u x0 r ε x z)) := by
    simpa only [Function.uncurry] using!
      continuous_convexApproxIntegrand_prod
        hρ hu x0 r ε
  simpa only [convexApproxSmoothing] using!
    (continuous_parametric_integral_of_continuous
      (μ := MeasureTheory.volume)
      (f := fun x z =>
        convexApproxIntegrand ρ u x0 r ε x z)
      hIntegrand hρCompact.isCompact)

end PDE

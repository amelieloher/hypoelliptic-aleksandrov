module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeVStarPrimitive
public import HypoellipticAleksandrov.Parabolic.Dirichlet.WeakTimeDerivative
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeDerivativeKernel
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialSobolevSeparable

/-!
# Canonical affine representative for the reverse-time Gelfand curve

This module identifies the reverse-time Gelfand curve with its dual Bochner
primitive plus its canonical Bochner-average affine constant.  The result is
only an almost-everywhere identity in the spatial Gelfand dual; it supplies no
trace, energy identity, or Hilbert-valued representative.
-/

@[expose] public section

open Filter Function MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The canonical Bochner-average constant in the reverse-time affine Gelfand
identification.  The positive-time proof argument guards this normalization. -/
noncomputable def reverseTimeGelfandAffineConstant
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (_hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) :
    H10HilbertGraphDual hΩ :=
  T⁻¹ • ∫ tau,
    (reverseTimeGelfandCLM hΩ T u tau -
      reverseTimeVStarPrimitive hΩ T g tau) ∂reverseTimeVolume T

private theorem integrable_reverseTimeGelfandAffineDifference
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) :
    Integrable
      (fun tau => reverseTimeGelfandCLM hΩ T u tau -
        reverseTimeVStarPrimitive hΩ T g tau)
      (reverseTimeVolume T) := by
  letI : IsFiniteMeasure (reverseTimeVolume T) := by
    change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) T))
    infer_instance
  have hGLp : MemLp (fun tau => reverseTimeGelfandCLM hΩ T u tau)
      (2 : ℝ≥0∞) (reverseTimeVolume T) :=
    MeasureTheory.Lp.memLp (reverseTimeGelfandCLM hΩ T u)
  have hG : Integrable (fun tau => reverseTimeGelfandCLM hΩ T u tau)
      (reverseTimeVolume T) :=
    hGLp.integrable (by norm_num)
  have hP : Integrable (reverseTimeVStarPrimitive hΩ T g) (reverseTimeVolume T) := by
    change IntegrableOn (reverseTimeVStarPrimitive hΩ T g) (Ioo (0 : ℝ) T) volume
    exact (continuousOn_reverseTimeVStarPrimitive hΩ T g).integrableOn_Icc
      |>.mono_set Ioo_subset_Icc_self
  exact hG.sub hP

private theorem reverseTimeVolume_real_univ (T : ℝ) (hT : 0 < T) :
    (reverseTimeVolume T).real univ = T := by
  change (volume.restrict (Ioo (0 : ℝ) T)).real univ = T
  rw [MeasureTheory.measureReal_restrict_apply_univ,
    Real.volume_real_Ioo_of_le (le_of_lt hT)]
  norm_num

private theorem integral_reverseTimeGelfandAffineDifference_apply_deriv_eq_zero
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
    (v : H10HilbertGraph hΩ) (eta : ReverseTimeScalarTest T) :
    (∫ tau,
      (reverseTimeGelfandCLM hΩ T u tau -
        reverseTimeVStarPrimitive hΩ T g tau) v * eta.deriv tau
      ∂reverseTimeVolume T) = 0 := by
  let G : ℝ → H10HilbertGraphDual hΩ := fun tau => reverseTimeGelfandCLM hΩ T u tau
  let P : ℝ → H10HilbertGraphDual hΩ := fun tau => reverseTimeVStarPrimitive hΩ T g tau
  change (∫ tau, (G tau - P tau) v * eta.deriv tau ∂reverseTimeVolume T) = 0
  obtain ⟨hGInner, _, hGIdentity⟩ := hderiv v eta
  obtain ⟨hP, _, hPIdentity⟩ :=
    reverseTimeVStarPrimitive_test_deriv hΩ T g v eta
  have hGae :
      (fun tau => G tau v * eta.deriv tau) =ᵐ[
        reverseTimeVolume T]
        fun tau => inner ℝ (valueCLM hΩ v) (reverseTimeValueCLM hΩ T u tau) * eta.deriv tau := by
    filter_upwards [coeFn_reverseTimeGelfandCLM hΩ T u,
      coeFn_reverseTimeValueCLM hΩ T u] with tau hGelfand hValue
    dsimp only [G]
    rw [hGelfand, scalarLpToH10HilbertGraphDual_apply, hValue]
  have hG : Integrable
      (fun tau => G tau v * eta.deriv tau)
      (reverseTimeVolume T) :=
    hGInner.congr hGae.symm
  have hIdentity :
      (∫ tau, G tau v * eta.deriv tau
        ∂reverseTimeVolume T) =
        ∫ tau, P tau v * eta.deriv tau
          ∂reverseTimeVolume T := by
    calc
      (∫ tau, G tau v * eta.deriv tau
        ∂reverseTimeVolume T) =
          ∫ tau, inner ℝ (valueCLM hΩ v) (reverseTimeValueCLM hΩ T u tau) * eta.deriv tau
            ∂reverseTimeVolume T := integral_congr_ae hGae
      _ = -(∫ tau, (g tau) v * eta tau ∂reverseTimeVolume T) := hGIdentity
      _ = ∫ tau, P tau v * eta.deriv tau
          ∂reverseTimeVolume T := hPIdentity.symm
  calc
    (∫ tau,
      (G tau - P tau) v * eta.deriv tau
      ∂reverseTimeVolume T) =
        ∫ tau, (G tau v * eta.deriv tau - P tau v * eta.deriv tau)
          ∂reverseTimeVolume T := by
            apply integral_congr_ae
            filter_upwards with tau
            rw [ContinuousLinearMap.sub_apply, sub_mul]
    _ = (∫ tau, G tau v * eta.deriv tau
        ∂reverseTimeVolume T) -
        ∫ tau, P tau v * eta.deriv tau
          ∂reverseTimeVolume T := integral_sub hG hP
    _ = 0 := by rw [hIdentity, sub_self]

private theorem reverseTimeGelfandAffineDifference_apply_ae_eq_affineConstant_apply
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
    (hF : Integrable
      (fun tau => reverseTimeGelfandCLM hΩ T u tau -
        reverseTimeVStarPrimitive hΩ T g tau)
      (reverseTimeVolume T))
    (v : H10HilbertGraph hΩ) :
    (fun tau =>
      (reverseTimeGelfandCLM hΩ T u tau -
        reverseTimeVStarPrimitive hΩ T g tau) v) =ᵐ[reverseTimeVolume T]
      fun _ => reverseTimeGelfandAffineConstant hΩ T hT u g v := by
  let F : ℝ → H10HilbertGraphDual hΩ := fun tau =>
    reverseTimeGelfandCLM hΩ T u tau - reverseTimeVStarPrimitive hΩ T g tau
  change Integrable F (reverseTimeVolume T) at hF
  change (fun tau => F tau v) =ᵐ[reverseTimeVolume T]
    fun _ => reverseTimeGelfandAffineConstant hΩ T hT u g v
  have hScalar : Integrable (fun tau => F tau v) (reverseTimeVolume T) :=
    (ContinuousLinearMap.apply ℝ ℝ v).integrable_comp hF
  obtain ⟨a, ha⟩ := exists_ae_eq_const_of_integral_deriv_eq_zero T hT hScalar (by
    intro eta
    exact integral_reverseTimeGelfandAffineDifference_apply_deriv_eq_zero
      hΩ T hT u g hderiv v eta)
  have hIntegral : (∫ tau, F tau v ∂reverseTimeVolume T) = T • a := by
    calc
      (∫ tau, F tau v ∂reverseTimeVolume T) = ∫ _ : ℝ, a ∂reverseTimeVolume T :=
        integral_congr_ae ha
      _ = (reverseTimeVolume T).real univ • a := MeasureTheory.integral_const a
      _ = T • a := by rw [reverseTimeVolume_real_univ T hT]
  have hConstant : reverseTimeGelfandAffineConstant hΩ T hT u g v = a := by
    rw [reverseTimeGelfandAffineConstant, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.integral_apply hF v]
    change T⁻¹ * (∫ tau, F tau v ∂reverseTimeVolume T) = a
    rw [hIntegral, smul_eq_mul]
    calc
      T⁻¹ * (T * a) = (T⁻¹ * T) * a := (mul_assoc _ _ _).symm
      _ = a := by rw [inv_mul_cancel₀ hT.ne', one_mul]
  filter_upwards [ha] with tau htau
  rw [htau, hConstant]

private theorem ae_all_h10HilbertGraphDual_apply_eq
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    {hΩ : IsOpen Ω} {T : ℝ}
    (F : ℝ → H10HilbertGraphDual hΩ) (c : H10HilbertGraphDual hΩ)
    (q : ℕ → H10HilbertGraph hΩ)
    (hpair : ∀ n : ℕ, (fun tau => F tau (q n)) =ᵐ[reverseTimeVolume T]
      fun _ => c (q n)) :
    ∀ᵐ tau ∂reverseTimeVolume T, ∀ n : ℕ, F tau (q n) = c (q n) :=
  ae_all_iff.mpr hpair

private theorem h10HilbertGraphDual_eq_of_dense_apply_eq
    {d : ℕ} {Ω : Set (PDE.Vec d)} {hΩ : IsOpen Ω}
    (q : ℕ → H10HilbertGraph hΩ) (hqDense : DenseRange q)
    (ell ell' : H10HilbertGraphDual hΩ)
    (hpair : ∀ n : ℕ, ell (q n) = ell' (q n)) :
    ell = ell' := by
  apply ContinuousLinearMap.coeFn_injective
  exact Continuous.ext_on hqDense ell.continuous ell'.continuous (by
    rintro _ ⟨n, rfl⟩
    exact hpair n)

private theorem reverseTimeGelfandAffineDifference_ae_eq_affineConstant
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
    (hF : Integrable
      (fun tau => reverseTimeGelfandCLM hΩ T u tau -
        reverseTimeVStarPrimitive hΩ T g tau)
      (reverseTimeVolume T)) :
    (fun tau => reverseTimeGelfandCLM hΩ T u tau -
      reverseTimeVStarPrimitive hΩ T g tau) =ᵐ[reverseTimeVolume T]
      fun _ => reverseTimeGelfandAffineConstant hΩ T hT u g := by
  let F : ℝ → H10HilbertGraphDual hΩ := fun tau =>
    reverseTimeGelfandCLM hΩ T u tau - reverseTimeVStarPrimitive hΩ T g tau
  let c : H10HilbertGraphDual hΩ := reverseTimeGelfandAffineConstant hΩ T hT u g
  change Integrable F (reverseTimeVolume T) at hF
  change F =ᵐ[reverseTimeVolume T] fun _ => c
  letI : TopologicalSpace.SeparableSpace (H10HilbertGraph hΩ) :=
    h10HilbertGraphSeparableSpace hΩ
  let q : ℕ → H10HilbertGraph hΩ := TopologicalSpace.denseSeq (H10HilbertGraph hΩ)
  have hqDense : DenseRange q :=
    TopologicalSpace.denseRange_denseSeq (H10HilbertGraph hΩ)
  have hpairAE : ∀ n : ℕ, (fun tau => F tau (q n)) =ᵐ[reverseTimeVolume T]
      fun _ => c (q n) := by
    intro n
    simpa only [F, c] using
      reverseTimeGelfandAffineDifference_apply_ae_eq_affineConstant_apply
        hΩ T hT u g hderiv hF (q n)
  have hpairAll : ∀ᵐ tau ∂reverseTimeVolume T, ∀ n : ℕ, F tau (q n) = c (q n) :=
    ae_all_h10HilbertGraphDual_apply_eq F c q hpairAE
  filter_upwards [hpairAll] with tau htau
  exact h10HilbertGraphDual_eq_of_dense_apply_eq q hqDense (F tau) c (htau)

private theorem ae_eq_add_of_ae_sub_eq
    {alpha E : Type _} [MeasurableSpace alpha] [AddCommGroup E]
    {mu : Measure alpha} {G P : alpha → E} {c : E}
    (h : (fun x => G x - P x) =ᵐ[mu] fun _ => c) :
    G =ᵐ[mu] fun x => P x + c := by
  filter_upwards [h] with x hx
  simpa only [add_comm] using sub_eq_iff_eq_add.mp hx

/-- The reverse-time Gelfand curve agrees almost everywhere with its dual
Bochner primitive plus the canonical affine Bochner-average constant. -/
theorem reverseTimeGelfandCLM_ae_eq_reverseTimeVStarPrimitive_add_affineConstant
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g) :
    reverseTimeGelfandCLM hΩ T u =ᵐ[reverseTimeVolume T] fun tau =>
      reverseTimeVStarPrimitive hΩ T g tau +
        reverseTimeGelfandAffineConstant hΩ T hT u g := by
  have hF : Integrable
      (fun tau => reverseTimeGelfandCLM hΩ T u tau -
        reverseTimeVStarPrimitive hΩ T g tau)
      (reverseTimeVolume T) :=
    integrable_reverseTimeGelfandAffineDifference hΩ T u g
  exact ae_eq_add_of_ae_sub_eq
    (reverseTimeGelfandAffineDifference_ae_eq_affineConstant hΩ T hT u g hderiv hF)

end HypoellipticAleksandrov.Parabolic.Dirichlet

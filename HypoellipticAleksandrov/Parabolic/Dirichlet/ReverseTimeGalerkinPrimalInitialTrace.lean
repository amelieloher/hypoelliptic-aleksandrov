module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinPrimalResidualDerivative
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeHilbertBoundaryPairing
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinPrimalBoundaryTime
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGalerkinPrimalBochner
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeGelfandPairing
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSeparatedMultiplier

/-!
# Canonical initial trace of the reverse-time Galerkin limit

This module transfers the finite projected initial datum through the common
Galerkin subsequence to the canonical Gelfand initial trace.  The affine time
multiplier is deliberately handled here as a bounded Bochner multiplier: it
does not vanish at the initial endpoint and is therefore not a scalar test.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal Matrix Matrix.Norms.Elementwise MatrixOrder RealInnerProductSpace

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

private def affineReverseTimeMultiplier (T : ℝ) : ℝ → ℝ := fun tau => 1 - tau / T

private def affineReverseTimeDerivative (T : ℝ) : ℝ → ℝ := fun _tau => -(T⁻¹)

private theorem memLp_affine_reverseTime_multiplier {T : ℝ} (hT : 0 < T) :
    MemLp (affineReverseTimeMultiplier T) (∞ : ℝ≥0∞) (reverseTimeVolume T) := by
  letI : IsFiniteMeasure (reverseTimeVolume T) := by
    change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) T))
    infer_instance
  apply memLp_of_bounded (a := 0) (b := 1) ?_ ?_ _
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with tau ht
    change 1 - tau / T ∈ Icc 0 1
    have hquotient_nonneg : 0 ≤ tau / T := le_of_lt (div_pos ht.1 hT)
    have hquotient_le_one : tau / T ≤ 1 := (div_le_one₀ hT).2 ht.2.le
    constructor <;> linarith
  · exact (continuous_const.sub (continuous_id.div_const T)).aestronglyMeasurable

private theorem memLp_affine_reverseTime_deriv {T : ℝ} (_hT : 0 < T) :
    MemLp (affineReverseTimeDerivative T) (∞ : ℝ≥0∞) (reverseTimeVolume T) := by
  letI : IsFiniteMeasure (reverseTimeVolume T) := by
    change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) T))
    infer_instance
  exact memLp_const _

private noncomputable def affineReverseTimeVTest
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (hT : 0 < T) (v : H10HilbertGraph hΩ) : ReverseTimeL2V hΩ T :=
  reverseTimeSeparatedVTestOfMemLp hΩ (affineReverseTimeMultiplier T)
    (memLp_affine_reverseTime_multiplier hT) v

private noncomputable def affineReverseTimeDerivativeVTest
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (hT : 0 < T) (v : H10HilbertGraph hΩ) : ReverseTimeL2V hΩ T :=
  reverseTimeSeparatedVTestOfMemLp hΩ (affineReverseTimeDerivative T)
    (memLp_affine_reverseTime_deriv hT) v

private theorem reverseTimeDualPairingRightCLM_ofMemLp_eq_integral
    {d : ℕ} {Ω : Set (PDE.Vec d)} {T : ℝ}
    (hΩ : IsOpen Ω) (g : ReverseTimeL2VStar hΩ T)
    (q : ℝ → ℝ) (hq : MemLp q (∞ : ℝ≥0∞) (reverseTimeVolume T))
    (v : H10HilbertGraph hΩ) :
    reverseTimeDualPairingRightCLM hΩ T
        (reverseTimeSeparatedVTestOfMemLp hΩ q hq v) g =
      ∫ tau, (g tau) v * q tau ∂reverseTimeVolume T := by
  calc
    reverseTimeDualPairingRightCLM hΩ T
        (reverseTimeSeparatedVTestOfMemLp hΩ q hq v) g =
        reverseTimeDualPairingCLM hΩ T g
          (reverseTimeSeparatedVTestOfMemLp hΩ q hq v) :=
      reverseTimeDualPairingRightCLM_apply hΩ T _ g
    _ = ∫ tau, g tau (reverseTimeSeparatedVTestOfMemLp hΩ q hq v tau)
        ∂reverseTimeVolume T := reverseTimeDualPairingCLM_apply hΩ T g _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_reverseTimeSeparatedVTestOfMemLp hΩ q hq v] with tau hz
      rw [hz, ContinuousLinearMap.map_smul]
      exact mul_comm _ _

private theorem reverseTimeNegativeSource_pairing_ofMemLp_eq_integral_raw
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (q : ℝ → ℝ) (hq : MemLp q (∞ : ℝ≥0∞) (reverseTimeVolume (r₁ - r₀)))
    (v : H10HilbertGraph hΩ) :
    reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
        (reverseTimeSeparatedVTestOfMemLp hΩ q hq v)
        (reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth) =
      ∫ tau, reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v * q tau
        ∂reverseTimeVolume (r₁ - r₀) := by
  let S := reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth
  calc
    reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
        (reverseTimeSeparatedVTestOfMemLp hΩ q hq v) S =
        ∫ tau, S tau v * q tau ∂reverseTimeVolume (r₁ - r₀) :=
      reverseTimeDualPairingRightCLM_ofMemLp_eq_integral hΩ S q hq v
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [
        (memLp_reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth).coeFn_toLp]
        with tau hS
      simpa only [S, reverseTimeNegativeSource] using
        congrArg (fun s => s v * q tau) hS

private theorem reverseTimeSpatialForm_pairing_ofMemLp_eq_integral
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (q : ℝ → ℝ) (hq : MemLp q (∞ : ℝ≥0∞) (reverseTimeVolume (r₁ - r₀)))
    (v : H10HilbertGraph hΩ) :
    reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
        (reverseTimeSeparatedVTestOfMemLp hΩ q hq v)
        (reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth u) =
      ∫ tau, reverseTimeSpatialForm hΩ r₁ tau a b c (u tau) v * q tau
        ∂reverseTimeVolume (r₁ - r₀) := by
  let A := reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth u
  calc
    reverseTimeDualPairingRightCLM hΩ (r₁ - r₀)
        (reverseTimeSeparatedVTestOfMemLp hΩ q hq v) A =
        ∫ tau, A tau v * q tau ∂reverseTimeVolume (r₁ - r₀) :=
      reverseTimeDualPairingRightCLM_ofMemLp_eq_integral hΩ A q hq v
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_reverseTimeSpatialFormBochnerAction_apply r₀ r₁ h₀₁ hΩ hΩbounded
        a b c haSmooth hbSmooth hcSmooth u] with tau hA
      exact congrArg (fun s : ℝ => s * q tau) (hA v)

private theorem integrable_source_raw_mul_multiplier
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (F : ℝ → PDE.Vec d → ℝ)
    (hFSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (q : ℝ → ℝ) (hq : MemLp q (∞ : ℝ≥0∞) (reverseTimeVolume (r₁ - r₀)))
    (v : H10HilbertGraph hΩ) :
    Integrable (fun tau =>
      reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau v * q tau)
      (reverseTimeVolume (r₁ - r₀)) := by
  let S := reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth
  let z := reverseTimeSeparatedVTestOfMemLp hΩ q hq v
  refine (integrable_reverseTimeDualPairing hΩ (r₁ - r₀) z S).congr ?_
  filter_upwards [(memLp_reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth).coeFn_toLp,
    ae_reverseTimeSeparatedVTestOfMemLp hΩ q hq v] with tau hS hz
  rw [hz, ContinuousLinearMap.map_smul]
  change q tau *
      ((memLp_reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth).toLp
        (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth) tau) v = _
  rw [hS]
  ring

private theorem integrable_form_raw_mul_multiplier
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (q : ℝ → ℝ) (hq : MemLp q (∞ : ℝ≥0∞) (reverseTimeVolume (r₁ - r₀)))
    (v : H10HilbertGraph hΩ) :
    Integrable (fun tau => reverseTimeSpatialForm hΩ r₁ tau a b c (u tau) v * q tau)
      (reverseTimeVolume (r₁ - r₀)) := by
  let A := reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth u
  let z := reverseTimeSeparatedVTestOfMemLp hΩ q hq v
  refine (integrable_reverseTimeDualPairing hΩ (r₁ - r₀) z A).congr ?_
  filter_upwards [ae_reverseTimeSpatialFormBochnerAction_apply r₀ r₁ h₀₁ hΩ hΩbounded
    a b c haSmooth hbSmooth hcSmooth u, ae_reverseTimeSeparatedVTestOfMemLp hΩ q hq v]
    with tau hA hz
  rw [hz, ContinuousLinearMap.map_smul]
  change q tau * A tau v = _
  rw [hA v]
  ring

private theorem canonical_affine_mass_eq_gelfand_mass
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hdu : HasGelfandWeakTimeDerivative hΩ T hT u g)
    (v : H10HilbertGraph hΩ)
    (qDeriv : ℝ → ℝ) (hqDeriv : MemLp qDeriv (∞ : ℝ≥0∞) (reverseTimeVolume T)) :
    (∫ tau, inner ℝ (valueCLM hΩ v)
      (Set.IccExtend hT.le (reverseTimeHilbertRepresentative hΩ T hT u g hdu) tau) * qDeriv tau
      ∂reverseTimeVolume T) =
      reverseTimeDualPairingRightCLM hΩ T
        (reverseTimeSeparatedVTestOfMemLp hΩ qDeriv hqDeriv v)
        (reverseTimeGelfandCLM hΩ T u) := by
  have hrep := (reverseTimeHilbertRepresentative_spec hΩ T hT u g hdu).1
  have hcanonical :
      (fun tau => inner ℝ (valueCLM hΩ v)
        (Set.IccExtend hT.le (reverseTimeHilbertRepresentative hΩ T hT u g hdu) tau) *
          qDeriv tau) =ᵐ[
          reverseTimeVolume T]
        fun tau => inner ℝ (valueCLM hΩ v) (valueCLM hΩ (u tau)) * qDeriv tau := by
    filter_upwards [hrep, ae_restrict_mem measurableSet_Ioo] with tau hrepTau ht
    have htIcc : tau ∈ Icc 0 T := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    rw [Set.IccExtend_of_mem hT.le _ htIcc, hrepTau ht]
  calc
    (∫ tau, inner ℝ (valueCLM hΩ v)
      (Set.IccExtend hT.le (reverseTimeHilbertRepresentative hΩ T hT u g hdu) tau) * qDeriv tau
      ∂reverseTimeVolume T) =
        ∫ tau, inner ℝ (valueCLM hΩ v) (valueCLM hΩ (u tau)) * qDeriv tau
          ∂reverseTimeVolume T := integral_congr_ae hcanonical
    _ = _ := (reverseTimeGelfand_pairing_multiplier_eq_integral hΩ u qDeriv hqDeriv v).symm

private noncomputable def affineReverseTimeMassPairing
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (v : H10HilbertGraph hΩ) : ℝ :=
  reverseTimeDualPairingRightCLM hΩ T
    (affineReverseTimeDerivativeVTest hΩ T hT v)
    (reverseTimeGelfandCLM hΩ T u)

private noncomputable def affineReverseTimeSourcePairing
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (S : ReverseTimeL2VStar hΩ T) (v : H10HilbertGraph hΩ) : ℝ :=
  reverseTimeDualPairingRightCLM hΩ T
    (affineReverseTimeVTest hΩ T hT v) S

private noncomputable def affineReverseTimeFormPairing
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (A : ReverseTimeL2V hΩ T →L[ℝ] ReverseTimeL2VStar hΩ T)
    (u : ReverseTimeL2V hΩ T) (v : H10HilbertGraph hΩ) : ℝ :=
  reverseTimeDualPairingRightCLM hΩ T
    (affineReverseTimeVTest hΩ T hT v) (A u)

private noncomputable def affineReverseTimeInitialPairing
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (v : H10HilbertGraph hΩ)
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) : ℝ :=
  inner ℝ (valueCLM hΩ v) initial

private noncomputable def affineReverseTimeResidualPairing
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (g : ReverseTimeL2VStar hΩ T) (v : H10HilbertGraph hΩ) : ℝ :=
  reverseTimeDualPairingRightCLM hΩ T (affineReverseTimeVTest hΩ T hT v) g

private theorem neg_add_sub_of_pairing_eq
    (source sourceRaw form formRaw initial : ℝ)
    (hSource : source = sourceRaw) (hForm : form = formRaw) :
    -sourceRaw + formRaw - initial = -source + form - initial := by
  rw [← hSource, ← hForm]

private theorem reverseTimeDualPairingRightCLM_sub
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (z : ReverseTimeL2V hΩ T)
    (f g : ReverseTimeL2VStar hΩ T) :
    reverseTimeDualPairingRightCLM hΩ T z (f - g) =
      reverseTimeDualPairingRightCLM hΩ T z f -
        reverseTimeDualPairingRightCLM hΩ T z g :=
  (reverseTimeDualPairingRightCLM hΩ T z).map_sub f g

private theorem reverseTimeHilbertRepresentative_affine_initial_pairing_wrapped
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hdu : HasGelfandWeakTimeDerivative hΩ T hT u g)
    (v : H10HilbertGraph hΩ) :
    (∫ tau, inner ℝ (valueCLM hΩ v)
        (Set.IccExtend hT.le (reverseTimeHilbertRepresentative hΩ T hT u g hdu) tau) *
          affineReverseTimeDerivative T tau ∂reverseTimeVolume T) =
      -affineReverseTimeResidualPairing hΩ T hT g v -
        affineReverseTimeInitialPairing hΩ v
          (reverseTimeInitialTrace hΩ T hT u g hdu) := by
  have hBoundary := reverseTimeHilbertRepresentative_affine_initial_pairing hΩ T hT u g hdu v
  have hPair := reverseTimeDualPairingRightCLM_ofMemLp_eq_integral hΩ g
    (affineReverseTimeMultiplier T) (memLp_affine_reverseTime_multiplier hT) v
  calc
    _ = -(∫ tau, g tau v * affineReverseTimeMultiplier T tau ∂reverseTimeVolume T) -
          inner ℝ (valueCLM hΩ v) (reverseTimeInitialTrace hΩ T hT u g hdu) := by
          simpa only [affineReverseTimeMultiplier, affineReverseTimeDerivative] using hBoundary
    _ = -reverseTimeDualPairingRightCLM hΩ T
          (reverseTimeSeparatedVTestOfMemLp hΩ (affineReverseTimeMultiplier T)
            (memLp_affine_reverseTime_multiplier hT) v) g -
          inner ℝ (valueCLM hΩ v) (reverseTimeInitialTrace hΩ T hT u g hdu) := by
          rw [← hPair]
    _ = _ := rfl



private theorem finite_affine_boundary_pairing_wrapped
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hLower : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
    (hcNonpos : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0)
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) (N k : ℕ) (hNk : k + 1 ≤ N) :
    affineReverseTimeMassPairing hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
        (reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial)
        (galerkinVector hΩ k) =
      -affineReverseTimeSourcePairing hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
          (reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth)
          (galerkinVector hΩ k) +
        affineReverseTimeFormPairing hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
          (reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
            haSmooth hbSmooth hcSmooth)
          (reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
            haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial)
          (galerkinVector hΩ k) -
        affineReverseTimeInitialPairing hΩ (galerkinVector hΩ k) initial := by
  let T := r₁ - r₀
  let eta := affineReverseTimeMultiplier T
  let etaDeriv := affineReverseTimeDerivative T
  let hEta := memLp_affine_reverseTime_multiplier (sub_pos.mpr h₀₁)
  let hEtaDeriv := memLp_affine_reverseTime_deriv (sub_pos.mpr h₀₁)
  let S := reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth
  let A := reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth
  let v : galerkinSpace hΩ N := ⟨galerkinVector hΩ k,
    galerkinSpace_mono hΩ hNk (by
      change galerkinVector hΩ k ∈ Submodule.span ℝ
        (Set.range fun i : Fin (k + 1) => galerkinVector hΩ i)
      apply Submodule.subset_span
      exact ⟨⟨k, Nat.lt_succ_self k⟩, rfl⟩)⟩
  let vk : galerkinSpace hΩ (k + 1) := ⟨galerkinVector hΩ k, by
    change galerkinVector hΩ k ∈ Submodule.span ℝ
      (Set.range fun i : Fin (k + 1) => galerkinVector hΩ i)
    apply Submodule.subset_span
    exact ⟨⟨k, Nat.lt_succ_self k⟩, rfl⟩⟩
  let UN := reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
    haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial
  change affineReverseTimeMassPairing hΩ T (sub_pos.mpr h₀₁) UN (galerkinVector hΩ k) =
    -affineReverseTimeSourcePairing hΩ T (sub_pos.mpr h₀₁) S (galerkinVector hΩ k) +
      affineReverseTimeFormPairing hΩ T (sub_pos.mpr h₀₁) A UN (galerkinVector hΩ k) -
      affineReverseTimeInitialPairing hΩ (galerkinVector hΩ k) initial
  have hT : 0 < T := by
    simpa only [T] using sub_pos.mpr h₀₁
  have hEtaDerivWithin : ∀ tau ∈ Icc 0 T,
      HasDerivWithinAt eta (etaDeriv tau) (Icc 0 T) tau := by
    intro tau _
    dsimp only [eta, etaDeriv]
    unfold affineReverseTimeMultiplier affineReverseTimeDerivative
    simpa only [div_eq_mul_inv, zero_sub, one_mul, Pi.sub_def, id_eq] using
      (hasDerivAt_const (x := tau) (1 : ℝ)).sub
        ((hasDerivAt_id (x := tau)).mul_const T⁻¹) |>.hasDerivWithinAt
  have hEtaTerminal : eta T = 0 := by
    dsimp only [eta, affineReverseTimeMultiplier]
    rw [div_self hT.ne']
    ring
  obtain ⟨_hMass, _hResidual, hBoundary⟩ :=
    reverseTimeGalerkinPrimal_boundaryTime r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
      haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial v eta etaDeriv
      (by simpa only [T] using hEtaDerivWithin) continuousOn_const
      (by simpa only [T] using hEtaTerminal)
  have hUNraw := ae_reverseTimeGalerkinPrimal_eq_raw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
    haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial
  have hMass : reverseTimeDualPairingRightCLM hΩ T
      (reverseTimeSeparatedVTestOfMemLp hΩ etaDeriv hEtaDeriv (galerkinVector hΩ k))
      (reverseTimeGelfandCLM hΩ T UN) =
      ∫ tau, inner ℝ (valueCLM hΩ (galerkinVector hΩ k))
        (valueCLM hΩ
          (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
            haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial tau)) * etaDeriv tau
        ∂reverseTimeVolume T := by
    calc
      _ = ∫ tau, inner ℝ (valueCLM hΩ (galerkinVector hΩ k)) (valueCLM hΩ (UN tau)) *
          etaDeriv tau ∂reverseTimeVolume T :=
        reverseTimeGelfand_pairing_multiplier_eq_integral hΩ UN etaDeriv hEtaDeriv
          (galerkinVector hΩ k)
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hUNraw] with tau hUNtau
        rw [hUNtau]
  have hSource := reverseTimeNegativeSource_pairing_ofMemLp_eq_integral_raw
    r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth eta hEta (galerkinVector hΩ k)
  have hForm := reverseTimeSpatialForm_pairing_ofMemLp_eq_integral
    r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth UN eta hEta
      (galerkinVector hΩ k)
  have hSourceInt := integrable_source_raw_mul_multiplier
    r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth eta hEta (galerkinVector hΩ k)
  have hFormInt := integrable_form_raw_mul_multiplier
    r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth UN eta hEta
      (galerkinVector hΩ k)
  have hSource' :
      affineReverseTimeSourcePairing hΩ T (sub_pos.mpr h₀₁) S (galerkinVector hΩ k) =
        ∫ tau, reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau
          (galerkinVector hΩ k) * eta tau ∂reverseTimeVolume T := by
    change reverseTimeDualPairingRightCLM hΩ T
        (affineReverseTimeVTest hΩ T (sub_pos.mpr h₀₁) (galerkinVector hΩ k)) S = _
    simpa only [T, eta, hEta, affineReverseTimeVTest] using hSource
  have hForm' :
      affineReverseTimeFormPairing hΩ T (sub_pos.mpr h₀₁) A UN (galerkinVector hΩ k) =
        ∫ tau, reverseTimeSpatialForm hΩ r₁ tau a b c (UN tau) (galerkinVector hΩ k) * eta tau
          ∂reverseTimeVolume T := by
    change reverseTimeDualPairingRightCLM hΩ T
        (affineReverseTimeVTest hΩ T (sub_pos.mpr h₀₁) (galerkinVector hΩ k)) (A UN) = _
    simpa only [T, eta, hEta, affineReverseTimeVTest] using hForm
  have hInitial := inner_value_galerkinInitialProjection_eq hΩ hNk initial vk
  have hInitial' :
      inner ℝ (valueCLM hΩ (galerkinVector hΩ k))
        (valueCLM hΩ (galerkinInitialProjection hΩ N initial : H10HilbertGraph hΩ)) =
      inner ℝ (valueCLM hΩ (galerkinVector hΩ k)) initial := by
    simpa only [vk] using hInitial
  have hRaw :
      (∫ tau, inner ℝ (valueCLM hΩ (galerkinVector hΩ k))
        (valueCLM hΩ
          (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
            haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial tau)) * etaDeriv tau
        ∂reverseTimeVolume T) =
      -(∫ tau, reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau
          (galerkinVector hΩ k) * eta tau ∂reverseTimeVolume T) +
        ∫ tau, reverseTimeSpatialForm hΩ r₁ tau a b c (UN tau) (galerkinVector hΩ k) * eta tau
          ∂reverseTimeVolume T - inner ℝ (valueCLM hΩ (galerkinVector hΩ k)) initial := by
    calc
      _ = -(∫ tau,
          (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau
            (galerkinVector hΩ k) -
          reverseTimeSpatialForm hΩ r₁ tau a b c
            (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
              haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial tau)
            (galerkinVector hΩ k)) * eta tau ∂reverseTimeVolume T) -
          inner ℝ (valueCLM hΩ (galerkinVector hΩ k))
            (valueCLM hΩ (galerkinInitialProjection hΩ N initial : H10HilbertGraph hΩ)) *
              eta 0 := by
          simpa only [T, v, UN] using hBoundary
      _ = -(∫ tau, reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau
          (galerkinVector hΩ k) * eta tau -
          reverseTimeSpatialForm hΩ r₁ tau a b c (UN tau) (galerkinVector hΩ k) * eta tau
            ∂reverseTimeVolume T) -
          inner ℝ (valueCLM hΩ (galerkinVector hΩ k))
            (valueCLM hΩ (galerkinInitialProjection hΩ N initial : H10HilbertGraph hΩ)) *
              eta 0 := by
          congr 2
          apply integral_congr_ae
          filter_upwards [hUNraw] with tau hUNtau
          rw [hUNtau]
          ring
      _ = -(∫ tau, reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau
          (galerkinVector hΩ k) * eta tau ∂reverseTimeVolume T -
          ∫ tau, reverseTimeSpatialForm hΩ r₁ tau a b c (UN tau) (galerkinVector hΩ k) * eta tau
            ∂reverseTimeVolume T) -
          inner ℝ (valueCLM hΩ (galerkinVector hΩ k)) initial := by
          rw [integral_sub hSourceInt hFormInt]
          rw [hInitial']
          dsimp only [eta, affineReverseTimeMultiplier]
          ring
      _ = _ := by ring
  calc
    affineReverseTimeMassPairing hΩ T (sub_pos.mpr h₀₁) UN (galerkinVector hΩ k) =
        ∫ tau, inner ℝ (valueCLM hΩ (galerkinVector hΩ k))
          (valueCLM hΩ
            (reverseTimeGalerkinPrimalRaw r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
              haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos N initial tau)) * etaDeriv tau
          ∂reverseTimeVolume T := by
        simpa only [affineReverseTimeMassPairing, affineReverseTimeDerivativeVTest, T, etaDeriv,
          hEtaDeriv, UN] using hMass
    _ = -(∫ tau, reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth tau
          (galerkinVector hΩ k) * eta tau ∂reverseTimeVolume T) +
        ∫ tau, reverseTimeSpatialForm hΩ r₁ tau a b c (UN tau) (galerkinVector hΩ k) * eta tau
          ∂reverseTimeVolume T - inner ℝ (valueCLM hΩ (galerkinVector hΩ k)) initial := hRaw
    _ = -affineReverseTimeSourcePairing hΩ T (sub_pos.mpr h₀₁) S (galerkinVector hΩ k) +
        affineReverseTimeFormPairing hΩ T (sub_pos.mpr h₀₁) A UN (galerkinVector hΩ k) -
        affineReverseTimeInitialPairing hΩ (galerkinVector hΩ k) initial := by
        exact neg_add_sub_of_pairing_eq _ _ _ _ _ hSource' hForm'


variable {d : ℕ} {Ω : Set (PDE.Vec d)}
variable
  (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam)
  (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
  (a : CoefficientField d)
  (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
  (haSmooth : IsSmoothOnNeighborhood
    (fun z : TimeVelocity d => a z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hbSmooth : IsSmoothOnNeighborhood
    (fun z : TimeVelocity d => b z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hcSmooth : IsSmoothOnNeighborhood
    (fun z : TimeVelocity d => c z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hFSmooth : IsSmoothOnNeighborhood
    (fun z : TimeVelocity d => F z.1 z.2)
    (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hLower : ∀ z : TimeVelocity d,
    z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → lam • (1 : PDE.Mat d) ≤ a z.1 z.2)
  (hcNonpos : ∀ z : TimeVelocity d,
    z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0)

include lam hlam hLower hcNonpos

private theorem reverseTimeGalerkinPrimal_initialTrace_pairing
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (U : ReverseTimeL2V hΩ (r₁ - r₀))
    (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (hclm : ∀ ell : ReverseTimeL2V hΩ (r₁ - r₀) →L[ℝ] ℝ,
      Tendsto (fun n => ell
        (reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos (phi n) initial))
        atTop (𝓝 (ell U)))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) U
      (reverseTimeFormResidual r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth F hFSmooth U))
    (k : ℕ) :
    inner ℝ (valueCLM hΩ (galerkinVector hΩ k))
      (reverseTimeInitialTrace hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) U
        (reverseTimeFormResidual r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth F hFSmooth U) hdu) =
      inner ℝ (valueCLM hΩ (galerkinVector hΩ k)) initial := by
  let T := r₁ - r₀
  let eta := affineReverseTimeMultiplier T
  let etaDeriv := affineReverseTimeDerivative T
  let hEta := memLp_affine_reverseTime_multiplier (sub_pos.mpr h₀₁)
  let hEtaDeriv := memLp_affine_reverseTime_deriv (sub_pos.mpr h₀₁)
  let S := reverseTimeNegativeSource r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth
  let A := reverseTimeSpatialFormBochnerAction r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth
  let g := reverseTimeFormResidual r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth F hFSmooth U
  let trace := reverseTimeInitialTrace hΩ T (sub_pos.mpr h₀₁) U g hdu
  change inner ℝ (valueCLM hΩ (galerkinVector hΩ k)) trace =
    inner ℝ (valueCLM hΩ (galerkinVector hΩ k)) initial
  let massEll : ReverseTimeL2V hΩ T →L[ℝ] ℝ :=
    (reverseTimeDualPairingRightCLM hΩ T
      (reverseTimeSeparatedVTestOfMemLp hΩ etaDeriv hEtaDeriv (galerkinVector hΩ k))).comp
      (reverseTimeGelfandCLM hΩ T)
  let formEll : ReverseTimeL2V hΩ T →L[ℝ] ℝ :=
    (reverseTimeDualPairingRightCLM hΩ T
      (reverseTimeSeparatedVTestOfMemLp hΩ eta hEta (galerkinVector hΩ k))).comp A
  let source : ℝ := reverseTimeDualPairingRightCLM hΩ T
    (reverseTimeSeparatedVTestOfMemLp hΩ eta hEta (galerkinVector hΩ k)) S
  have hIndex : ∀ᶠ n in atTop, k + 1 ≤ phi n := by
    filter_upwards [eventually_ge_atTop (k + 1)] with n hn
    exact hn.trans (hphi.id_le n)
  have hFinite :
      (fun n => massEll
        (reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos (phi n) initial)) =ᶠ[atTop]
      fun n => -source + formEll
        (reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos (phi n) initial) -
          inner ℝ (valueCLM hΩ (galerkinVector hΩ k)) initial := by
    filter_upwards [hIndex] with n hn
    simpa only [massEll, formEll, source, ContinuousLinearMap.comp_apply, T, eta, etaDeriv,
      hEta, hEtaDeriv, S, A, affineReverseTimeMassPairing,
      affineReverseTimeSourcePairing, affineReverseTimeFormPairing,
      affineReverseTimeInitialPairing, affineReverseTimeVTest,
      affineReverseTimeDerivativeVTest] using
        finite_affine_boundary_pairing_wrapped r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial (phi n) k hn
  have hMass := hclm massEll
  have hForm := hclm formEll
  have hRight : Tendsto
      (fun n => -source + formEll
        (reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos (phi n) initial) -
        inner ℝ (valueCLM hΩ (galerkinVector hΩ k)) initial)
      atTop (𝓝 (-source + formEll U -
        inner ℝ (valueCLM hΩ (galerkinVector hΩ k)) initial)) :=
    ((tendsto_const_nhds.neg.add hForm).sub tendsto_const_nhds)
  have hLimit : massEll U = -source + formEll U -
      inner ℝ (valueCLM hΩ (galerkinVector hΩ k)) initial :=
    tendsto_nhds_unique_of_eventuallyEq hMass hRight hFinite
  have hResidual : reverseTimeDualPairingRightCLM hΩ T
      (reverseTimeSeparatedVTestOfMemLp hΩ eta hEta (galerkinVector hΩ k)) g =
      source - formEll U := by
    exact reverseTimeDualPairingRightCLM_sub hΩ T
      (reverseTimeSeparatedVTestOfMemLp hΩ eta hEta (galerkinVector hΩ k)) S (A U)
  have hBoundary := reverseTimeHilbertRepresentative_affine_initial_pairing hΩ T
    (sub_pos.mpr h₀₁) U g hdu (galerkinVector hΩ k)
  have hCanonical := canonical_affine_mass_eq_gelfand_mass hΩ T (sub_pos.mpr h₀₁) U g hdu
    (galerkinVector hΩ k) etaDeriv hEtaDeriv
  have hTrace : massEll U =
      -affineReverseTimeResidualPairing hΩ T (sub_pos.mpr h₀₁) g (galerkinVector hΩ k) -
      affineReverseTimeInitialPairing hΩ (galerkinVector hΩ k) trace := by
    calc
      massEll U =
          (∫ tau, inner ℝ (valueCLM hΩ (galerkinVector hΩ k))
            (Set.IccExtend (sub_pos.mpr h₀₁).le
              (reverseTimeHilbertRepresentative hΩ T (sub_pos.mpr h₀₁) U g hdu) tau) *
              etaDeriv tau ∂reverseTimeVolume T) := hCanonical.symm
      _ = -affineReverseTimeResidualPairing hΩ T (sub_pos.mpr h₀₁) g (galerkinVector hΩ k) -
            affineReverseTimeInitialPairing hΩ (galerkinVector hΩ k) trace := by
            simpa only [etaDeriv] using
              reverseTimeHilbertRepresentative_affine_initial_pairing_wrapped hΩ T
                (sub_pos.mpr h₀₁) U g hdu (galerkinVector hΩ k)
  dsimp only [massEll, formEll, source, affineReverseTimeResidualPairing,
    affineReverseTimeInitialPairing, affineReverseTimeVTest, eta, hEta,
    affineReverseTimeMultiplier] at hLimit hTrace hResidual
  linarith


/-- A reverse-time Galerkin limit has the prescribed canonical initial trace. -/
theorem exists_reverseTimeGalerkinPrimal_initialTrace
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    ∃ (U : ReverseTimeL2V hΩ (r₁ - r₀)),
      ∃ hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) U
        (reverseTimeFormResidual r₀ r₁ h₀₁ hΩ hΩbounded a b c
          haSmooth hbSmooth hcSmooth F hFSmooth U),
        reverseTimeInitialTrace hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) U
          (reverseTimeFormResidual r₀ r₁ h₀₁ hΩ hΩbounded a b c
            haSmooth hbSmooth hcSmooth F hFSmooth U) hdu = initial := by
  obtain ⟨U, phi, hphi, hclm, hdu⟩ :=
    exists_strictMono_tendsto_clm_reverseTimeGalerkinPrimal_residual_derivative
      r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F haSmooth hbSmooth hcSmooth hFSmooth
      hLower hcNonpos initial
  let T := r₁ - r₀
  let g := reverseTimeFormResidual r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth F hFSmooth U
  let trace := reverseTimeInitialTrace hΩ T (sub_pos.mpr h₀₁) U g hdu
  refine ⟨U, hdu, ?_⟩
  apply scalarLpToH10HilbertGraphDual_injective hΩ
  apply ContinuousLinearMap.ext
  intro v
  have hvClosure : v ∈ closure (Set.range (galerkinVector hΩ)) := by
    rw [(denseRange_galerkinVector hΩ).closure_range]
    exact mem_univ _
  obtain ⟨vN, hvN, hv⟩ := mem_closure_iff_seq_limit.mp hvClosure
  choose k hk using hvN
  have hPair : ∀ k : ℕ,
      inner ℝ (valueCLM hΩ (galerkinVector hΩ k)) trace =
        inner ℝ (valueCLM hΩ (galerkinVector hΩ k)) initial := by
    intro k
    simpa only [T, g, trace] using
      reverseTimeGalerkinPrimal_initialTrace_pairing r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial U phi hphi hclm hdu k
  have hLeft : Tendsto (fun n =>
      scalarLpToH10HilbertGraphDual hΩ trace (vN n)) atTop
      (𝓝 (scalarLpToH10HilbertGraphDual hΩ trace v)) :=
    (scalarLpToH10HilbertGraphDual hΩ trace).continuous.tendsto v |>.comp hv
  have hRight : Tendsto (fun n =>
      scalarLpToH10HilbertGraphDual hΩ initial (vN n)) atTop
      (𝓝 (scalarLpToH10HilbertGraphDual hΩ initial v)) :=
    (scalarLpToH10HilbertGraphDual hΩ initial).continuous.tendsto v |>.comp hv
  have hRange : ∀ n,
      scalarLpToH10HilbertGraphDual hΩ trace (vN n) =
        scalarLpToH10HilbertGraphDual hΩ initial (vN n) := by
    intro n
    simpa only [scalarLpToH10HilbertGraphDual_apply, hk n] using hPair (k n)
  exact tendsto_nhds_unique_of_eventuallyEq hLeft hRight (Eventually.of_forall hRange)


/-- A supplied common reverse-time Galerkin subsequence has the prescribed
canonical initial trace. -/
theorem reverseTimeGalerkinPrimal_initialTrace_of_strictMono_tendsto_clm
    (initial : PDE.ScalarLp Ω (2 : ℝ≥0∞))
    (U : ReverseTimeL2V hΩ (r₁ - r₀))
    (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (hclm : ∀ ell : ReverseTimeL2V hΩ (r₁ - r₀) →L[ℝ] ℝ,
      Tendsto (fun n => ell
        (reverseTimeGalerkinPrimal r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
          haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos (phi n) initial))
        atTop (𝓝 (ell U)))
    (hdu : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) U
      (reverseTimeFormResidual r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth F hFSmooth U)) :
    reverseTimeInitialTrace hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) U
      (reverseTimeFormResidual r₀ r₁ h₀₁ hΩ hΩbounded a b c
        haSmooth hbSmooth hcSmooth F hFSmooth U) hdu = initial := by
  let T := r₁ - r₀
  let g := reverseTimeFormResidual r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth F hFSmooth U
  let trace := reverseTimeInitialTrace hΩ T (sub_pos.mpr h₀₁) U g hdu
  apply scalarLpToH10HilbertGraphDual_injective hΩ
  apply ContinuousLinearMap.ext
  intro v
  have hvClosure : v ∈ closure (Set.range (galerkinVector hΩ)) := by
    rw [(denseRange_galerkinVector hΩ).closure_range]
    exact mem_univ _
  obtain ⟨vN, hvN, hv⟩ := mem_closure_iff_seq_limit.mp hvClosure
  choose k hk using hvN
  have hPair : ∀ k : ℕ,
      inner ℝ (valueCLM hΩ (galerkinVector hΩ k)) trace =
        inner ℝ (valueCLM hΩ (galerkinVector hΩ k)) initial := by
    intro k
    simpa only [T, g, trace] using
      reverseTimeGalerkinPrimal_initialTrace_pairing r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c F
        haSmooth hbSmooth hcSmooth hFSmooth hLower hcNonpos initial U phi hphi hclm hdu k
  have hLeft : Tendsto (fun n =>
      scalarLpToH10HilbertGraphDual hΩ trace (vN n)) atTop
      (𝓝 (scalarLpToH10HilbertGraphDual hΩ trace v)) :=
    (scalarLpToH10HilbertGraphDual hΩ trace).continuous.tendsto v |>.comp hv
  have hRight : Tendsto (fun n =>
      scalarLpToH10HilbertGraphDual hΩ initial (vN n)) atTop
      (𝓝 (scalarLpToH10HilbertGraphDual hΩ initial v)) :=
    (scalarLpToH10HilbertGraphDual hΩ initial).continuous.tendsto v |>.comp hv
  have hRange : ∀ n,
      scalarLpToH10HilbertGraphDual hΩ trace (vN n) =
        scalarLpToH10HilbertGraphDual hΩ initial (vN n) := by
    intro n
    simpa only [scalarLpToH10HilbertGraphDual_apply, hk n] using hPair (k n)
  exact tendsto_nhds_unique_of_eventuallyEq hLeft hRight (Eventually.of_forall hRange)

end HypoellipticAleksandrov.Parabolic.Dirichlet

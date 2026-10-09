module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeTests
public import PDEFoundation.Sobolev.OneDimensional.PrimitiveWeakIdentity
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Reverse-time dual Bochner primitives

This module constructs the literal restricted-measure Bochner primitive of a
reverse-time `L²(V*)` curve.  It contains no representative, trace, energy,
weak PDE, or Lions--Magenes assertion.
-/

@[expose] public section

open Function MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

private theorem integrable_vstar
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (g : ReverseTimeL2VStar hΩ T) :
    Integrable (fun tau => g tau) (reverseTimeVolume T) := by
  letI : IsFiniteMeasure (reverseTimeVolume T) := by
    change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) T))
    infer_instance
  have hg : MemLp (g : ℝ → H10HilbertGraphDual hΩ) 2 (reverseTimeVolume T) :=
    MeasureTheory.Lp.memLp g
  exact hg.integrable (by norm_num)

/-- The restricted-measure Bochner primitive of a reverse-time dual curve. -/
noncomputable def reverseTimeVStarPrimitive
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (g : ReverseTimeL2VStar hΩ T) :
    ℝ → H10HilbertGraphDual hΩ :=
  fun t => ∫ tau in Set.Ioc 0 t, g tau ∂reverseTimeVolume T

/-- A bundled reverse-time `L²(V*)` curve has an integrable representative
for the literal restricted time measure. -/
theorem integrable_reverseTimeVStar
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (g : ReverseTimeL2VStar hΩ T) :
    MeasureTheory.Integrable (fun tau => g tau) (reverseTimeVolume T) :=
  integrable_vstar hΩ T g

/-- The dual primitive is continuous on the closed reverse-time interval. -/
theorem continuousOn_reverseTimeVStarPrimitive
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (g : ReverseTimeL2VStar hΩ T) :
    ContinuousOn (reverseTimeVStarPrimitive hΩ T g) (Set.Icc 0 T) := by
  letI : NullSingletonClass (reverseTimeVolume T) := by
    change NullSingletonClass (volume.restrict (Ioo (0 : ℝ) T))
    infer_instance
  exact intervalIntegral.continuousOn_primitive
    (integrable_vstar hΩ T g).integrableOn

/-- The dual primitive restricted to the closed reverse-time interval. -/
noncomputable def reverseTimeVStarPrimitiveOnIcc
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (g : ReverseTimeL2VStar hΩ T) :
    C(↥(Set.Icc 0 T), H10HilbertGraphDual hΩ) :=
  ⟨fun t => reverseTimeVStarPrimitive hΩ T g t,
    (continuousOn_reverseTimeVStarPrimitive hΩ T g).restrict⟩

/-- The restricted-measure primitive vanishes at time zero. -/
theorem reverseTimeVStarPrimitive_zero
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (g : ReverseTimeL2VStar hΩ T) :
    reverseTimeVStarPrimitive hΩ T g 0 = 0 := by
  change ∫ tau in Set.Ioc 0 0, g tau ∂reverseTimeVolume T = 0
  simp

/-- Increments of the dual primitive are the corresponding restricted-time integrals. -/
theorem reverseTimeVStarPrimitive_sub
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (g : ReverseTimeL2VStar hΩ T)
    {s t : ℝ} (hs : s ∈ Set.Icc 0 T) (ht : t ∈ Set.Icc 0 T)
    (hst : s ≤ t) :
    reverseTimeVStarPrimitive hΩ T g t -
        reverseTimeVStarPrimitive hΩ T g s =
      ∫ tau in Set.Ioc s t, g tau ∂reverseTimeVolume T := by
  change (∫ tau in Ioc 0 t, g tau ∂reverseTimeVolume T) -
      ∫ tau in Ioc 0 s, g tau ∂reverseTimeVolume T = _
  rw [← intervalIntegral.integral_of_le ht.1,
    ← intervalIntegral.integral_of_le hs.1,
    intervalIntegral.integral_interval_sub_left
      (integrable_vstar hΩ T g).intervalIntegrable
      (integrable_vstar hΩ T g).intervalIntegrable,
    intervalIntegral.integral_of_le hst]

/-- Evaluation by a fixed spatial test commutes with the dual primitive. -/
theorem reverseTimeVStarPrimitive_apply
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (g : ReverseTimeL2VStar hΩ T)
    (v : H10HilbertGraph hΩ) (t : ℝ) :
    reverseTimeVStarPrimitive hΩ T g t v =
      ∫ tau in Set.Ioc 0 t, (g tau) v ∂reverseTimeVolume T := by
  exact ContinuousLinearMap.integral_apply
    ((integrable_vstar hΩ T g).integrableOn) v

/-- A fixed-vector evaluation of the dual primitive is integrable in reverse time. -/
theorem integrable_reverseTimeVStarPrimitive_apply
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (g : ReverseTimeL2VStar hΩ T)
    (v : H10HilbertGraph hΩ) :
    MeasureTheory.Integrable
      (fun tau => reverseTimeVStarPrimitive hΩ T g tau v)
      (reverseTimeVolume T) := by
  change IntegrableOn
    (fun tau => reverseTimeVStarPrimitive hΩ T g tau v)
    (Ioo (0 : ℝ) T) volume
  have hcont : ContinuousOn
      (fun tau => reverseTimeVStarPrimitive hΩ T g tau v) (Icc 0 T) :=
    (ContinuousLinearMap.apply ℝ ℝ v).continuous.comp_continuousOn
      (continuousOn_reverseTimeVStarPrimitive hΩ T g)
  exact (hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self)

private theorem primitive_apply_on_Ioo
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (g : ReverseTimeL2VStar hΩ T)
    (v : H10HilbertGraph hΩ) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    reverseTimeVStarPrimitive hΩ T g t v =
      PDE.intervalPrimitive 0 (fun s => (g s) v) t := by
  rw [reverseTimeVStarPrimitive_apply]
  change (∫ s in Ioc 0 t, (g s) v ∂reverseTimeVolume T) = _
  rw [show (∫ s in Ioc 0 t, (g s) v ∂reverseTimeVolume T) =
      ∫ s in Ioc 0 t, (g s) v ∂volume by
    simp only [reverseTimeVolume, reverseTimeOpenInterval,
      Measure.restrict_restrict measurableSet_Ioc]
    rw [inter_eq_left.mpr]
    intro s hs
    exact ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩]
  exact (intervalIntegral.integral_of_le (le_of_lt ht.1)).symm

/-- The dual primitive has weak derivative `g` against compact scalar tests. -/
theorem reverseTimeVStarPrimitive_test_deriv
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (g : ReverseTimeL2VStar hΩ T)
    (v : H10HilbertGraph hΩ) (eta : ReverseTimeScalarTest T) :
    MeasureTheory.Integrable
      (fun tau => reverseTimeVStarPrimitive hΩ T g tau v * eta.deriv tau)
      (reverseTimeVolume T) ∧
    MeasureTheory.Integrable (fun tau => (g tau) v * eta tau)
      (reverseTimeVolume T) ∧
    (∫ tau,
      reverseTimeVStarPrimitive hΩ T g tau v * eta.deriv tau
      ∂reverseTimeVolume T) =
      -(∫ tau, (g tau) v * eta tau ∂reverseTimeVolume T) := by
  have hleft : Integrable
      (fun tau => reverseTimeVStarPrimitive hΩ T g tau v * eta.deriv tau)
      (reverseTimeVolume T) := by
    change IntegrableOn
      (fun tau => reverseTimeVStarPrimitive hΩ T g tau v * eta.deriv tau)
      (Ioo (0 : ℝ) T) volume
    have hcont : ContinuousOn
        (fun tau => reverseTimeVStarPrimitive hΩ T g tau v * eta.deriv tau)
        (Icc 0 T) :=
      ((ContinuousLinearMap.apply ℝ ℝ v).continuous.comp_continuousOn
        (continuousOn_reverseTimeVStarPrimitive hΩ T g)).mul
        eta.contDiff_deriv.continuous.continuousOn
    exact hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  letI : IsFiniteMeasure (reverseTimeVolume T) := by
    change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) T))
    infer_instance
  have hqLp : MemLp (fun tau => (g tau) v) 2 (reverseTimeVolume T) :=
    (MeasureTheory.Lp.memLp g).continuousLinearMap_comp
      (ContinuousLinearMap.apply ℝ ℝ v)
  have hright : Integrable (fun tau => (g tau) v * eta tau)
      (reverseTimeVolume T) := by
    simpa only [Pi.mul_def] using hqLp.integrable_mul (eta.memLp 2)
  refine ⟨hleft, hright, ?_⟩
  have hqIcc : IntegrableOn (fun tau => (g tau) v) (Icc (0 : ℝ) T) volume := by
    change Integrable (fun tau => (g tau) v) (volume.restrict (Icc (0 : ℝ) T))
    simpa only [reverseTimeVolume, reverseTimeOpenInterval,
      restrict_Ioo_eq_restrict_Icc] using hqLp.integrable (by norm_num)
  have hae : (fun tau => reverseTimeVStarPrimitive hΩ T g tau v * eta.deriv tau) =ᵐ[
      reverseTimeVolume T] fun tau =>
        PDE.intervalPrimitive 0 (fun s => (g s) v) tau * _root_.deriv eta tau := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with tau ht
    rw [primitive_apply_on_Ioo hΩ T g v ht, eta.deriv_apply]
  calc
    (∫ tau, reverseTimeVStarPrimitive hΩ T g tau v * eta.deriv tau
      ∂reverseTimeVolume T) =
        ∫ tau, PDE.intervalPrimitive 0 (fun s => (g s) v) tau * _root_.deriv eta tau
          ∂reverseTimeVolume T := integral_congr_ae hae
    _ = -(∫ tau, (g tau) v * eta tau ∂reverseTimeVolume T) := by
      simpa only [reverseTimeVolume, reverseTimeOpenInterval] using
        PDE.intervalPrimitive_scalar_weak_identity_Ioo hqIcc
          (eta.contDiff.of_le (by simp)) eta.tsupport_subset

end HypoellipticAleksandrov.Parabolic.Dirichlet

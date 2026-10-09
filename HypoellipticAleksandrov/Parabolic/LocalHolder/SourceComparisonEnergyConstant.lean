module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeHilbertTraces
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Stationary reverse-time Sobolev barriers

Constant curves retain their spatial H10 value at every canonical closed time and have
zero weak time derivative. These facts refer to the quotient-valued energy carriers.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter MeasureTheory Set Dirichlet
open scoped ENNReal Topology RealInnerProductSpace

/-- Restricted volume on a finite time interval is finite. -/
local instance finiteSourceTimeVolume (T : ℝ) : IsFiniteMeasure (reverseTimeVolume T) := by
  change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) T))
  infer_instance

/-- The literal constant curve with one fixed zero-boundary spatial Sobolev value. -/
def stationarySourceCurve {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (q : H10HilbertGraph hΩ) : ReverseTimeL2V hΩ T :=
  Lp.const 2 (reverseTimeVolume T) q

/-- The selected raw stationary curve agrees almost everywhere with its constant value. -/
theorem stationarySourceCurve_ae {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (q : H10HilbertGraph hΩ) :
    stationarySourceCurve hΩ T q =ᵐ[reverseTimeVolume T] fun _ => q := by
  simpa only [stationarySourceCurve, Function.const_def] using
    (Lp.coeFn_const (2 : ℝ≥0∞) (reverseTimeVolume T) q)

/-- A compact reverse-time test has zero integral of its ordinary time derivative. -/
theorem integral_reverseTimeScalarTest_deriv_zero {T : ℝ} (hT : 0 < T)
    (η : ReverseTimeScalarTest T) : (∫ t, η.deriv t ∂reverseTimeVolume T) = 0 := by
  have hzero (t : ℝ) (ht : t ∉ Ioo 0 T) : η t = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => ht (η.tsupport_subset h))
  change (∫ t in Ioo 0 T, deriv (η : ℝ → ℝ) t) = 0
  rw [restrict_Ioo_eq_restrict_Ioc, ← intervalIntegral.integral_of_le hT.le,
    intervalIntegral.integral_deriv_eq_sub
      (fun _ _ => η.contDiff.differentiable (by simp) _)
      (η.contDiff_deriv.continuous.intervalIntegrable 0 T)]
  rw [hzero T (by simp), hzero 0 (by simp), sub_self]

/-- Stationary Sobolev curves have zero Gelfand weak time derivative. -/
theorem stationarySourceCurve_hasWeakTimeDerivative {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T) (q : H10HilbertGraph hΩ) :
    HasGelfandWeakTimeDerivative hΩ T hT (stationarySourceCurve hΩ T q) 0 := by
  intro v η
  refine ⟨integrable_reverseTimeWeakDerivative_left hΩ T _ v η,
    integrable_reverseTimeWeakDerivative_right hΩ T 0 v η, ?_⟩
  have hval : reverseTimeValueCLM hΩ T (stationarySourceCurve hΩ T q) =ᵐ[reverseTimeVolume T]
      fun _ => valueCLM hΩ q := by
    filter_upwards [coeFn_reverseTimeValueCLM hΩ T (stationarySourceCurve hΩ T q),
      stationarySourceCurve_ae hΩ T q] with t ht hq
    rw [ht, hq]
  have hleft : (∫ t,
      inner ℝ (valueCLM hΩ v)
        (reverseTimeValueCLM hΩ T (stationarySourceCurve hΩ T q) t) * η.deriv t
        ∂reverseTimeVolume T) = 0 := by
    calc
      _ = ∫ t, inner ℝ (valueCLM hΩ v) (valueCLM hΩ q) * η.deriv t
          ∂reverseTimeVolume T := integral_congr_ae (hval.mono fun _ ht => by rw [ht])
      _ = inner ℝ (valueCLM hΩ v) (valueCLM hΩ q) *
          ∫ t, η.deriv t ∂reverseTimeVolume T := integral_const_mul _ _
      _ = 0 := by rw [integral_reverseTimeScalarTest_deriv_zero hT η, mul_zero]
  rw [hleft]
  have hright : (∫ t, ((0 : ReverseTimeL2VStar hΩ T) t) v * η t
      ∂reverseTimeVolume T) = 0 := by
    calc
      _ = ∫ _ : ℝ, (0 : ℝ) ∂reverseTimeVolume T := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_zero (H10HilbertGraphDual hΩ) 2 (reverseTimeVolume T)]
          with t ht
        rw [ht]
        change (0 : ℝ) * η t = 0
        exact zero_mul _
      _ = 0 := integral_zero _ _
  rw [hright, neg_zero]

/-- Canonical closed-time values of a stationary curve equal its fixed spatial value. -/
theorem stationarySourceCurve_hilbertRepresentative {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T) (q : H10HilbertGraph hΩ) :
    reverseTimeHilbertRepresentative hΩ T hT (stationarySourceCurve hΩ T q) 0
      (stationarySourceCurve_hasWeakTimeDerivative hΩ T hT q) =
        ContinuousMap.const (Icc 0 T) (valueCLM hΩ q) := by
  apply (reverseTimeHilbertRepresentative_spec hΩ T hT
    (stationarySourceCurve hΩ T q) 0
    (stationarySourceCurve_hasWeakTimeDerivative hΩ T hT q)).1.unique hT
  filter_upwards [stationarySourceCurve_ae hΩ T q] with t ht hti
  change valueCLM hΩ q = valueCLM hΩ (stationarySourceCurve hΩ T q t)
  rw [ht]

end HypoellipticAleksandrov.Parabolic.LocalHolder

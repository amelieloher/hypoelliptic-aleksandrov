module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.KillingComparison
public import HypoellipticAleksandrov.KineticAleksandrov.Interval.KillingJets
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.UniquenessMeasure
import Mathlib.Topology.Order.Compact

/-! # Regularized endpoint comparison and its terminal limit

Smooth compact tests are scaled strictly below one. Compactness of their supports
makes the positive endpoint distance uniform, permitting the terminal epsilon limit.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory Filter Topology HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay
open scoped MatrixOrder

/-- The scalar diagonal inherits the source lower ellipticity bound. -/
theorem interval_coefficient_lower {lam Lam : ℝ} (B : CoefficientField 1)
    (hB : IsSectionTwoCoefficient lam Lam B) (r : ℝ) (v : PDE.Vec 1) :
    lam ≤ B r v 0 0 := by
  have h := (hB.2.2.2.2.1 r v).diag_nonneg (i := (0 : Fin 1))
  simpa only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul, mul_one, sub_nonneg] using h

/-- Coordinates of the closure of an interval satisfy the closed endpoint bounds. -/
theorem interval_coordinate_closure {a c : ℝ} {v : PDE.Vec 1}
    (hv : v ∈ closure (PDE.oneDimensionalAxisBox a c)) : a ≤ v 0 ∧ v 0 ≤ c := by
  have hsub : PDE.oneDimensionalAxisBox a c ⊆ {w : PDE.Vec 1 | a ≤ w 0 ∧ w 0 ≤ c} := by
    intro w hw
    have hh := PDE.mem_oneDimensionalAxisBox_iff.mp hw
    exact ⟨hh.1.le, hh.2.le⟩
  exact closure_minimal hsub ((isClosed_le continuous_const (continuous_apply 0)).inter
    (isClosed_le (continuous_apply 0) continuous_const)) hv

/-- Positive endpoint distance on compact test support provides eventual terminal domination. -/
theorem endpointHeat_terminal_domination {lam s e κ : ℝ} (hlam : 0 < lam)
    (hκ0 : 0 ≤ κ) (hκ : κ < 1) (φ : PDE.Vec 1 → ℝ) (hφc : HasCompactSupport φ)
    (hφ : ∀ v, 0 ≤ φ v ∧ φ v ≤ 1)
    (hpos : ∀ v ∈ tsupport φ, 0 < s * (v 0 - e)) :
    ∀ᶠ ε in nhdsWithin 0 (Ioi 0),
      ∀ v ∈ tsupport φ, κ * φ v ≤ intervalHeat lam ε (s * (v 0 - e)) := by
  by_cases hempty : (tsupport φ).Nonempty
  · have hc : Continuous (fun v : PDE.Vec 1 => s * (v 0 - e)) := by fun_prop
    obtain ⟨v₀, hv₀, hmin⟩ := hφc.exists_isMinOn hempty hc.continuousOn
    have ht := tendsto_intervalHeat_time_zero hlam (hpos v₀ hv₀)
    have he := ht.eventually (eventually_gt_nhds hκ)
    filter_upwards [he, self_mem_nhdsWithin] with ε hε hεpos v hv
    calc κ * φ v ≤ κ := by
          exact mul_le_of_le_one_right hκ0 (hφ v).2
      _ ≤ intervalHeat lam ε (s * (v₀ 0 - e)) := hε.le
      _ ≤ intervalHeat lam ε (s * (v 0 - e)) :=
        intervalHeat_mono_distance hlam hεpos (hmin hv)
  · exact Eventually.of_forall fun _ v hv => (hempty ⟨v, hv⟩).elim

/-- Smooth tests on the interval satisfy the endpoint killing estimate.
The endpoint geometry premises are discharged for both endpoints in `Killing`. -/
theorem interval_endpoint_test_bound {a c lam Lam σ τ s e : ℝ}
    (hac : a < c) (hστ : σ < τ) (hlam : 0 < lam) (hs : s ^ 2 = 1)
    (B : CoefficientField 1) (hB : IsSectionTwoCoefficient lam Lam B)
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (hpar : HasParabolicMarginalBundle (PDE.oneDimensionalAxisBox a c) stationary hJ
      (zIndependentCoefficient B) K)
    (hdpos : ∀ v ∈ PDE.oneDimensionalAxisBox a c, 0 < s * (v 0 - e))
    (hdnonneg : ∀ v ∈ closure (PDE.oneDimensionalAxisBox a c), 0 ≤ s * (v 0 - e))
    (v : PDE.Vec 1) (hv : v ∈ movingDomain (PDE.oneDimensionalAxisBox a c) stationary σ)
    (φ : PDE.Vec 1 → ℝ) (hφs : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφJ : tsupport φ ⊆ PDE.oneDimensionalAxisBox a c)
    (hφ : ∀ w, 0 ≤ φ w ∧ φ w ≤ 1) :
    (∫ w, φ w ∂P K hJ (scalarQuery σ τ hστ.le v hv)) ≤
      intervalHeat lam (τ - σ) (s * (v 0 - e)) := by
  let μ := P K hJ (scalarQuery σ τ hστ.le v hv)
  obtain ⟨Q, _hfirst, _hid, _hpos, _hsub, _hcomp, hrepr,
    _hmeas, _hend, _hkc, hsolve⟩ := hpar (fun _ _ _ _ => rfl)
  have hscaled : ∀ κ : ℝ, 0 ≤ κ → κ < 1 →
      κ * (∫ w, φ w ∂μ) ≤ intervalHeat lam (τ - σ) (s * (v 0 - e)) := by
    intro κ hκ0 hκ1
    let F : BoundedBorel (PDE.Vec 1) :=
      ⟨fun w => κ * φ w, measurable_const.mul hφs.continuous.measurable,
        ⟨1, zero_le_one, fun w => by
          rw [abs_of_nonneg (mul_nonneg hκ0 (hφ w).1)]
          exact (mul_le_of_le_one_right hκ0 (hφ w).2).trans hκ1.le⟩⟩
    have hFJ : tsupport (fun w => κ * φ w) ⊆ PDE.oneDimensionalAxisBox a c :=
      tsupport_mul_subset_right.trans hφJ
    obtain ⟨V, hV, heval, _hunique⟩ := hsolve τ F
      ⟨contDiff_const.mul hφs, hφc.mul_left, by
        simpa only [movingDomain_stationary] using hFJ⟩
    have hdom := endpointHeat_terminal_domination hlam hκ0 hκ1 φ hφc hφ
      (fun w hw => hdpos w (hφJ hw))
    have hεbound : ∀ᶠ ε in nhdsWithin 0 (Ioi 0),
        V (σ, v) ≤ intervalHeat lam (τ - σ + ε) (s * (v 0 - e)) := by
      filter_upwards [hdom, self_mem_nhdsWithin] with ε hdomε hε
      have hε0 : 0 < ε := hε
      apply interval_terminal_comparison hac hστ hlam B hB F V
        (endpointHeat lam τ ε s e) hV
      · intro p hp
        exact (contDiffAt_endpointHeat hlam p (by linarith only [hp.1.2, hε0])).continuousAt
          |>.continuousWithinAt
      · intro p hp
        exact (contDiffAt_endpointHeat hlam p (by linarith only [hp.1.2, hε0])).of_le (by simp)
      · intro p hp
        exact endpointHeat_operator_nonpos hlam hs B p (by linarith only [hp.1.2, hε0])
          (hdpos _ hp.2).le (interval_coefficient_lower B hB _ _)
      · intro w hw
        change κ * φ w ≤ intervalHeat lam (τ - τ + ε) (s * (w 0 - e))
        rw [sub_self, zero_add]
        by_cases hwφ : w ∈ tsupport φ
        · exact hdomε w hwφ
        · rw [image_eq_zero_of_notMem_tsupport hwφ, mul_zero]
          exact intervalErf_nonneg (div_nonneg (hdnonneg w hw) (by positivity))
      · intro p hp
        exact intervalErf_nonneg (div_nonneg (hdnonneg _ (frontier_subset_closure hp.2))
          (by positivity))
      · simpa only [movingDomain_stationary] using subset_closure
          (show v ∈ PDE.oneDimensionalAxisBox a c from
            by simpa only [movingDomain_stationary] using hv)
    have hlimit : Tendsto (fun ε => intervalHeat lam (τ - σ + ε) (s * (v 0 - e)))
        (nhdsWithin 0 (Ioi 0)) (𝓝 (intervalHeat lam (τ - σ) (s * (v 0 - e)))) := by
      have hc := (contDiffAt_intervalHeat hlam (τ - σ, s * (v 0 - e))
        (sub_pos.mpr hστ)).continuousAt
      have ht0 : Tendsto (fun ε : ℝ => ε) (nhdsWithin 0 (Ioi 0)) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have ht1 : Tendsto (fun ε : ℝ => τ - σ + ε) (nhdsWithin 0 (Ioi 0))
          (𝓝 (τ - σ)) := by simpa only [add_zero] using ht0.const_add (τ - σ)
      have ht := ht1.prodMk_nhds (tendsto_const_nhds (x := s * (v 0 - e)))
      exact hc.tendsto.comp
        (f := fun ε : ℝ => (τ - σ + ε, s * (v 0 - e))) ht
    have hbound := ge_of_tendsto hlimit hεbound
    have he := heval σ hστ.le ⟨v, hv⟩
    rw [hrepr] at he
    have hi : (∫ w, φ w ∂μ) =
        ∫ w : EvolutionPosition (PDE.oneDimensionalAxisBox a c) stationary τ, φ w.1
          ∂parabolicMarginalKernel K hJ σ τ hστ.le ⟨v, hv⟩ := by
      exact integral_map measurable_subtype_coe.aemeasurable
        hφs.continuous.measurable.aestronglyMeasurable
    rw [hi, ← integral_const_mul]
    exact he ▸ hbound
  have ht : Tendsto (fun κ : ℝ => κ * (∫ w, φ w ∂μ)) (nhdsWithin 1 (Iio 1))
      (𝓝 (∫ w, φ w ∂μ)) := by
    have hκ : Tendsto (fun κ : ℝ => κ) (nhdsWithin 1 (Iio 1)) (𝓝 1) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [one_mul] using hκ.mul_const (∫ w, φ w ∂μ)
  apply le_of_tendsto ht
  filter_upwards [(eventually_gt_nhds (zero_lt_one : (0 : ℝ) < 1)).filter_mono
    nhdsWithin_le_nhds, self_mem_nhdsWithin] with κ hκ0 hκ1
  exact hscaled κ hκ0.le hκ1

end HypoellipticAleksandrov.KineticAleksandrov.Interval

module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.DecayIteration
public import HypoellipticAleksandrov.KineticAleksandrov.Interval.Killing
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.DecayIterationArithmetic

/-! # Exponential iteration and the fixed-length killing block -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay

/-- Full-block contractions imply exponential decay, including durations shorter than a block. -/
theorem interval_exponential_of_blocks {a c T q : ℝ}
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (hcomp : K.HasComposition hJ)
    (hcov : IsTranslationCovariantEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ K)
    (hT : 0 < T) (hq : 0 < q) (hq1 : q ≤ 1) (ξ : PDE.Vec 1)
    (hsteps : ∀ (s : ℝ) (v : PDE.oneDimensionalAxisBox a c),
      TV (intervalFourierKernel K s (s + T) (le_add_of_nonneg_right hT.le) ξ v) ≤ q)
    (σ τ : ℝ) (hστ : σ ≤ τ) (v : PDE.oneDimensionalAxisBox a c) :
    TV (intervalFourierKernel K σ τ hστ ξ v) ≤
      q⁻¹ * Real.exp (-(-Real.log q / T) * (τ - σ)) := by
  let x := (τ - σ) / T
  have hx : 0 ≤ x := div_nonneg (sub_nonneg.mpr hστ) hT.le
  have hk : (Nat.floor x : ℝ) * T ≤ τ - σ := by
    calc (Nat.floor x : ℝ) * T ≤ x * T :=
          mul_le_mul_of_nonneg_right (Nat.floor_le hx) hT.le
      _ = τ - σ := div_mul_cancel₀ _ hT.ne'
  have hstep : ∀ (s : ℝ) (w : PDE.oneDimensionalAxisBox a c),
      totalVariationNorm (intervalFourierKernel K s (s + T)
        (le_add_of_nonneg_right hT.le) ξ w) ≤ ENNReal.ofReal q := by
    intro s w
    have hf : totalVariationNorm (intervalFourierKernel K s (s + T)
        (le_add_of_nonneg_right hT.le) ξ w) ≠ ⊤ :=
      ne_of_lt ((intervalFourierKernel_totalVariation_le_one K _ _ _ ξ w).trans_lt
        ENNReal.one_lt_top)
    rw [← ENNReal.ofReal_toReal hf]
    exact ENNReal.ofReal_le_ofReal (hsteps s w)
  have hn := interval_natural_block_iteration K hJ hcomp hcov ξ hT hq.le hstep
    (Nat.floor x) σ τ hστ hk v
  have hr := ENNReal.toReal_mono (by simp) hn
  simp only [ENNReal.toReal_pow, ENNReal.toReal_ofReal hq.le] at hr
  have he := decay_power_exponential hq hT (τ - σ) 1
  simp only [mul_one] at he
  exact hr.trans ((decay_floor_power hq hq1).trans_eq he)

/-- Over a squared-length block the largest endpoint barrier is length independent. -/
theorem intervalHeat_squared_length {lam ℓ : ℝ} (hlam : 0 < lam) (hℓ : 0 < ℓ) :
    intervalHeat lam (ℓ ^ 2) (ℓ / 2) = intervalErf (1 / (4 * Real.sqrt lam)) := by
  unfold intervalHeat
  rw [Real.sqrt_mul hlam.le, Real.sqrt_sq_eq_abs, abs_of_pos hℓ]
  congr 1
  field_simp
  ring

/-- Every Fourier mode contracts over one squared-length killing block. -/
theorem interval_killing_block
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam m Lb a c : ℝ} (hac : a < c)
    (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1)
    (hs : SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b)
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (hr : RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ
      (zIndependentCoefficient B) b S K)
    (σ : ℝ) (ξ : PDE.Vec 1) (v : PDE.oneDimensionalAxisBox a c)
    (ht : σ ≤ σ + (c - a) ^ 2) :
    TV (intervalFourierKernel K σ (σ + (c - a) ^ 2) ht ξ v) ≤
      intervalErf (1 / (4 * Real.sqrt lam)) := by
  have hlen : 0 < c - a := sub_pos.mpr hac
  have hT : 0 < (c - a) ^ 2 := sq_pos_of_pos hlen
  have hv : v.1 ∈ movingDomain (PDE.oneDimensionalAxisBox a c) stationary σ := by
    simpa only [movingDomain_stationary] using v.2
  have hp := (interval_evolution_clauses hH hLE hac B b hs hJ S K hr).2.1
  have htv := interval_fourier_tv_le_mass hJ K B hp σ (σ + (c - a) ^ 2) ht
    v.1 0 ξ hv _ (intervalFourierKernel_spec K _ _ ht ξ v)
  have hkill := interval_killing hH hLE hac B b hs hJ S K hr σ (σ + (c - a) ^ 2)
    (lt_add_of_pos_right σ hT) v.1 hv
  have he : σ + (c - a) ^ 2 - σ = (c - a) ^ 2 := by ring
  rw [he] at hkill
  have hd : min (v.1 0 - a) (c - v.1 0) ≤ (c - a) / 2 := by
    rcases le_total (v.1 0 - a) (c - v.1 0) with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  have hm := intervalHeat_mono_distance hs.1.1 hT hd
  rw [intervalHeat_squared_length hs.1.1 hlen] at hm
  exact htv.trans (hkill.trans hm)

/-- The killing-block contraction factor belongs to `(0,1)`. -/
theorem interval_killing_factor {lam : ℝ} (hlam : 0 < lam) :
    0 < intervalErf (1 / (4 * Real.sqrt lam)) ∧
      intervalErf (1 / (4 * Real.sqrt lam)) < 1 := by
  have hx : 0 < 1 / (4 * Real.sqrt lam) := by positivity
  refine ⟨?_, intervalErf_lt_one hx.le⟩
  rw [← intervalErf_zero]
  exact strictMono_intervalErf hx

end HypoellipticAleksandrov.KineticAleksandrov.Interval

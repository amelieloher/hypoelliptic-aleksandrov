module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.DecayMass
public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourierEmbedding
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Finite mass of the infinite-horizon interval Green measure

The proved killing estimate is integrated in elapsed Lebesgue time. The resulting
constant is uniform in the initial time, coefficient derivatives and interval position.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay
open HypoellipticAleksandrov.KineticAleksandrov.Green
open scoped ENNReal

/-- The exponentially killed time profile has exact elapsed integral `1/k`. -/
theorem lintegral_interval_killing_profile {k : ℝ} (hk : 0 < k) :
    (∫⁻ t : ElapsedTime ⊤, ENNReal.ofReal (Real.exp (-k * t.1))
      ∂elapsedVolume ⊤) = ENNReal.ofReal k⁻¹ := by
  rw [lintegral_elapsed_top (fun t : ℝ => ENNReal.ofReal (Real.exp (-k * t)))]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos hk) 0)
    (Filter.Eventually.of_forall fun t => (Real.exp_pos _).le)]
  congr 1
  rw [integral_exp_mul_Ioi (neg_neg_of_pos hk) 0]
  simp only [mul_zero, Real.exp_zero, neg_div_neg_eq, one_div]

/-- Infinite-horizon interval Green mass is uniformly finite. -/
theorem interval_green_finite_mass
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam m Lb length : ℝ) (hlam : 0 < lam) (hlength : 0 < length) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a c : ℝ) (_hac : a < c) (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1),
      SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b →
      ∀ (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
      (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
      (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary),
      RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ
        (zIndependentCoefficient B) b S K →
      c - a = length → ∀ (σ : ℝ)
      (μ : Measure (EvolutionState (PDE.oneDimensionalAxisBox a c) stationary σ))
      [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier 1)),
      IsGreenMeasure K σ ⊤ μ Γ → Γ univ ≤ ENNReal.ofReal C * μ univ ∧ Γ univ < ⊤ := by
  obtain ⟨C, k, hC, hk, hmass⟩ :=
    interval_mass_decay hH hLE lam Lam m Lb length hlam hlength
  refine ⟨C * k⁻¹, mul_pos hC (inv_pos.mpr hk), ?_⟩
  intro a c hac B b hs hJ S K hr hlen σ μ _ Γ hΓ
  have hp := (interval_evolution_clauses hH hLE hac B b hs hJ S K hr).2.1
  have hpoint : ∀ (p : EvolutionState (PDE.oneDimensionalAxisBox a c) stationary σ)
      (t : ElapsedTime ⊤), K.master (elapsedQuery σ p t) univ ≤
      ENNReal.ofReal (C * Real.exp (-k * t.1)) := by
    intro p t
    have hv : p.1.1 ∈ PDE.oneDimensionalAxisBox a c := by
      simpa only [evolutionStateSet, mem_prod, movingDomain_stationary] using p.2.1
    have hm := hmass a c hac B b hs hJ S K hr hlen σ (σ + t.1)
      (le_add_of_nonneg_right t.2.1.le) ⟨p.1.1, hv⟩
    have he := interval_parabolic_mass_eq_master hJ K B hp σ (σ + t.1)
      (le_add_of_nonneg_right t.2.1.le) p.1.1 p.1.2 p.2.1
    unfold Measure.real at hm
    rw [he] at hm
    have hf : K.master (elapsedQuery σ p t) univ ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (K.mass_le_one _)
    rw [← ENNReal.ofReal_toReal hf]
    apply ENNReal.ofReal_le_ofReal
    simpa only [movingQuery, elapsedQuery, add_sub_cancel_left] using hm
  have hbound : Γ univ ≤ ENNReal.ofReal (C * k⁻¹) * μ univ := by
    rw [← lintegral_one, hΓ _ measurable_const]
    simp only [lintegral_one]
    calc
      _ ≤ ∫⁻ _p, ∫⁻ t : ElapsedTime ⊤,
          ENNReal.ofReal (C * Real.exp (-k * t.1)) ∂elapsedVolume ⊤ ∂μ :=
        lintegral_mono fun p => lintegral_mono fun t => hpoint p t
      _ = _ := by
        simp_rw [ENNReal.ofReal_mul hC.le]
        rw [lintegral_const_mul _ (by fun_prop), lintegral_interval_killing_profile hk,
          lintegral_const]
  exact ⟨hbound, hbound.trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ univ))⟩

end HypoellipticAleksandrov.KineticAleksandrov.Interval

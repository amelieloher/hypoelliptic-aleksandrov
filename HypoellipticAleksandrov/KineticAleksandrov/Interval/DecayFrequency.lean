module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.BlockScaling
public import HypoellipticAleksandrov.KineticAleksandrov.Interval.DecayBlocks

/-! # Frequency decay uniformly over interval location and length -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay

/-- The frequency decay constants depend only on the structural source bounds. -/
theorem interval_frequency_decay
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam m Lb : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hm : 0 < m) (hmLb : m ≤ Lb) :
    ∃ C k : ℝ, 0 < C ∧ 0 < k ∧
      ∀ (a c : ℝ) (_hac : a < c) (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1),
      SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b →
      ∀ (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
      (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
      (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary),
      RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ
        (zIndependentCoefficient B) b S K →
      ∀ (σ τ : ℝ) (hστ : σ ≤ τ) (ξ : PDE.Vec 1)
      (v : PDE.oneDimensionalAxisBox a c),
      TV (intervalFourierKernel K σ τ hστ ξ v) ≤
        C * Real.exp (-k * (τ - σ) * PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ)) := by
  obtain ⟨L, δ, hL, hδ, hδ1, hsteps⟩ := interval_frequency_blocks
    hH hLE lam Lam m Lb hlam hlamLam hm hmLb
  have hq : 0 < 1 - δ := sub_pos.mpr hδ1
  obtain ⟨hC, hk⟩ := decay_constants hδ hδ1 hL
  refine ⟨(1 - δ)⁻¹, -Real.log (1 - δ) / L, zero_lt_one.trans_le hC, hk, ?_⟩
  intro a c hac B b hs hJ S K hr σ τ hστ ξ v
  by_cases hξ : ξ = 0
  · subst ξ
    have htv := intervalFourierKernel_totalVariation_le_one K σ τ hστ 0 v
    have hr := ENNReal.toReal_mono ENNReal.one_ne_top htv
    simp only [ENNReal.toReal_one] at hr
    simpa only [PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot, Pi.zero_apply,
      zero_mul, Finset.sum_const_zero, Real.sqrt_zero,
      Real.zero_rpow (by norm_num : (2 / 3 : ℝ) ≠ 0), mul_zero,
      Real.exp_zero, mul_one] using hr.trans hC
  · have hN := frequency_norm_pos hξ
    let N := PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ)
    have hNp : 0 < N := Real.rpow_pos_of_pos hN _
    let T := L * PDE.vecEuclideanNorm ξ ^ (-(2 / 3 : ℝ))
    have hTdef : T = L / N := by
      dsimp [T, N]
      rw [Real.rpow_neg hN.le]
      rfl
    have hT : 0 < T := by rw [hTdef]; exact div_pos hL hNp
    have hc := (interval_evolution_clauses hH hLE hac B b hs hJ S K hr).2.2
    have hb := interval_exponential_of_blocks K hJ hr.2.2.2 hc hT hq
      (by linarith only [hδ] : 1 - δ ≤ 1) ξ
      (fun s w => hsteps a c hac B b hs hJ S K hr ξ hξ s w
        (le_add_of_nonneg_right hT.le)) σ τ hστ v
    have he : -(-Real.log (1 - δ) / T) * (τ - σ) =
        -(-Real.log (1 - δ) / L) * (τ - σ) * N := by
      rw [hTdef]
      field_simp
    rw [he] at hb
    exact hb

end HypoellipticAleksandrov.KineticAleksandrov.Interval

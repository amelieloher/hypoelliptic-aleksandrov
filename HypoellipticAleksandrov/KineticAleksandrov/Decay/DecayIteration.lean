module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.FrequencyBlocks
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.DecayIterationKernel
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.DecayIterationArithmetic

/-! # Source frequency iteration, including the short-interval remainder -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal

/-- The frequency-floor estimate follows from the actual scaled blocks and Fourier composition. -/
theorem fourier_floor_iteration_of_blocks {d : ℕ}
    (K : MovingFiberKernel (wholeSpace d) stationary)
    (hcomp : K.HasComposition MeasurableSet.univ)
    (hcov : IsTranslationCovariantEvolution (wholeSpace d) stationary MeasurableSet.univ K)
    {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ1 : δ < 1)
    (ξ : PDE.Vec d) (hξ : ξ ≠ 0)
    (hsteps : ∀ (s : ℝ) (v : PDE.Vec d)
      (q : EvolutionQuery (wholeSpace d) stationary),
      q.1 = (s, s + L * PDE.vecEuclideanNorm ξ ^ (-(2 / 3 : ℝ)), v, 0) →
      ∀ ν : ComplexMeasure (PDE.Vec d), IsFourierProjection K q ξ ν → TV ν ≤ 1 - δ)
    (σ τ : ℝ) (hστ : σ < τ) (v : PDE.Vec d)
    (q : EvolutionQuery (wholeSpace d) stationary) (hq : q.1 = (σ, τ, v, 0))
    (ν : ComplexMeasure (PDE.Vec d)) (hν : IsFourierProjection K q ξ ν) :
    let x := (τ - σ) * PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ) / L
    let k := Nat.floor x
    TV ν ≤ (1 - δ) ^ k ∧
      (1 - δ) ^ k ≤ (1 - δ) ^ (x - 1) ∧
      (1 - δ) ^ (x - 1) = (1 - δ)⁻¹ *
        Real.exp (-(-Real.log (1 - δ) / L) * (τ - σ) *
          PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ)) := by
  dsimp only
  have hN : 0 < PDE.vecEuclideanNorm ξ := frequency_norm_pos hξ
  let N := PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ)
  have hNp : 0 < N := Real.rpow_pos_of_pos hN _
  let T := L * PDE.vecEuclideanNorm ξ ^ (-(2 / 3 : ℝ))
  have hTdef : T = L / N := by
    dsimp [T, N]
    rw [Real.rpow_neg hN.le]
    rfl
  have hT : 0 < T := by rw [hTdef]; exact div_pos hL hNp
  have ha : 0 < 1 - δ := sub_pos.mpr hδ1
  let x := (τ - σ) * N / L
  have hx : 0 ≤ x := (div_pos (mul_pos (sub_pos.mpr hστ) hNp) hL).le
  have hxT : x * T = τ - σ := by
    rw [hTdef]
    dsimp [x]
    field_simp
  have hk : (Nat.floor x : ℝ) * T ≤ τ - σ := by
    rw [← hxT]
    exact mul_le_mul_of_nonneg_right (Nat.floor_le hx) hT.le
  have hstep : ∀ (s : ℝ) (w : PDE.Vec d),
      totalVariationNorm (fourierKernel K s (s + T) (le_add_of_nonneg_right hT.le) ξ w) ≤
        ENNReal.ofReal (1 - δ) := by
    intro s w
    have hst : s ≤ s + T := le_add_of_nonneg_right hT.le
    let qs := wholeSpaceQuery s (s + T) hst w 0
    have hs := hsteps s w qs rfl _ (fourierKernel_spec K s (s + T) hst ξ w)
    have hf : totalVariationNorm (fourierKernel K s (s + T) hst ξ w) ≠ ⊤ :=
      ne_of_lt ((fourierKernel_totalVariation_le_one K s (s + T) hst ξ w).trans_lt
        ENNReal.one_lt_top)
    calc
      _ = ENNReal.ofReal (TV (fourierKernel K s (s + T) hst ξ w)) :=
        (ENNReal.ofReal_toReal hf).symm
      _ ≤ ENNReal.ofReal (1 - δ) := ENNReal.ofReal_le_ofReal hs
  have hn := fourier_natural_block_iteration K hcomp hcov ξ hT ha.le hstep
    (Nat.floor x) σ τ hστ.le hk v
  have hr := ENNReal.toReal_mono (by simp) hn
  simp only [ENNReal.toReal_pow, ENNReal.toReal_ofReal ha.le] at hr
  rw [iteration_projection_eq K σ τ hστ.le v ξ q hq ν hν]
  exact ⟨hr, decay_floor_power ha (by linarith only [hδ]),
    decay_power_exponential ha hL (τ - σ) N⟩

/-- The full frequency iteration, conditional on the unit-block estimate and the terminal evolution
statement. -/
theorem fourier_decay_frequency_iteration_of_unitBlock (d : ℕ) (hd : 1 ≤ d)
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hEvol : IterationEvolutionStatement)
    (hblock : UnitBlockStatementW d hd lam Lam 1 1 hlam hlamLam zero_lt_one le_rfl) :
    ∃ L δ : ℝ, 0 < L ∧ 0 < δ ∧ δ < 1 ∧
      ∀ (B : CoefficientField d), IsSectionTwoCoefficient lam Lam B →
      ∀ (S : TerminalOperatorFamily univ stationary) (K : MovingFiberKernel univ stationary),
        RealizesTerminalEvolution univ stationary MeasurableSet.univ
          (zIndependentCoefficient B) id S K →
      ∀ (ξ : PDE.Vec d), ξ ≠ 0 → ∀ (σ τ : ℝ), σ < τ →
      ∀ (v : PDE.Vec d) (q : EvolutionQuery univ stationary), q.1 = (σ, τ, v, 0) →
      ∀ (ν : ComplexMeasure (PDE.Vec d)), IsFourierProjection K q ξ ν →
        let x := (τ - σ) * PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ) / L
        let k := Nat.floor x
        TV ν ≤ (1 - δ) ^ k ∧ (1 - δ) ^ k ≤ (1 - δ) ^ (x - 1) ∧
          (1 - δ) ^ (x - 1) = (1 - δ)⁻¹ *
            Real.exp (-(-Real.log (1 - δ) / L) * (τ - σ) *
              PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ)) := by
  obtain ⟨L, δ, hL, hδ, hδ1, hsteps⟩ :=
    nonzero_frequency_blocks_of_unitBlock d hd lam Lam hlam hlamLam hEvol hblock
  refine ⟨L, δ, hL, hδ, hδ1, ?_⟩
  intro B hB S K hreal ξ hξ σ τ hστ v q hq ν hν
  have hcov := (iteration_evolution_clauses hEvol hd hlam hlamLam B hB S K hreal).2.2
  exact fourier_floor_iteration_of_blocks K hreal.2.2.2 hcov hL hδ hδ1 ξ hξ
    (hsteps B hB S K hreal ξ hξ) σ τ hστ v q hq ν hν

end HypoellipticAleksandrov.KineticAleksandrov.Decay

module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.Slab
public import HypoellipticAleksandrov.KineticAleksandrov.Interval.GreenNorm

/-! # The interval infinite-horizon Green theorem

Killed slab densities are glued and logarithmically averaged over all positive times.
Constants depend only on the structural parameters, interval length and exponent.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Decay
open HypoellipticAleksandrov.KineticAleksandrov.Green
open scoped ENNReal NNReal

/-- Uniform infinite-horizon interval density and norm, obtained from killed slabs. -/
theorem interval_green_infinite_norm
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam m Lb length : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hm : 0 < m) (hmLb : m ≤ Lb) (hlength : 0 < length)
    (q : ℝ) (hq : 1 < q) (hq2 : q < (3 : ℝ) / 2) :
    ∃ C k : ℝ, 0 < C ∧ 0 < k ∧
    ∀ (a c : ℝ) (_hac : a < c) (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1),
    SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b →
    ∀ (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
      (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
      (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary),
    RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ
      (zIndependentCoefficient B) b S K →
    c - a = length → ∀ (σ : ℝ),
    ∀ (μ : Measure (EvolutionState (PDE.oneDimensionalAxisBox a c) stationary σ))
    [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier 1)), IsGreenMeasure K σ ⊤ μ Γ →
    ∃ G : GreenCarrier 1 → ℝ≥0∞, Measurable G ∧
      Γ = (greenLebesgue 1).withDensity G ∧
      eLpNorm G (ENNReal.ofReal q) (greenLebesgue 1) ≤ ENNReal.ofReal C * μ univ := by
  have hq' : q < 2 := by linarith
  have hq0 : 0 < q := by linarith
  have hδ : 0 < 3 - 2 * q := by linarith
  obtain ⟨A, k, _hA, hk, hslab⟩ := interval_slab_density hH hLE
    lam Lam m Lb length hlam hlamLam hm hmLb hlength q hq hq'
  let N := killedGreenConstant A (3 - 2 * q) k q
  have hN : N ≠ ⊤ := killedGreenConstant_ne_top hδ hk hq0
  refine ⟨N.toReal + 1, k, by positivity, hk, ?_⟩
  intro a c hac B b hs hJ S K hr hlen σ μ _ Γ hΓ
  have hloc : ∀ T : ℝ, ∃ G : GreenCarrier 1 → ℝ≥0∞, 0 < T →
      Measurable G ∧
      Γ.restrict (slabSet T) = ((greenLebesgue 1).restrict (slabSet T)).withDensity G ∧
      ∫⁻ p in slabSet T, G p ^ q ∂greenLebesgue 1 ≤
        ENNReal.ofReal A * μ univ ^ q *
          ENNReal.ofReal (T ^ (3 - 2 * q) * Real.exp (-k * T)) := by
    intro T
    by_cases hT : 0 < T
    · obtain ⟨G, hG⟩ := hslab a c hac B b hs hJ S K hr hlen σ T hT μ Γ hΓ
      exact ⟨G, fun _ => hG⟩
    · exact ⟨0, fun h => absurd h hT⟩
  choose Gl hGl using hloc
  obtain ⟨G, hGm, hGE, hGae⟩ := exists_global_density K σ μ Γ hΓ Gl
    (fun T hT => (hGl T hT).1) (fun T hT => (hGl T hT).2.1)
  refine ⟨G, hGm, hGE, ?_⟩
  have hbd := killed_green_norm_bound G hGm A (3 - 2 * q) k q (μ univ) hq0 (by
    intro T hT
    calc ∫⁻ p in slabSet T, G p ^ q ∂greenLebesgue 1
        = ∫⁻ p in slabSet T, Gl T p ^ q ∂greenLebesgue 1 := by
          refine lintegral_congr_ae ?_
          filter_upwards [hGae T hT] with p hp
          rw [hp]
      _ ≤ _ := (hGl T hT).2.2)
  apply hbd.trans
  apply mul_le_mul' ?_ le_rfl
  calc N = ENNReal.ofReal N.toReal := (ENNReal.ofReal_toReal hN).symm
    _ ≤ ENNReal.ofReal (N.toReal + 1) := ENNReal.ofReal_le_ofReal (by linarith)

end HypoellipticAleksandrov.KineticAleksandrov.Interval

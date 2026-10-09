module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.GreenInfinite
public import HypoellipticAleksandrov.KineticAleksandrov.Interval.GreenMass

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

/-- The interval Green theorem: uniform density norm and finite infinite-horizon mass. -/
theorem interval_green_density
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam m Lb length : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hm : 0 < m) (hmLb : m ≤ Lb) (hlength : 0 < length)
    (q : ℝ) (hq : 1 < q) (hq2 : q < (3 : ℝ) / 2) :
    ∃ C : ℝ, 0 < C ∧
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
      eLpNorm G (ENNReal.ofReal q) (greenLebesgue 1) ≤ ENNReal.ofReal C * μ univ ∧
      Γ univ < ⊤ := by
  obtain ⟨C, k, hC, _hk, hnorm⟩ := interval_green_infinite_norm hH hLE
    lam Lam m Lb length hlam hlamLam hm hmLb hlength q hq hq2
  obtain ⟨_Cm, _hCm, hmass⟩ := interval_green_finite_mass hH hLE
    lam Lam m Lb length hlam hlength
  refine ⟨C, hC, ?_⟩
  intro a c hac B b hs hJ S K hr hlen σ μ _ Γ hΓ
  obtain ⟨G, hGm, hGE, hGn⟩ := hnorm a c hac B b hs hJ S K hr hlen σ μ Γ hΓ
  exact ⟨G, hGm, hGE, hGn, (hmass a c hac B b hs hJ S K hr hlen σ μ Γ hΓ).2⟩

end HypoellipticAleksandrov.KineticAleksandrov.Interval

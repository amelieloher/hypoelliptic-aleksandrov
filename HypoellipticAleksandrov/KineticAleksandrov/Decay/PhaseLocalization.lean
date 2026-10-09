module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.SmoothTestOrder
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.PhaseExclusion
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-!
# Closed phase strips from vanishing forbidden-region tests

The two strictly forbidden open sets have zero mass. Their complement is the
source's closed phase strip, interpreted as an almost-everywhere measure statement.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open Set MeasureTheory
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

/-- Two signs of vanishing smooth tests place a finite measure in the closed phase strip. -/
theorem ae_phase_strip_of_forbidden_tests {d : ℕ}
    {μ : Measure (EvolutionAmbientState d)} [IsFiniteMeasure μ]
    {D : Set (EvolutionAmbientState d)} (hD : IsOpen D) (hμ : μ Dᶜ = 0)
    {q : EvolutionAmbientState d → ℝ} (hq : Continuous q) (c : ℝ)
    (htest : ∀ sgn : ℝ, sgn = 1 ∨ sgn = -1 →
      ∀ φ : EvolutionAmbientState d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
        HasCompactSupport φ → tsupport φ ⊆ {x | 0 < sgn * q x - c} ∩ D →
        (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) → ∫ x, φ x ∂μ = 0) :
    ∀ᵐ x ∂μ, |q x| ≤ c := by
  have hzero : ∀ sgn : ℝ, sgn = 1 ∨ sgn = -1 → μ {x | 0 < sgn * q x - c} = 0 := by
    intro sgn hs
    apply measure_eq_zero_of_smooth_integral_eq_zero_of_support
      (isOpen_lt continuous_const ((continuous_const.mul hq).sub continuous_const)) hD hμ
    exact htest sgn hs
  apply ae_iff.mpr
  apply measure_mono_null (fun x hx => ?_)
    (measure_union_null (hzero 1 (Or.inl rfl)) (hzero (-1) (Or.inr rfl)))
  change ¬ |q x| ≤ c at hx
  change 0 < 1 * q x - c ∨ 0 < -1 * q x - c
  by_cases hp : 0 ≤ q x
  · rw [abs_of_nonneg hp] at hx
    left
    linarith
  · rw [abs_of_neg (lt_of_not_ge hp)] at hx
    right
    linarith

/-- The supplied moving kernel is concentrated in the source closed phase strip. -/
theorem moving_ball_phase_localization (d : ℕ) (_hd : 1 ≤ d)
    (lam Lam : ℝ) (_hlam : 0 < lam) (_hlamLam : lam ≤ Lam)
    (m Lb : ℝ) (D : Set (PDE.Vec d)) (B : CoefficientField d)
    (b : PDE.Vec d → PDE.Vec d) (hsetting : SourceSetting lam Lam m Lb D B b)
    (σ τ H ρ : ℝ) (γ : ℝ → PDE.Vec d) (hστ0 : σ ≤ τ) (hρ : 0 < ρ)
    (hγ : PiecewiseC1On γ σ τ) (_hspeed : HasCurveSpeedOn H γ σ τ)
    (_hfit : ∀ r ∈ Icc σ τ, PDE.euclideanBall (γ r) ρ ⊆ D)
    (S : TerminalOperatorFamily (PDE.euclideanBall 0 ρ) (clippedCurve γ σ τ))
    (K : MovingFiberKernel (PDE.euclideanBall 0 ρ) (clippedCurve γ σ τ))
    (hreal : RealizesTerminalEvolution (PDE.euclideanBall 0 ρ) (clippedCurve γ σ τ)
      (PDE.isOpen_euclideanBall 0 ρ).measurableSet (zIndependentCoefficient B) b S K)
    (_hpar : HasParabolicMarginalBundle (PDE.euclideanBall 0 ρ) (clippedCurve γ σ τ)
      (PDE.isOpen_euclideanBall 0 ρ).measurableSet (zIndependentCoefficient B) K)
    (ξ z0 v : PDE.Vec d) (hξ : PDE.vecNormSq ξ = 1)
    (hστ : σ ≤ τ)
    (hv : v ∈ movingDomain (PDE.euclideanBall 0 ρ) (clippedCurve γ σ τ) σ)
    : ∀ᵐ x ∂K.master (movingQuery σ τ hστ v z0 hv),
      |phaseCoordinate ξ z0 x - phaseCenter ξ b γ σ τ| ≤ Lb * ρ * (τ - σ) := by
  let μ := K.master (movingQuery σ τ hστ v z0 hv)
  have hfinite : IsFiniteMeasure μ := ⟨(K.mass_le_one _).trans_lt ENNReal.one_lt_top⟩
  let U := evolutionStateSet (PDE.euclideanBall 0 ρ) (clippedCurve γ σ τ) τ
  have hU : IsOpen U := (isOpen_movingDomain (PDE.isOpen_euclideanBall 0 ρ) τ).prod
    isOpen_univ
  have hμ : μ Uᶜ = 0 := by
    have hr : μ.restrict U = μ := K.terminal_support _
    calc
      μ Uᶜ = (μ.restrict U) Uᶜ := by rw [hr]
      _ = μ (Uᶜ ∩ U) := Measure.restrict_apply hU.measurableSet.compl
      _ = 0 := by simp only [compl_inter_self, measure_empty]
  have hq : Continuous (fun x : EvolutionAmbientState d =>
      phaseCoordinate ξ z0 x - phaseCenter ξ b γ σ τ) := by
    unfold phaseCoordinate PDE.vecDot
    simp only [Pi.sub_apply]
    fun_prop
  apply ae_phase_strip_of_forbidden_tests hU hμ hq (Lb * ρ * (τ - σ))
  intro sgn hsgn φ hφ hc hs hbound
  let φB := smoothTestDatum φ hφ hbound
  have hd : IsSmoothCompactTerminalDatum (PDE.euclideanBall 0 ρ)
      (clippedCurve γ σ τ) τ φB := ⟨hφ, hc, fun x hx => (hs hx).2⟩
  exact phase_forbidden_test_integral_eq_zero d _hd lam Lam _hlam _hlamLam
    m Lb D B b hsetting σ τ H ρ γ hστ0 hρ hγ _hspeed _hfit S K hreal _hpar
    ξ z0 v hξ hστ hv sgn hsgn φB hd hbound (fun x hx => (hs hx).1)

end HypoellipticAleksandrov.KineticAleksandrov.Decay

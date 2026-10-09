module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeTests
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Gelfand weak time derivatives

This module defines the quotient-safe scalar testing relation for a reverse-time
Bochner `L²(V)` curve and its `L²(V*)` weak derivative.  It contains only the
basic linear algebra of that relation; endpoint, uniqueness, and smooth-curve
results belong to later modules.
-/

@[expose] public section

open Function MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

local instance instReverseTimeL2VStarModule
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) :
    Module ℝ (ReverseTimeL2VStar hΩ T) :=
  MeasureTheory.Lp.instModule

private noncomputable def weakDerivativeLeft
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (v : H10HilbertGraph hΩ) (eta : ReverseTimeScalarTest T)
    (u : ReverseTimeL2V hΩ T) : ℝ → ℝ :=
  fun tau => inner ℝ (valueCLM hΩ v) (reverseTimeValueCLM hΩ T u tau) * eta.deriv tau

private noncomputable def weakDerivativeRight
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (v : H10HilbertGraph hΩ) (eta : ReverseTimeScalarTest T)
    (g : ReverseTimeL2VStar hΩ T) : ℝ → ℝ :=
  fun tau => (g tau) v * eta tau

private theorem weakDerivativeLeft_add_ae
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (v : H10HilbertGraph hΩ) (eta : ReverseTimeScalarTest T)
    (u₁ u₂ : ReverseTimeL2V hΩ T) :
    weakDerivativeLeft hΩ T v eta (u₁ + u₂) =ᵐ[reverseTimeVolume T]
      weakDerivativeLeft hΩ T v eta u₁ + weakDerivativeLeft hΩ T v eta u₂ := by
  have hmap : reverseTimeValueCLM hΩ T (u₁ + u₂) =
      reverseTimeValueCLM hΩ T u₁ + reverseTimeValueCLM hΩ T u₂ :=
    (reverseTimeValueCLM hΩ T).map_add u₁ u₂
  filter_upwards [Lp.coeFn_add (reverseTimeValueCLM hΩ T u₁)
    (reverseTimeValueCLM hΩ T u₂)] with tau ht
  dsimp only [weakDerivativeLeft]
  rw [hmap, ht]
  change inner ℝ (valueCLM hΩ v)
    (reverseTimeValueCLM hΩ T u₁ tau + reverseTimeValueCLM hΩ T u₂ tau) * eta.deriv tau =
    inner ℝ (valueCLM hΩ v) (reverseTimeValueCLM hΩ T u₁ tau) * eta.deriv tau +
      inner ℝ (valueCLM hΩ v) (reverseTimeValueCLM hΩ T u₂ tau) * eta.deriv tau
  simp only [inner_add_right, add_mul]

private theorem weakDerivativeRight_add_ae
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (v : H10HilbertGraph hΩ) (eta : ReverseTimeScalarTest T)
    (g₁ g₂ : ReverseTimeL2VStar hΩ T) :
    weakDerivativeRight hΩ T v eta (g₁ + g₂) =ᵐ[reverseTimeVolume T]
      weakDerivativeRight hΩ T v eta g₁ + weakDerivativeRight hΩ T v eta g₂ := by
  filter_upwards [Lp.coeFn_add g₁ g₂] with tau ht
  dsimp only [weakDerivativeRight]
  rw [ht]
  change ((g₁ tau + g₂ tau) v) * eta tau = (g₁ tau) v * eta tau + (g₂ tau) v * eta tau
  simp only [ContinuousLinearMap.add_apply, add_mul]

private theorem weakDerivativeLeft_smul_ae
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (v : H10HilbertGraph hΩ) (eta : ReverseTimeScalarTest T)
    (u : ReverseTimeL2V hΩ T) (a : ℝ) :
    weakDerivativeLeft hΩ T v eta (a • u) =ᵐ[reverseTimeVolume T]
      a • weakDerivativeLeft hΩ T v eta u := by
  have hmap : reverseTimeValueCLM hΩ T (a • u) = a • reverseTimeValueCLM hΩ T u :=
    (reverseTimeValueCLM hΩ T).map_smul a u
  filter_upwards [Lp.coeFn_smul a (reverseTimeValueCLM hΩ T u)] with tau ht
  have ht' : ((a • reverseTimeValueCLM hΩ T u : ReverseTimeL2H hΩ T) tau) =
      a • reverseTimeValueCLM hΩ T u tau := by
    simpa only [Pi.smul_apply] using ht
  dsimp only [weakDerivativeLeft]
  rw [hmap, ht']
  simp only [weakDerivativeLeft, Pi.smul_apply, inner_smul_right, smul_eq_mul, mul_assoc]

private theorem weakDerivativeRight_smul_ae
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ)
    (v : H10HilbertGraph hΩ) (eta : ReverseTimeScalarTest T)
    (g : ReverseTimeL2VStar hΩ T) (a : ℝ) :
    weakDerivativeRight hΩ T v eta (a • g : ReverseTimeL2VStar hΩ T) =ᵐ[reverseTimeVolume T]
      a • weakDerivativeRight hΩ T v eta g := by
  filter_upwards [Lp.coeFn_smul (𝕜 := ℝ) a g] with tau ht
  dsimp only [weakDerivativeRight]
  simpa only [weakDerivativeRight, Pi.smul_apply, smul_apply, smul_eq_mul, mul_assoc] using
    congrArg (fun q : H10HilbertGraphDual hΩ => q v * eta tau) ht

private theorem integral_neg_add
    {α : Type _} [MeasurableSpace α] (μ : Measure α)
    {f₁ f₂ f g₁ g₂ g : α → ℝ}
    (hf₁ : Integrable f₁ μ) (hf₂ : Integrable f₂ μ)
    (hg₁ : Integrable g₁ μ) (hg₂ : Integrable g₂ μ)
    (hleft : f =ᵐ[μ] f₁ + f₂) (hright : g =ᵐ[μ] g₁ + g₂)
    (hidentity₁ : (∫ x, f₁ x ∂μ) = -(∫ x, g₁ x ∂μ))
    (hidentity₂ : (∫ x, f₂ x ∂μ) = -(∫ x, g₂ x ∂μ)) :
    (∫ x, f x ∂μ) = -(∫ x, g x ∂μ) := by
  calc
    (∫ x, f x ∂μ) = ∫ x, f₁ x + f₂ x ∂μ := integral_congr_ae hleft
    _ = (∫ x, f₁ x ∂μ) + ∫ x, f₂ x ∂μ := integral_add hf₁ hf₂
    _ = -(∫ x, g₁ x ∂μ) + -(∫ x, g₂ x ∂μ) := by rw [hidentity₁, hidentity₂]
    _ = -((∫ x, g₁ x ∂μ) + ∫ x, g₂ x ∂μ) := by ring
    _ = -(∫ x, g₁ x + g₂ x ∂μ) := by rw [integral_add hg₁ hg₂]
    _ = -(∫ x, g x ∂μ) := congrArg Neg.neg (integral_congr_ae hright).symm

private theorem integral_neg_smul
    {α : Type _} [MeasurableSpace α] (μ : Measure α)
    {f fScaled g gScaled : α → ℝ} (a : ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hleft : fScaled =ᵐ[μ] a • f) (hright : gScaled =ᵐ[μ] a • g)
    (hidentity : (∫ x, f x ∂μ) = -(∫ x, g x ∂μ)) :
    (∫ x, fScaled x ∂μ) = -(∫ x, gScaled x ∂μ) := by
  calc
    (∫ x, fScaled x ∂μ) = ∫ x, a • f x ∂μ := integral_congr_ae hleft
    _ = a • ∫ x, f x ∂μ := hf.integral_smul a
    _ = -(a • ∫ x, g x ∂μ) := by rw [hidentity, smul_neg]
    _ = -(∫ x, a • g x ∂μ) := by rw [hg.integral_smul a]
    _ = -(∫ x, gScaled x ∂μ) := congrArg Neg.neg (integral_congr_ae hright).symm

/-- The Gelfand weak reverse-time derivative identity against compactly
supported scalar tests.  The derivative is the ordinary positive-time
derivative of the test, so the distributional sign appears on the right. -/
def HasGelfandWeakTimeDerivative
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) : Prop :=
  ∀ v : H10HilbertGraph hΩ, ∀ eta : ReverseTimeScalarTest T,
    Integrable
      (fun tau =>
        inner ℝ (valueCLM hΩ v) (reverseTimeValueCLM hΩ T u tau) * eta.deriv tau)
      (reverseTimeVolume T) ∧
    Integrable
      (fun tau => (g tau) v * eta tau)
      (reverseTimeVolume T) ∧
    (∫ tau,
      inner ℝ (valueCLM hΩ v) (reverseTimeValueCLM hΩ T u tau) * eta.deriv tau
      ∂reverseTimeVolume T) =
      -(∫ tau, (g tau) v * eta tau ∂reverseTimeVolume T)

/-- The left-hand scalar pairing in the Gelfand weak derivative identity is
integrable by the Bochner `L²` carrier and Hölder's inequality. -/
theorem integrable_reverseTimeWeakDerivative_left
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ)
    (u : ReverseTimeL2V hΩ T)
    (v : H10HilbertGraph hΩ) (eta : ReverseTimeScalarTest T) :
    Integrable
      (fun tau =>
        inner ℝ (valueCLM hΩ v) (reverseTimeValueCLM hΩ T u tau) * eta.deriv tau)
      (reverseTimeVolume T) := by
  have hpair : MemLp
      (fun tau => inner ℝ (valueCLM hΩ v) (reverseTimeValueCLM hΩ T u tau))
      (2 : ℝ≥0∞) (reverseTimeVolume T) :=
    (MeasureTheory.Lp.memLp (reverseTimeValueCLM hΩ T u)).continuousLinearMap_comp
      (innerSL ℝ (valueCLM hΩ v))
  simpa only [Pi.mul_def] using hpair.integrable_mul (eta.memLp_deriv 2)

/-- The right-hand dual pairing in the Gelfand weak derivative identity is
integrable by the Bochner `L²` carrier and Hölder's inequality. -/
theorem integrable_reverseTimeWeakDerivative_right
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ)
    (g : ReverseTimeL2VStar hΩ T)
    (v : H10HilbertGraph hΩ) (eta : ReverseTimeScalarTest T) :
    Integrable
      (fun tau => (g tau) v * eta tau)
      (reverseTimeVolume T) := by
  have hpair : MemLp (fun tau => (g tau) v) (2 : ℝ≥0∞) (reverseTimeVolume T) :=
    (MeasureTheory.Lp.memLp g).continuousLinearMap_comp (ContinuousLinearMap.apply ℝ ℝ v)
  simpa only [Pi.mul_def] using hpair.integrable_mul (eta.memLp 2)

/-- The zero reverse-time curve has zero Gelfand weak time derivative. -/
theorem hasGelfandWeakTimeDerivative_zero
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T) :
    HasGelfandWeakTimeDerivative hΩ T hT 0 0 := by
  intro v eta
  refine ⟨integrable_reverseTimeWeakDerivative_left hΩ T 0 v eta,
    integrable_reverseTimeWeakDerivative_right hΩ T 0 v eta, ?_⟩
  have hleft :
      (fun tau =>
        inner ℝ (valueCLM hΩ v) (reverseTimeValueCLM hΩ T (0 : ReverseTimeL2V hΩ T) tau) *
          eta.deriv tau) =ᵐ[reverseTimeVolume T] 0 := by
    filter_upwards [Lp.coeFn_zero
      (PDE.ScalarLp Ω (2 : ℝ≥0∞)) (2 : ℝ≥0∞) (reverseTimeVolume T)] with tau ht
    rw [ContinuousLinearMap.map_zero, ht]
    simp
  have hright :
      (fun tau => ((0 : ReverseTimeL2VStar hΩ T) tau) v * eta tau) =ᵐ[reverseTimeVolume T] 0 := by
    filter_upwards [Lp.coeFn_zero
      (H10HilbertGraphDual hΩ) (2 : ℝ≥0∞) (reverseTimeVolume T)] with tau ht
    rw [ht]
    simp
  rw [integral_congr_ae hleft, integral_congr_ae hright]
  simp

/-- Gelfand weak time derivatives are closed under addition. -/
theorem HasGelfandWeakTimeDerivative.add
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    {hΩ : IsOpen Ω} {T : ℝ} {hT : 0 < T}
    {u₁ u₂ : ReverseTimeL2V hΩ T} {g₁ g₂ : ReverseTimeL2VStar hΩ T}
    (h₁ : HasGelfandWeakTimeDerivative hΩ T hT u₁ g₁)
    (h₂ : HasGelfandWeakTimeDerivative hΩ T hT u₂ g₂) :
    HasGelfandWeakTimeDerivative hΩ T hT (u₁ + u₂) (g₁ + g₂) := by
  intro v eta
  obtain ⟨hleft₁, hright₁, hidentity₁⟩ := h₁ v eta
  obtain ⟨hleft₂, hright₂, hidentity₂⟩ := h₂ v eta
  change Integrable (weakDerivativeLeft hΩ T v eta u₁) (reverseTimeVolume T) at hleft₁
  change Integrable (weakDerivativeRight hΩ T v eta g₁) (reverseTimeVolume T) at hright₁
  change (∫ tau, weakDerivativeLeft hΩ T v eta u₁ tau ∂reverseTimeVolume T) =
    -(∫ tau, weakDerivativeRight hΩ T v eta g₁ tau ∂reverseTimeVolume T) at hidentity₁
  change Integrable (weakDerivativeLeft hΩ T v eta u₂) (reverseTimeVolume T) at hleft₂
  change Integrable (weakDerivativeRight hΩ T v eta g₂) (reverseTimeVolume T) at hright₂
  change (∫ tau, weakDerivativeLeft hΩ T v eta u₂ tau ∂reverseTimeVolume T) =
    -(∫ tau, weakDerivativeRight hΩ T v eta g₂ tau ∂reverseTimeVolume T) at hidentity₂
  change Integrable (weakDerivativeLeft hΩ T v eta (u₁ + u₂)) (reverseTimeVolume T) ∧
    Integrable (weakDerivativeRight hΩ T v eta (g₁ + g₂)) (reverseTimeVolume T) ∧
    (∫ tau, weakDerivativeLeft hΩ T v eta (u₁ + u₂) tau ∂reverseTimeVolume T) =
      -(∫ tau, weakDerivativeRight hΩ T v eta (g₁ + g₂) tau ∂reverseTimeVolume T)
  refine ⟨integrable_reverseTimeWeakDerivative_left hΩ T (u₁ + u₂) v eta,
    integrable_reverseTimeWeakDerivative_right hΩ T (g₁ + g₂) v eta, ?_⟩
  exact integral_neg_add (reverseTimeVolume T) hleft₁ hleft₂ hright₁ hright₂
    (weakDerivativeLeft_add_ae hΩ T v eta u₁ u₂)
    (weakDerivativeRight_add_ae hΩ T v eta g₁ g₂)
    hidentity₁ hidentity₂

/-- Gelfand weak time derivatives are closed under scalar multiplication. -/
theorem HasGelfandWeakTimeDerivative.smul
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    {hΩ : IsOpen Ω} {T : ℝ} {hT : 0 < T}
    {u : ReverseTimeL2V hΩ T} {g : ReverseTimeL2VStar hΩ T}
    (h : HasGelfandWeakTimeDerivative hΩ T hT u g) (a : ℝ) :
    HasGelfandWeakTimeDerivative hΩ T hT (a • u) (a • g : ReverseTimeL2VStar hΩ T) := by
  intro v eta
  obtain ⟨hleft, hright, hidentity⟩ := h v eta
  refine ⟨integrable_reverseTimeWeakDerivative_left hΩ T (a • u) v eta,
    integrable_reverseTimeWeakDerivative_right hΩ T (a • g : ReverseTimeL2VStar hΩ T) v eta, ?_⟩
  exact integral_neg_smul (reverseTimeVolume T) a hleft hright
    (weakDerivativeLeft_smul_ae hΩ T v eta u a)
    (weakDerivativeRight_smul_ae hΩ T v eta g a) hidentity

/-- The weak derivative relation respects equality of its two bundled curves. -/
theorem HasGelfandWeakTimeDerivative.congr
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    {hΩ : IsOpen Ω} {T : ℝ} {hT : 0 < T}
    {u u' : ReverseTimeL2V hΩ T} {g g' : ReverseTimeL2VStar hΩ T}
    (h : HasGelfandWeakTimeDerivative hΩ T hT u g)
    (hu : u = u') (hg : g = g') :
    HasGelfandWeakTimeDerivative hΩ T hT u' g' := by
  subst u'
  subst g'
  exact h

end HypoellipticAleksandrov.Parabolic.Dirichlet

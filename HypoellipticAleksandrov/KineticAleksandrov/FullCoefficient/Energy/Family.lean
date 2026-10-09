module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Energy.Setting

/-!
# The slice inequality along the family of slices

The energy inequality: for every `τ ∈ (τ₁, τ₂)`, zero slices and non-zero
slices alike satisfy `a'(τ) + (q(q-1)/4) A(τ) ≤ (4dq(q-1)/λ²) B(τ) + q ε d G(τ)`, and `G` is
bounded.
Joint measurability of the integrands in `(τ, y)` is also recorded.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open MeasureTheory Matrix
open scoped MatrixOrder

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

variable {d : ℕ}

/-- The cut-off data used in the time integration. -/
structure CutoffData (Bv ε : ℝ) (ζ : EvolutionAmbientState d → ℝ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) ζ
  nonneg : ∀ y, 0 ≤ ζ y
  le_one : ∀ y, ζ y ≤ 1
  inr : ∀ i y, coordPartial (Sum.inr i) ζ y = 0
  vel : ∀ i y, |y.1 i * ζ y| ≤ Bv
  inl : ∀ i y, |coordPartial (Sum.inl i) ζ y| ≤ ε
  eps_nonneg : 0 ≤ ε

theorem CutoffData.abs_le_one {Bv ε : ℝ} {ζ : EvolutionAmbientState d → ℝ}
    (Z : CutoffData Bv ε ζ) (y : EvolutionAmbientState d) : |ζ y| ≤ 1 := by
  rw [abs_of_nonneg (Z.nonneg y)]
  exact Z.le_one y

theorem flowGamma_zero (lam h : ℝ) (y : EvolutionAmbientState d) :
    flowGamma lam h (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) y = 0 := by
  simp [flowGamma, gradZZ, gradZV, gradVV, positionPartial, velocityPartial]

theorem coefficientGammaSum_eq_zero_of_dim_zero {lam h : ℝ}
    {β : EvolutionAmbientState d → PDE.Mat d} (hd : d = 0) (y : EvolutionAmbientState d) :
    coefficientGammaSum lam h β y = 0 := by
  subst hd
  simp [coefficientGammaSum]

variable {lam h q τ₁ τ₂ : ℝ} {ρ : ℝ → EvolutionAmbientState d → ℝ}
  {β J : ℝ → EvolutionAmbientState d → PDE.Mat d}

namespace EnergySetting

variable (S : EnergySetting lam h q τ₁ τ₂ ρ β J)

include S

theorem continuous_rho_slice (τ : ℝ) : Continuous (ρ τ) :=
  S.smooth_rho.continuous.comp (Continuous.prodMk_right τ)

theorem measurable_partial_rho (c : Fin d ⊕ Fin d) :
    Measurable fun p : ℝ × EvolutionAmbientState d => coordPartial c (ρ p.1) p.2 :=
  (continuous_coordPartial_slice S.smooth_rho c).measurable

theorem measurable_partial_flux (i j : Fin d) (c : Fin d ⊕ Fin d) :
    Measurable fun p : ℝ × EvolutionAmbientState d => coordPartial c (fun y => J p.1 y i j) p.2 :=
  (continuous_coordPartial_slice (g := fun τ y => J τ y i j) (S.smooth_flux i j) c).measurable

end EnergySetting

theorem measurable_flowGamma_family {g : ℝ → EvolutionAmbientState d → ℝ} (lam h : ℝ)
    (hm : ∀ c, Measurable fun p : ℝ × EvolutionAmbientState d => coordPartial c (g p.1) p.2) :
    Measurable fun p : ℝ × EvolutionAmbientState d => flowGamma lam h (g p.1) (g p.1) p.2 := by
  have hp : ∀ i, Measurable fun p : ℝ × EvolutionAmbientState d =>
      positionPartial i (g p.1) p.2 := fun i => hm (Sum.inr i)
  have hv : ∀ i, Measurable fun p : ℝ × EvolutionAmbientState d =>
      velocityPartial i (g p.1) p.2 := fun i => hm (Sum.inl i)
  unfold flowGamma gradZZ gradZV gradVV
  fun_prop

namespace EnergySetting

variable (S : EnergySetting lam h q τ₁ τ₂ ρ β J)

include S

theorem measurable_FA : Measurable fun p : ℝ × EvolutionAmbientState d =>
    ρ p.1 p.2 ^ (q - 2) * flowGamma lam h (ρ p.1) (ρ p.1) p.2 :=
  (S.smooth_rho.continuous.measurable.pow_const _).mul
    (measurable_flowGamma_family lam h S.measurable_partial_rho)

theorem measurable_FB : Measurable fun p : ℝ × EvolutionAmbientState d =>
    ρ p.1 p.2 ^ q * coefficientGammaSum lam h (β p.1) p.2 := by
  refine (S.smooth_rho.continuous.measurable.pow_const _).mul ?_
  unfold coefficientGammaSum
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  exact measurable_flowGamma_family (g := fun τ y => β τ y i j) lam h (S.beta_meas i j)

theorem measurable_FA_nonneg : ∀ p : ℝ × EvolutionAmbientState d,
    0 ≤ ρ p.1 p.2 ^ (q - 2) * flowGamma lam h (ρ p.1) (ρ p.1) p.2 := fun _ =>
  mul_nonneg (Real.rpow_nonneg (S.nonneg _ _) _) (flowGamma_self_nonneg S.lam_pos _ _)

theorem FB_nonneg : ∀ p : ℝ × EvolutionAmbientState d,
    0 ≤ ρ p.1 p.2 ^ q * coefficientGammaSum lam h (β p.1) p.2 := fun _ =>
  mul_nonneg (Real.rpow_nonneg (S.nonneg _ _) _) (coefficientGammaSum_nonneg S.lam_pos _ _)

/-- The slice inequality at every `τ ∈ (τ₁, τ₂)`, for zero and non-zero slices. -/
theorem slice_inequality {Bv ε : ℝ} {ζ : EvolutionAmbientState d → ℝ} (Z : CutoffData Bv ε ζ)
    {C : ℝ} (hC : ∀ τ ∈ Set.Ioo τ₁ τ₂, (∀ y, ρ τ y = 0) ∨
      (NonzeroSlice lam h q (ρ τ) (fun y => deriv (fun τ' => ρ τ' y) τ) (β τ) (J τ) ∧
        (∫ y, ρ τ y ^ (q - 1) * gradNorm (ρ τ) y) ≤ C ∧
        (∫ y, ρ τ y ^ (q - 1) * coefficientGradNorm (J τ) y) ≤ C))
    {τ : ℝ} (hτ : τ ∈ Set.Ioo τ₁ τ₂) :
    cutoffMassDeriv q ρ ζ τ + q * (q - 1) / 4 * energyA lam h q ρ ζ τ ≤
      4 * d * q * (q - 1) / lam ^ 2 * energyB lam h q ρ β ζ τ +
        q * ε * d * energyG lam h q ρ J τ := by
  have hq := S.one_lt
  rcases hC τ hτ with hz | ⟨hS, -, -⟩
  · have hq1 : q - 1 ≠ 0 := by linarith
    have hq0 : q ≠ 0 := by linarith
    have hρ0 : ρ τ = fun _ => 0 := funext hz
    have e1 : cutoffMassDeriv q ρ ζ τ = 0 := by
      simp [cutoffMassDeriv, hz, Real.zero_rpow hq1]
    have e2 : energyA lam h q ρ ζ τ = 0 := by
      simp [energyA, hρ0, flowGamma_zero]
    have e3 : energyB lam h q ρ β ζ τ = 0 := by
      simp [energyB, hz, Real.zero_rpow hq0]
    have e4 : energyG lam h q ρ J τ = 0 := by
      simp [energyG, hz, Real.zero_rpow hq1]
    rw [e1, e2, e3, e4]
    simp
  · exact (hS.toSliceHyp S.lam_pos hq Z.eps_nonneg Z.smooth Z.nonneg Z.le_one Z.inr Z.vel
      Z.inl).slice_energy

/-- The integrability of the two weighted integrands on every slice `τ ∈ (τ₁, τ₂)`. -/
theorem integrable_slice {Bv ε : ℝ} {ζ : EvolutionAmbientState d → ℝ} (Z : CutoffData Bv ε ζ)
    {C : ℝ} (hC : ∀ τ ∈ Set.Ioo τ₁ τ₂, (∀ y, ρ τ y = 0) ∨
      (NonzeroSlice lam h q (ρ τ) (fun y => deriv (fun τ' => ρ τ' y) τ) (β τ) (J τ) ∧
        (∫ y, ρ τ y ^ (q - 1) * gradNorm (ρ τ) y) ≤ C ∧
        (∫ y, ρ τ y ^ (q - 1) * coefficientGradNorm (J τ) y) ≤ C))
    {τ : ℝ} (hτ : τ ∈ Set.Ioo τ₁ τ₂) :
    Integrable (fun y => ζ y * (ρ τ y ^ (q - 2) * flowGamma lam h (ρ τ) (ρ τ) y)) ∧
      Integrable (fun y => ζ y * (ρ τ y ^ q * coefficientGammaSum lam h (β τ) y)) := by
  have hq := S.one_lt
  rcases hC τ hτ with hz | ⟨hS, -, -⟩
  · have hq0 : q ≠ 0 := by linarith
    have hρ0 : ρ τ = fun _ => 0 := funext hz
    refine ⟨?_, ?_⟩
    · have : (fun y => ζ y * (ρ τ y ^ (q - 2) * flowGamma lam h (ρ τ) (ρ τ) y)) =
          fun _ => 0 := funext fun y => by simp [hρ0, flowGamma_zero]
      rw [this]; exact integrable_zero _ _ _
    · have : (fun y => ζ y * (ρ τ y ^ q * coefficientGammaSum lam h (β τ) y)) =
          fun _ => 0 := funext fun y => by simp [hz, Real.zero_rpow hq0]
      rw [this]; exact integrable_zero _ _ _
  · have H := hS.toSliceHyp S.lam_pos hq Z.eps_nonneg Z.smooth Z.nonneg Z.le_one Z.inr Z.vel Z.inl
    exact ⟨H.integrable_gamma, H.integrable_beta⟩

theorem energyG_le {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ τ ∈ Set.Ioo τ₁ τ₂, (∀ y, ρ τ y = 0) ∨
      (NonzeroSlice lam h q (ρ τ) (fun y => deriv (fun τ' => ρ τ' y) τ) (β τ) (J τ) ∧
        (∫ y, ρ τ y ^ (q - 1) * gradNorm (ρ τ) y) ≤ C ∧
        (∫ y, ρ τ y ^ (q - 1) * coefficientGradNorm (J τ) y) ≤ C))
    {τ : ℝ} (hτ : τ ∈ Set.Ioo τ₁ τ₂) : energyG lam h q ρ J τ ≤ (|lam * h / 2| + d) * C := by
  have hq := S.one_lt
  rcases hC τ hτ with hz | ⟨-, h1, h2⟩
  · have hq1 : q - 1 ≠ 0 := by linarith
    have e4 : energyG lam h q ρ J τ = 0 := by
      simp [energyG, hz, Real.zero_rpow hq1]
    rw [e4]
    exact mul_nonneg (add_nonneg (abs_nonneg _) (Nat.cast_nonneg d)) hC0
  · unfold energyG
    have h3 := mul_le_mul_of_nonneg_left h1 (abs_nonneg (lam * h / 2))
    have h4 := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
    linarith

end EnergySetting

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

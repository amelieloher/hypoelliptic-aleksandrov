module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Absorb.DensityFubini
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Group.Integral

/-!
# Weak convergence of the smoothed densities and the duality bound

If the smoothed
densities `ρ_ε` of `Γ = μ ⊗ₘ κ` are bounded in `L^q` by `K` for every `ε > 0` and the kernel
family is an approximate identity, then `∫ ψ dΓ ≤ K ‖ψ‖_{L^{q'}}` for every bounded continuous
nonnegative `ψ` (Hölder's inequality at level `ε`, then dominated convergence).
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

variable {d : ℕ} {lam : ℝ}

/-- Local instance: Lebesgue measure on phase space is an additive Haar measure. -/
local instance absorbVolumeIsAddHaar' (d : ℕ) :
    (volume : Measure (EvolutionAmbientState d)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure volume volume

/-- A kernel family is an *approximate identity* if its translates integrate every bounded
continuous function to its value in the limit `ε ↓ 0`. -/
def IsApproxIdentity (Φ : SmoothingKernelFamily d lam) : Prop :=
  ∀ (ψ : EvolutionAmbientState d → ℝ) (B : ℝ), Continuous ψ → (∀ y, |ψ y| ≤ B) →
    ∀ y, Tendsto (fun ε => ∫ w, ψ (y + w) * Φ.kernel ε w) (𝓝[>] 0) (𝓝 (ψ y))

variable {α : Type*} [MeasurableSpace α]

omit [MeasurableSpace α] in
/-- The adjoint smoothing converges pointwise to the test function. -/
theorem tendsto_dualSmooth {Φ : SmoothingKernelFamily d lam} (hΦ : IsApproxIdentity Φ)
    {ψ : α × EvolutionAmbientState d → ℝ} (hψc : ∀ τ, Continuous fun y => ψ (τ, y)) {B : ℝ}
    (hψB : ∀ x, |ψ x| ≤ B) (x : α × EvolutionAmbientState d) :
    Tendsto (fun ε => dualSmooth Φ ε ψ x) (𝓝[>] 0) (𝓝 (ψ x)) := by
  have h := hΦ (fun y => ψ (x.1, y)) B (hψc x.1)
    (fun y => hψB _) x.2
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  unfold dualSmooth
  have := integral_add_left_eq_self (μ := (volume : Measure (EvolutionAmbientState d)))
    (fun y => ψ (x.1, y) * Φ.kernel ε (y - x.2)) x.2
  simpa using this

/-- **Duality bound at the limit**: the `L^q` bounds of the smoothed
densities pass to the pairing with bounded continuous nonnegative test functions. -/
theorem integral_le_of_smoothed_bound {Φ : SmoothingKernelFamily d lam}
    (hΦ : IsApproxIdentity Φ) (μ : Measure α) [SFinite μ]
    (κ : Kernel α (EvolutionAmbientState d)) [IsFiniteKernel κ] [IsFiniteMeasure (μ ⊗ₘ κ)]
    {p q K : ℝ} (hpq : p.HolderConjugate q) (hK : 0 ≤ K)
    (hρ : ∀ ε : ℝ, 0 < ε →
      ∫⁻ x, ENNReal.ofReal (smoothDensity Φ ε (κ x.1) x.2 ^ q) ∂(μ.prod volume) ≤
        ENNReal.ofReal (K ^ q))
    {ψ : α × EvolutionAmbientState d → ℝ} (hψm : Measurable ψ)
    (hψc : ∀ τ, Continuous fun y => ψ (τ, y)) (hψ0 : ∀ x, 0 ≤ ψ x) {B : ℝ}
    (hψB : ∀ x, ψ x ≤ B)
    (hfin : (∫⁻ x, ENNReal.ofReal (ψ x) ^ p ∂(μ.prod volume)) ≠ ⊤) :
    ∫ x, ψ x ∂(μ ⊗ₘ κ) ≤
      K * ((∫⁻ x, ENNReal.ofReal (ψ x) ^ p ∂(μ.prod volume)) ^ (1 / p)).toReal := by
  have hq : 1 < q := hpq.symm.lt
  have hq0 : 0 < q := by linarith
  have hψabs : ∀ x, |ψ x| ≤ B := fun x => by rw [abs_of_nonneg (hψ0 x)]; exact hψB x
  set A : ℝ≥0∞ := (∫⁻ x, ENNReal.ofReal (ψ x) ^ p ∂(μ.prod volume)) ^ (1 / p) with hA
  have hAfin : A ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by have := hpq.lt; positivity) hfin
  have hle : ∀ ε : ℝ, 0 < ε → ∫ x, dualSmooth Φ ε ψ x ∂(μ ⊗ₘ κ) ≤ K * A.toReal := by
    intro ε hε
    have hL := dualSmooth_nonneg_le (Φ := Φ) hε hψ0 hψB
    have hLint : Integrable (dualSmooth Φ ε ψ) (μ ⊗ₘ κ) :=
      Integrable.of_bound (measurable_dualSmooth hε hψm).aestronglyMeasurable B
        (Eventually.of_forall fun x => by
          rw [Real.norm_of_nonneg (hL x).1]; exact (hL x).2)
    have h1 : ENNReal.ofReal (∫ x, dualSmooth Φ ε ψ x ∂(μ ⊗ₘ κ)) =
        ∫⁻ x, ENNReal.ofReal (ψ x) * ENNReal.ofReal (smoothDensity Φ ε (κ x.1) x.2)
          ∂(μ.prod volume) := by
      rw [ofReal_integral_eq_lintegral_ofReal hLint (Eventually.of_forall fun x => (hL x).1),
        lintegral_mul_smoothDensity_prod_eq hε μ κ hψm hψ0 hψB]
    have hρ0 : ∀ x : α × EvolutionAmbientState d, 0 ≤ smoothDensity Φ ε (κ x.1) x.2 :=
      fun x => integral_nonneg fun y' => (Φ.pos hε _).le
    have hρm : Measurable fun x : α × EvolutionAmbientState d =>
        ENNReal.ofReal (smoothDensity Φ ε (κ x.1) x.2) := measurable_ofReal_smoothDensity hε κ
    have h2 := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.prod volume) hpq
      (f := fun x => ENNReal.ofReal (ψ x))
      (g := fun x : α × EvolutionAmbientState d =>
        ENNReal.ofReal (smoothDensity Φ ε (κ x.1) x.2))
      (ENNReal.measurable_ofReal.comp hψm).aemeasurable hρm.aemeasurable
    have h3 : (∫⁻ x, ENNReal.ofReal (smoothDensity Φ ε (κ x.1) x.2) ^ q ∂(μ.prod volume)) ^
        (1 / q) ≤ ENNReal.ofReal K := by
      have e : ∀ x : α × EvolutionAmbientState d,
          ENNReal.ofReal (smoothDensity Φ ε (κ x.1) x.2) ^ q =
            ENNReal.ofReal (smoothDensity Φ ε (κ x.1) x.2 ^ q) := fun x =>
        ENNReal.ofReal_rpow_of_nonneg (hρ0 x) hq0.le
      simp_rw [e]
      calc _ ≤ (ENNReal.ofReal (K ^ q)) ^ (1 / q) :=
            ENNReal.rpow_le_rpow (hρ ε hε) (by positivity)
        _ = ENNReal.ofReal K := by
            rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity),
              ← Real.rpow_mul hK, mul_one_div_cancel hq0.ne', Real.rpow_one]
    have h4 : ENNReal.ofReal (∫ x, dualSmooth Φ ε ψ x ∂(μ ⊗ₘ κ)) ≤ A * ENNReal.ofReal K := by
      rw [h1]
      exact h2.trans (mul_le_mul' le_rfl h3)
    have h5 := ENNReal.toReal_mono (ENNReal.mul_ne_top hAfin ENNReal.ofReal_ne_top) h4
    rw [ENNReal.toReal_ofReal (integral_nonneg fun x => (hL x).1), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hK] at h5
    linarith
  have hlim : Tendsto (fun ε => ∫ x, dualSmooth Φ ε ψ x ∂(μ ⊗ₘ κ)) (𝓝[>] 0)
      (𝓝 (∫ x, ψ x ∂(μ ⊗ₘ κ))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => B) ?_ ?_
      (integrable_const B) ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (measurable_dualSmooth hε hψm).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      refine Eventually.of_forall fun x => ?_
      have hL := dualSmooth_nonneg_le (Φ := Φ) hε hψ0 hψB x
      rw [Real.norm_of_nonneg hL.1]; exact hL.2
    · exact Eventually.of_forall fun x => tendsto_dualSmooth hΦ hψc hψabs x
  refine le_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hle ε hε

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.MeasureDerivativeTestPrimitive
public import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Tactic

/-! # The one-dimensional distributional derivative kernel on Mathlib test functions -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- Mathlib's actual smooth compact test space on the whole real line. -/
abbrev BellmanRealTest := TestFunction (⊤ : TopologicalSpace.Opens ℝ) ℝ (⊤ : ℕ∞)

/-- The ordinary derivative of a real smooth compact test, in the same Mathlib test space. -/
def bellmanTestDerivative (φ : BellmanRealTest) : BellmanRealTest where
  toFun := deriv φ
  contDiff' := (contDiff_infty_iff_deriv.mp φ.contDiff).2
  hasCompactSupport' := φ.hasCompactSupport.deriv
  tsupport_subset' := subset_univ _

/-- A test-space linear functional annihilating all derivatives is a constant distribution. -/
theorem bellman_test_derivative_kernel (L : BellmanRealTest →ₗ[ℝ] ℝ)
    (hzero : ∀ ψ : BellmanRealTest, L (bellmanTestDerivative ψ) = 0) :
    ∃ c : ℝ, ∀ φ : BellmanRealTest, L φ = c * (∫ x, φ x) := by
  let raw : ContDiffBump (0 : ℝ) :=
    { rIn := 1
      rOut := 2
      rIn_pos := by norm_num
      rIn_lt_rOut := by norm_num }
  let ρ : BellmanRealTest :=
    { toFun := raw.normed volume
      contDiff' := raw.contDiff_normed
      hasCompactSupport' := raw.hasCompactSupport_normed
      tsupport_subset' := subset_univ _ }
  have hρ : (∫ x, ρ x) = 1 := raw.integral_normed
  refine ⟨L ρ, ?_⟩
  intro φ
  let a : ℝ := ∫ x, φ x
  let θ : BellmanRealTest := φ - a • ρ
  have hiφ : Integrable (fun x => φ x) volume :=
    φ.contDiff.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have hiρ : Integrable (fun x => ρ x) volume :=
    ρ.contDiff.continuous.integrable_of_hasCompactSupport ρ.hasCompactSupport
  have hmean : (∫ x, θ x) = 0 := by
    change (∫ x, φ x - a * ρ x) = 0
    rw [integral_sub hiφ (hiρ.const_mul a), integral_const_mul, hρ]
    change a - a * 1 = 0
    ring
  obtain ⟨ψ, hψ, hcψ, hdψ⟩ :=
    bellman_exists_test_primitive θ θ.contDiff θ.hasCompactSupport hmean
  let Ψ : BellmanRealTest := ⟨ψ, hψ, hcψ, subset_univ _⟩
  have he : bellmanTestDerivative Ψ = θ := by
    apply DFunLike.ext
    intro x
    exact congrFun hdψ x
  have hz := hzero Ψ
  rw [he] at hz
  change L (φ - a • ρ) = 0 at hz
  rw [map_sub, map_smul] at hz
  change L φ - a * L ρ = 0 at hz
  change L φ = L ρ * a
  linarith

end HypoellipticAleksandrov.KineticAleksandrov

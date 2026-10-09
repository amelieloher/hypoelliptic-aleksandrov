module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularPositiveTailDivergence
import Mathlib.Tactic

/-! # The angular tail rules out a positive linear growth limit -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set Filter
open scoped Topology

/-- Ellipticity and the finite tail exclude a positive limit of h(y)/y. -/
theorem bellmanAngularTail_no_positive_linear_limit (R β : ℝ) (hR : 1 ≤ R) (hβ : 3 ≤ β)
    (f h : ℝ → ℝ)
    (htail : IntegrableOn (fun y => f y * |y| ^ (β - 4)) {y : ℝ | 2 < |y|} volume)
    (hcomp : ∀ᵐ y ∂volume, h y ≤ R * f y) (L : ℝ) (hL : 0 < L)
    (hlim : Tendsto (fun y => h y / y) atTop (𝓝 L)) : False := by
  have hRp : 0 < R := by linarith
  have he : ∀ᶠ y : ℝ in atTop, L / 2 < h y / y :=
    hlim.eventually (eventually_gt_nhds (by linarith : L / 2 < L))
  obtain ⟨a, ha⟩ := eventually_atTop.mp he
  let b := max 2 a
  have hb : 2 ≤ b := le_max_left _ _
  have hc : 0 < L / (2 * R) := div_pos hL (by positivity)
  apply bellmanAngularTail_not_power_lower_bound f β b (L / (2 * R)) (β - 3)
    htail hb hc (by linarith)
  filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae hcomp] with y hy hcy
  have hyp : 0 < y := by have := (le_max_left 2 a).trans hy.le; linarith
  have hg := ha y ((le_max_right 2 a).trans hy.le)
  have hly : L / 2 * y < h y := (lt_div_iff₀ hyp).mp hg
  have hfy : (L / (2 * R)) * y ≤ f y := by
    have heq : R * ((L / (2 * R)) * y) = L / 2 * y := by field_simp
    rw [← heq] at hly
    exact le_of_mul_le_mul_left (hly.le.trans hcy) hRp
  have hm := mul_le_mul_of_nonneg_right hfy (Real.rpow_nonneg hyp.le (β - 4))
  have hp : y * y ^ (β - 4) = y ^ (β - 3) := by
    calc
      y * y ^ (β - 4) = y ^ (1 : ℝ) * y ^ (β - 4) := by rw [Real.rpow_one]
      _ = y ^ (1 + (β - 4)) := (Real.rpow_add hyp _ _).symm
      _ = y ^ (β - 3) := by congr 1; ring
  calc
    (L / (2 * R)) * y ^ (β - 3) =
        ((L / (2 * R)) * y) * y ^ (β - 4) := by rw [mul_assoc, hp]
    _ ≤ _ := hm

end HypoellipticAleksandrov.KineticAleksandrov

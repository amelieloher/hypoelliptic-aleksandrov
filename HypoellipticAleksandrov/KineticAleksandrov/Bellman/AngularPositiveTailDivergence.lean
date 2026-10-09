module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularTail
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-! # Power lower bounds incompatible with the finite angular tail -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- A finite angular tail cannot dominate a positive nonintegrable power on a positive half-
line. -/
theorem bellmanAngularTail_not_power_lower_bound (f : ℝ → ℝ) (β a c p : ℝ)
    (htail : IntegrableOn (fun y => f y * |y| ^ (β - 4)) {y : ℝ | 2 < |y|} volume)
    (ha : 2 ≤ a) (hc : 0 < c) (hp : -1 ≤ p)
    (hlower : ∀ᵐ y ∂volume.restrict (Ioi a), c * y ^ p ≤ f y * y ^ (β - 4)) : False := by
  have hap : 0 < a := by linarith
  have hi : IntegrableOn (fun y => f y * y ^ (β - 4)) (Ioi a) volume := by
    apply (htail.mono_set (show Ioi a ⊆ {y : ℝ | 2 < |y|} by
      intro y hy; change a < y at hy
      change 2 < |y|
      rw [abs_of_pos (by linarith : 0 < y)]
      linarith)).congr_fun _ measurableSet_Ioi
    intro y hy
    change f y * |y| ^ (β - 4) = f y * y ^ (β - 4)
    rw [abs_of_pos (hap.trans hy)]
  have hpow : IntegrableOn (fun y : ℝ => c * y ^ p) (Ioi a) volume := by
    apply hi.mono' (by fun_prop)
    filter_upwards [hlower, ae_restrict_mem measurableSet_Ioi] with y hy hya
    have hn : 0 ≤ c * y ^ p := mul_nonneg hc.le (Real.rpow_nonneg (hap.trans hya).le _)
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    exact hy
  have hrpow : IntegrableOn (fun y : ℝ => y ^ p) (Ioi a) volume := by
    have hs : Integrable (fun y : ℝ => c⁻¹ * (c * y ^ p))
        (volume.restrict (Ioi a)) := Integrable.const_mul hpow c⁻¹
    change Integrable (fun y : ℝ => y ^ p) (volume.restrict (Ioi a))
    convert! hs using 1
    funext y
    field_simp [hc.ne']
  have he := (integrableOn_Ioi_rpow_iff hap).mp hrpow
  linarith

end HypoellipticAleksandrov.KineticAleksandrov

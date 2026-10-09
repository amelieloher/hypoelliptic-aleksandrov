module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GeometricCoreCoverDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FarVelocityDensity
import Mathlib.Tactic

/-! # The improved cylinder density from its two named source predecessors

The band estimate and the complete clock-pushforward proposition remain explicit
conditional inputs. The conclusion is the independently density Prop.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory

/-- The exact improved density statement follows from the band and clock propositions. -/
theorem below_four_density_of_band (hband : BelowFourBandStatement)
    (hpush : PushforwardStatement) : BelowFourDensityStatement := by
  intro hH hLE lam Lam hlam hLam alpha q ha hq
  have hx := belowFour_exponent_range lam Lam hlam hLam alpha q ha hq
  obtain ⟨Cn, hCn, hn⟩ := below_four_near_velocity_density
    hband hH hLE lam Lam hlam hLam alpha q ha hq
  obtain ⟨Cf, hCf, hf⟩ := cylinder_density_far
    hpush hH hLE lam Lam hlam hLam q ⟨hq.1, hx.2.1⟩
  refine ⟨max Cn Cf, hCn.trans_le (le_max_left _ _), ?_⟩
  intro A Z₀ R hR P hP
  have hr : 0 ≤ R ^ (6 / q - 4) := Real.rpow_nonneg hR.le _
  by_cases hnear : |Z₀.velocity 0| ≤ 8 * R
  · obtain ⟨g, hgm, hg0, hgd, hgp, hgn⟩ := hn A Z₀ R hR P hP hnear
    exact ⟨g, hgm, hg0, hgd, hgp,
      hgn.trans (mul_le_mul_of_nonneg_right (le_max_left Cn Cf) hr)⟩
  · obtain ⟨g, hgm, hg0, hgd, hgp, hgn⟩ := hf A Z₀ R hR P hP (lt_of_not_ge hnear)
    exact ⟨g, hgm, hg0, hgd, hgp,
      hgn.trans (mul_le_mul_of_nonneg_right (le_max_right Cn Cf) hr)⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

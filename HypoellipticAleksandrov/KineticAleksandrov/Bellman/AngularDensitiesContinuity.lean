module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-! # Continuity and positivity of actual absolutely continuous angular representatives -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- Absolute continuity on every compact interval gives global continuity of the
representative. -/
theorem bellman_locallyAC_continuous {h : ℝ → ℝ}
    (hh : ∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval h a b) : Continuous h := by
  apply continuous_iff_continuousAt.mpr
  intro y
  have hle : y - 1 ≤ y + 1 := by linarith
  have hc : ContinuousOn h (Icc (y - 1) (y + 1)) := by
    simpa only [uIcc_of_le hle] using (hh (y - 1) (y + 1) hle).continuousOn
  exact hc.continuousAt (Icc_mem_nhds (by linarith) (by linarith))

/-- A continuous angular representative that is nonnegative almost everywhere is nonnegative. -/
theorem bellman_continuous_nonneg_of_ae {h : ℝ → ℝ} (hh : Continuous h)
    (hn : ∀ᵐ y ∂volume, 0 ≤ h y) : ∀ y : ℝ, 0 ≤ h y := by
  have hc : IsClosed {y : ℝ | 0 ≤ h y} := isClosed_le continuous_const hh
  have he : {y : ℝ | 0 ≤ h y} =ᵐ[volume] univ := by
    filter_upwards [hn] with y hy
    change (0 ≤ h y) = True
    exact propext ⟨fun _ => trivial, fun _ => hy⟩
  have hs := (hc.ae_eq_univ_iff_eq (μ := volume)).mp he
  intro y
  have hy : y ∈ {y : ℝ | 0 ≤ h y} := by rw [hs]; trivial
  exact hy

/-- Almost everywhere ellipticity gives nonnegativity of the continuous angular density. -/
theorem bellmanAngularDensity_nonneg {f h : ℝ → ℝ}
    (hh : ∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval h a b)
    (hf : ∀ᵐ y ∂volume, 0 ≤ f y) (hfh : ∀ᵐ y ∂volume, f y ≤ h y) :
    ∀ y : ℝ, 0 ≤ h y := by
  apply bellman_continuous_nonneg_of_ae (bellman_locallyAC_continuous hh)
  filter_upwards [hf, hfh] with y hy hfy
  exact hy.trans hfy

end HypoellipticAleksandrov.KineticAleksandrov

module

public import HypoellipticAleksandrov.Geometry.KineticPointMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Geometry
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifyApproximateIdentity
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-! # Measurable fixed-time convergence and positive-part norm convergence -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Filter MeasureTheory
open scoped Topology ENNReal

/-- Measurable convergence at almost every spatial point at each time yields convergence
in the literal kinetic product-volume carrier. -/
theorem construction_fixed_time_tendsto_ae_spacetime {d : ℕ}
    (F : ℕ → ℝ × XV d → ℝ) (g : ℝ × XV d → ℝ)
    (hF : ∀ n, Measurable (F n)) (hg : Measurable g)
    (ht : ∀ t : ℝ, ∀ᵐ q ∂volume,
      Tendsto (fun n => F n (t, q)) atTop (𝓝 (g (t, q)))) :
    ∀ᵐ P : KineticPoint d ∂volume,
      Tendsto (fun n => F n (KineticPoint.equivProd d P)) atTop
        (𝓝 (g (KineticPoint.equivProd d P))) := by
  have hp := measurableSet_tendsto_fun (l := atTop) hF hg
  have he : ∀ᵐ z : ℝ × XV d ∂volume,
      Tendsto (fun n => F n z) atTop (𝓝 (g z)) :=
    (Measure.ae_prod_iff_ae_ae hp).mpr (Eventually.of_forall ht)
  exact (KineticPoint.measurePreserving_equivProd d).quasiMeasurePreserving.ae he

/-- Uniformly bounded measurable convergence controls the positive-part source error in
any finite exponent on a finite-measure cylinder. -/
theorem construction_positive_part_error_tendsto {X : Type*} [MeasurableSpace X]
    (nu : Measure X) [IsFiniteMeasure nu] (p : ℝ≥0∞) (hp0 : p ≠ 0) (hpTop : p ≠ ∞)
    (F : ℕ → X → ℝ) (g : X → ℝ)
    (hF : ∀ n, AEStronglyMeasurable (F n) nu) (hg : AEStronglyMeasurable g nu)
    (C : ℝ) (hC : 0 ≤ C)
    (hFb : ∀ n, ∀ᵐ x ∂nu, |F n x| ≤ C) (hgb : ∀ᵐ x ∂nu, |g x| ≤ C)
    (hlim : ∀ᵐ x ∂nu, Tendsto (fun n => F n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => eLpNorm (fun x => max (F n x) 0 - max (g x) 0) p nu)
      atTop (𝓝 0) := by
  apply bounded_convergence_eLpNorm nu p hp0 hpTop _
    (fun n => ((hF n).aemeasurable.max aemeasurable_const).aestronglyMeasurable.sub
      (hg.aemeasurable.max aemeasurable_const).aestronglyMeasurable) (2 * C)
  · intro n
    filter_upwards [hFb n, hgb] with x hx hy
    have hbF : |max (F n x) 0| ≤ C := by
      rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le (le_abs_self _ |>.trans hx) hC
    have hbg : |max (g x) 0| ≤ C := by
      rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le (le_abs_self _ |>.trans hy) hC
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using!
      (abs_sub _ _).trans (show |max (F n x) 0| + |max (g x) 0| ≤ 2 * C by
        linarith only [hbF, hbg])
  · filter_upwards [hlim] with x hx
    have hm := (hx.max (tendsto_const_nhds (x := (0 : ℝ)))).sub_const (max (g x) 0)
    simpa only [Pi.sub_apply, sub_self] using! hm

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

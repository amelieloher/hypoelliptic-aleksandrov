module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeRegularityIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Exact differentiation of the fixed compact-parameter integral -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory Set

/-- Differentiation commutes with the compact integral of a smooth formula whose internal
parameter is merely continuous. This identifies the derivative, beyond joint smoothness. -/
theorem construction_deriv_compact_parameter {Y A : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [TopologicalSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A]
    (mu : Measure A) [IsFiniteMeasure mu] (radius : A → Y) (hr : Continuous radius)
    (f : ℝ × Y → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) :
    deriv (fun s => ∫ a, f (s, radius a) ∂mu) t =
      ∫ a, deriv (fun s => f (s, radius a)) t ∂mu := by
  let L : ℝ →L[ℝ] ℝ × Y := (ContinuousLinearMap.id ℝ ℝ).prod 0
  let J : ((ℝ × Y) →L[ℝ] ℝ) →L[ℝ] ℝ →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ ℝ (ℝ × Y) ℝ).flip L
  let g : ℝ × Y → ℝ →L[ℝ] ℝ := fun w => J (fderiv ℝ f w)
  have hg : Continuous g :=
    J.continuous.comp (hf.continuous_fderiv (by simp))
  have hd (s : ℝ) (a : A) : HasFDerivAt (fun x => f (x, radius a))
      (g (s, radius a)) s :=
    (hf.differentiable (by simp) (s, radius a)).hasFDerivAt.comp s
      ((hasFDerivAt_id s).prodMk (hasFDerivAt_const (radius a) s))
  have hfc : Continuous (fun w : ℝ × A => f (w.1, radius w.2)) :=
    hf.continuous.comp (continuous_fst.prodMk (hr.comp continuous_snd))
  have hgc : Continuous (fun w : ℝ × A => g (w.1, radius w.2)) :=
    hg.comp (continuous_fst.prodMk (hr.comp continuous_snd))
  have he := bellman_compact_parameter_hasFDerivAt mu isOpen_univ
    (fun s a => f (s, radius a)) (fun s a => g (s, radius a))
    hfc.continuousOn hgc.continuousOn (fun s _ a => hd s a) (mem_univ t)
  have hi : Integrable (fun a => g (t, radius a)) mu :=
    bellman_compact_parameter_integrable mu (f := fun s a => g (s, radius a))
      hgc.continuousOn (mem_univ t)
  rw [he.hasDerivAt.deriv, ContinuousLinearMap.integral_apply hi]
  apply integral_congr_ae
  filter_upwards [] with a
  exact (hd t a).hasDerivAt.deriv.symm

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.HomogeneousTestLiftIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! # Smooth integration when a continuous compact parameter enters a smooth formula -/

@[expose] public section
noncomputable section
universe u v
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Set MeasureTheory
open scoped Topology

/-- A continuous compact parameter need not be differentiable: integration of a formula
smooth in the external variables remains smooth to every specified finite order. -/
theorem compact_parameter_contDiff_nat {E Y : Type u} {A : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [TopologicalSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A]
    (mu : Measure A) [IsFiniteMeasure mu] (radius : A → Y) (hr : Continuous radius)
    (n : ℕ) : ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (f : E × Y → F), ContDiff ℝ n f →
        ContDiff ℝ n (fun q => ∫ a, f (q, radius a) ∂mu) := by
  induction n with
  | zero =>
    intro F _ _ f hf
    apply contDiff_zero.mpr
    apply continuous_iff_continuousAt.mpr
    intro q
    apply bellman_compact_parameter_continuousAt mu isOpen_univ _ _ (mem_univ q)
    exact (hf.continuous.comp (continuous_fst.prodMk
      (hr.comp continuous_snd))).continuousOn
  | succ n ih =>
    intro F _ _ f hf
    let L : E →L[ℝ] E × Y := (ContinuousLinearMap.id ℝ E).prod 0
    let J : ((E × Y) →L[ℝ] F) →L[ℝ] E →L[ℝ] F :=
      (ContinuousLinearMap.compL ℝ E (E × Y) F).flip L
    let g : E × Y → E →L[ℝ] F := fun w => J (fderiv ℝ f w)
    have hg : ContDiff ℝ n g := J.contDiff.comp
      (hf.fderiv_right (m := n) (by simp))
    have hd : ∀ q : E, ∀ a : A,
        HasFDerivAt (fun x => f (x, radius a)) (g (q, radius a)) q := by
      intro q a
      exact (hf.differentiable (by simp) (q, radius a)).hasFDerivAt.comp q
        ((hasFDerivAt_id q).prodMk (hasFDerivAt_const (radius a) q))
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨fun q => ∫ a, g (q, radius a) ∂mu, ih g hg, ?_⟩
    intro q
    apply bellman_compact_parameter_hasFDerivAt mu isOpen_univ _ _ _ _ _ (mem_univ q)
    · exact (hf.continuous.comp (continuous_fst.prodMk
        (hr.comp continuous_snd))).continuousOn
    · exact (hg.continuous.comp (continuous_fst.prodMk
        (hr.comp continuous_snd))).continuousOn
    · intro x _ a
      exact hd x a

/-- A globally smooth formula integrated against a continuous compact parameter is
smooth of all finite orders. -/
theorem compact_parameter_contDiff {E Y F : Type u} {A : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A]
    (mu : Measure A) [IsFiniteMeasure mu] (radius : A → Y) (hr : Continuous radius)
    (f : E × Y → F) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q => ∫ a, f (q, radius a) ∂mu) := by
  apply contDiff_infty.mpr
  intro n
  exact compact_parameter_contDiff_nat mu radius hr n f (hf.of_le (by simp))

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

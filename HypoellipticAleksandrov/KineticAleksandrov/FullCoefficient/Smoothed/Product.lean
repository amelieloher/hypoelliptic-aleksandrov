module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothed.Mollifier
public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothing.Kernel
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# The space-time kernel `η_δ(t) Φ_h(w)` is smooth with all derivatives bounded

Joint smoothness of the smoothed density and flux in `(τ, y)` is
obtained from the weighted-convolution engine of the smoothing estimates on `ℝ × ℝ^{2d}`; the engine
needs
the kernel `(t, w) ↦ η_δ(t) Φ_h(w)` to be smooth with every derivative bounded.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open MeasureTheory

variable {d : ℕ} {δ : ℝ} {η : ℝ → ℝ} {lam : ℝ}

/-- Composition with a contraction on the right does not increase iterated derivatives. -/
theorem norm_iteratedFDeriv_comp_le {E G F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : G →L[ℝ] E) (hg : ‖g‖ ≤ 1) {f : E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : G) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (f ∘ g) x‖ ≤ ‖iteratedFDeriv ℝ i f (g x)‖ := by
  rw [g.iteratedFDeriv_comp_right hf x (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have : ∏ _j : Fin i, ‖g‖ ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hg)
  calc _ ≤ ‖iteratedFDeriv ℝ i f (g x)‖ * 1 := by gcongr
    _ = _ := mul_one _

theorem IsMollifier.exists_bound_iteratedFDeriv (hη : IsMollifier δ η) (i : ℕ) :
    ∃ C : ℝ, ∀ t, ‖iteratedFDeriv ℝ i η t‖ ≤ C :=
  Continuous.bounded_above_of_compact_support
    (hη.contDiff.continuous_iteratedFDeriv (by exact_mod_cast le_top))
    (hη.hasCompactSupport.iteratedFDeriv i)

/-- The space-time kernel `(t, w) ↦ η(t) Φ_h(w)` is smooth with bounded derivatives. -/
theorem isBoundedSmooth_timeKernel (hη : IsMollifier δ η) (Φ : SmoothingKernelFamily d lam)
    {h : ℝ} (hh : 0 < h) :
    IsBoundedSmooth (fun p : ℝ × EvolutionAmbientState d => η p.1 * Φ.kernel h p.2) := by
  have hΦ := Φ.isBoundedSmooth hh
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × EvolutionAmbientState d => η p.1) :=
    hη.contDiff.comp contDiff_fst
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × EvolutionAmbientState d => Φ.kernel h p.2) :=
    hΦ.contDiff.comp contDiff_snd
  refine ⟨h1.mul h2, fun n => ?_⟩
  choose Cη hCη using fun i => hη.exists_bound_iteratedFDeriv i
  choose CΦ hCΦ using fun i => hΦ.bounded i
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * |Cη i| * |CΦ (n - i)|, fun x => ?_⟩
  have key := (ContinuousLinearMap.mul ℝ ℝ).norm_iteratedFDeriv_le_of_bilinear h1 h2 x
    (n := n) (by exact_mod_cast le_top)
  have hB : ‖ContinuousLinearMap.mul ℝ ℝ‖ ≤ 1 := ContinuousLinearMap.opNorm_mul_le ℝ ℝ
  refine (key.trans ?_)
  calc _ ≤ 1 * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun p : ℝ × EvolutionAmbientState d => η p.1) x‖ *
        ‖iteratedFDeriv ℝ (n - i) (fun p : ℝ × EvolutionAmbientState d => Φ.kernel h p.2) x‖ :=
        mul_le_mul_of_nonneg_right hB (Finset.sum_nonneg fun i _ => by positivity)
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun p : ℝ × EvolutionAmbientState d => η p.1) x‖ *
        ‖iteratedFDeriv ℝ (n - i) (fun p : ℝ × EvolutionAmbientState d => Φ.kernel h p.2) x‖ :=
        one_mul _
    _ ≤ _ := by
        refine Finset.sum_le_sum fun i _ => ?_
        have e1 : ‖iteratedFDeriv ℝ i (fun p : ℝ × EvolutionAmbientState d => η p.1) x‖ ≤
            |Cη i| :=
          (norm_iteratedFDeriv_comp_le (ContinuousLinearMap.fst ℝ ℝ (EvolutionAmbientState d))
            (ContinuousLinearMap.norm_fst_le ℝ ℝ (EvolutionAmbientState d)) hη.contDiff x i).trans
            ((hCη i _).trans (le_abs_self _))
        have e2 : ‖iteratedFDeriv ℝ (n - i) (fun p : ℝ × EvolutionAmbientState d =>
            Φ.kernel h p.2) x‖ ≤ |CΦ (n - i)| :=
          (norm_iteratedFDeriv_comp_le (ContinuousLinearMap.snd ℝ ℝ (EvolutionAmbientState d))
            (ContinuousLinearMap.norm_snd_le ℝ ℝ (EvolutionAmbientState d)) hΦ.contDiff x
            (n - i)).trans
            ((hCΦ (n - i) _).trans (le_abs_self _))
        gcongr

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

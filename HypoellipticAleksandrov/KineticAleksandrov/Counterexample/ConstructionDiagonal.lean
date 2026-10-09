module

public import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Diagonal scales preserving finitely many eventual conditions -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Filter
open scoped ENNReal

/-- Per-function error convergence permits separate scales with a vanishing diagonal error. -/
theorem construction_diagonal_choice (error : ℕ → ℕ → ℝ≥0∞)
    (herr : ∀ j, Tendsto (error j) atTop (nhds 0))
    (good : ℕ → ℕ → Prop) (hgood : ∀ j, ∀ᶠ k in atTop, good j k) :
    ∃ scale : ℕ → ℕ,
      (∀ j, good j (scale j) ∧
        error j (scale j) < ENNReal.ofReal (1 / ((j : ℝ) + 1))) ∧
      Tendsto (fun j => error j (scale j)) atTop (nhds 0) := by
  classical
  have hchoose : ∀ j, ∃ k, good j k ∧
      error j k < ENNReal.ofReal (1 / ((j : ℝ) + 1)) := by
    intro j
    have hp : 0 < (1 / ((j : ℝ) + 1)) := by positivity
    have he : ∀ᶠ k in atTop,
        error j k < ENNReal.ofReal (1 / ((j : ℝ) + 1)) :=
      (herr j).eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hp))
    exact ((hgood j).and he).exists
  choose scale hs using hchoose
  refine ⟨scale, hs, ?_⟩
  have hu : Tendsto (fun j : ℕ => ENNReal.ofReal (1 / ((j : ℝ) + 1)))
      atTop (nhds 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun _ => bot_le) (fun j => (hs j).2.le)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

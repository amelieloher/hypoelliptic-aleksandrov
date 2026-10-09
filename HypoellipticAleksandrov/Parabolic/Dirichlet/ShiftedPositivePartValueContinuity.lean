module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10ShiftedPositivePart
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Continuity of shifted positive parts in spatial `L²`

On a bounded spatial domain, the shifted positive part depends continuously
and jointly on its `L²` input and its nonnegative constant threshold.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ} {Ω : Set (PDE.Vec d)}

private theorem shiftedPositivePartValue_eq_posPart_sub_const
    [IsFiniteMeasure (PDE.volumeOn Ω)]
    (k : ℝ≥0) (f : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    shiftedPositivePartValue k f =
      Lp.posPart (f - Lp.const (2 : ℝ≥0∞) (PDE.volumeOn Ω) (k : ℝ)) := by
  apply Lp.ext
  filter_upwards [coeFn_shiftedPositivePartValue k f,
    Lp.coeFn_posPart (f - Lp.const (2 : ℝ≥0∞) (PDE.volumeOn Ω) (k : ℝ)),
    Lp.coeFn_sub f (Lp.const (2 : ℝ≥0∞) (PDE.volumeOn Ω) (k : ℝ)),
    Lp.coeFn_const (p := (2 : ℝ≥0∞)) (μ := PDE.volumeOn Ω) (k : ℝ)] with x hshift hpos hsub hconst
  rw [hshift, hpos, hsub]
  simp only [Pi.sub_apply, hconst, Function.const_apply]

/-- On a bounded domain, the spatial `L²` shifted positive part is jointly
continuous in the function and its nonnegative constant threshold. -/
theorem continuous_shiftedPositivePartValue_of_isBounded
    (hΩbounded : Bornology.IsBounded Ω) :
    Continuous (fun p : PDE.ScalarLp Ω (2 : ℝ≥0∞) × ℝ≥0 =>
      shiftedPositivePartValue p.2 p.1) := by
  letI : IsFiniteMeasure (PDE.volumeOn Ω) :=
    isFiniteMeasure_restrict.mpr hΩbounded.measure_lt_top.ne
  rw [show (fun p : PDE.ScalarLp Ω (2 : ℝ≥0∞) × ℝ≥0 =>
      shiftedPositivePartValue p.2 p.1) =
      fun p => Lp.posPart
        (p.1 - Lp.constL (2 : ℝ≥0∞) (PDE.volumeOn Ω) ℝ (p.2 : ℝ)) by
    funext p
    exact shiftedPositivePartValue_eq_posPart_sub_const p.2 p.1]
  exact Lp.continuous_posPart.comp
    (continuous_fst.sub
      ((Lp.constL (2 : ℝ≥0∞) (PDE.volumeOn Ω) ℝ).continuous.comp
        (NNReal.continuous_coe.comp continuous_snd)))

end HypoellipticAleksandrov.Parabolic.Dirichlet

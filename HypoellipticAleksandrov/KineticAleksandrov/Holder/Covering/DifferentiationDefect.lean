module

public import HypoellipticAleksandrov.Geometry.KineticPointMeasure
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.Tactic

/-! # Finite measure density defects

A failed near-full density bound is charged to the complement inside the comparison set.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

open Set MeasureTheory

/-- A finite-volume density deficit forces the corresponding complement measure. -/
theorem measure_density_defect {d : ℕ} {E C : Set (KineticPoint d)}
    (hE : NullMeasurableSet E volume) (hC : volume C ≠ ⊤)
    {eta : ℝ} (heta : 0 ≤ eta)
    (hdef : (volume (E ∩ C)).toReal ≤ (1-eta)*(volume C).toReal) :
    ENNReal.ofReal eta * volume C ≤ volume (C \ E) := by
  have hI : volume (C ∩ E) ≠ ⊤ := ne_top_of_le_ne_top hC (measure_mono inter_subset_left)
  have hD : volume (C \ E) ≠ ⊤ := ne_top_of_le_ne_top hC (measure_mono sdiff_subset)
  have hsum := congrArg ENNReal.toReal (measure_inter_add_sdiff₀ (μ := volume) C hE)
  rw [ENNReal.toReal_add hI hD, inter_comm] at hsum
  apply (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC) hD).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal heta]
  linarith only [hdef, hsum]

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

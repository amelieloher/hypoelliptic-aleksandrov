module

public import PDEFoundation.Geometry.AxisCube
public import PDEFoundation.Measure.RestrictedVolume
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Volume of axis-aligned cubes

Exact volume, positivity, and finiteness for the cube geometry shared with the
application repositories.
-/

@[expose] public section

namespace PDE

open MeasureTheory

theorem measurableSet_axisCube {d : ℕ}
    (z : Vec d) (L : ℝ) :
    MeasurableSet (axisCube z L) :=
  (isOpen_axisCube z L).measurableSet

theorem volume_axisCube_ne_top {d : ℕ}
    (z : Vec d) (L : ℝ) :
    volume (axisCube z L) ≠ ⊤ :=
  IsOpenBoundedConvexDomain.volume_ne_top
    (isOpenBoundedConvexDomain_axisCube z L)

/-- The real volume of a nonnegatively oriented axis cube is `L ^ d`. -/
theorem volume_axisCube_toReal {d : ℕ}
    (z : Vec d) {L : ℝ} (hL : 0 ≤ L) :
    (volume (axisCube z L)).toReal = L ^ d := by
  have hle : z ≤ fun i => z i + L :=
    fun i => by simpa using hL
  have hprod :
      (volume (axisCube z L)).toReal =
        ∏ _i : Fin d, L := by
    rw [axisCube, Real.volume_pi_Ioo_toReal hle]
    exact Finset.prod_congr rfl fun i _hi => by ring
  rw [hprod, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem volume_axisCube_pos {d : ℕ}
    (z : Vec d) {L : ℝ} (hL : 0 < L) :
    0 < volume (axisCube z L) :=
  IsOpenBoundedConvexDomain.volume_pos
    (isOpenBoundedConvexDomain_axisCube z L)
    (axisCube_nonempty z hL)

theorem volume_axisCube_toReal_pos {d : ℕ}
    (z : Vec d) {L : ℝ} (hL : 0 < L) :
    0 < (volume (axisCube z L)).toReal := by
  rw [volume_axisCube_toReal z hL.le]
  exact pow_pos hL d

theorem isFiniteMeasure_volumeOn_axisCube {d : ℕ}
    (z : Vec d) (L : ℝ) :
    IsFiniteMeasure (volumeOn (axisCube z L)) :=
  IsOpenBoundedConvexDomain.isFiniteMeasure_volumeOn
    (isOpenBoundedConvexDomain_axisCube z L)

end PDE

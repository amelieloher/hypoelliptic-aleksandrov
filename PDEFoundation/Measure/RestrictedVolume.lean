module

public import PDEFoundation.Geometry.ConvexDomain
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Restricted Lebesgue volume

One restricted-volume convention for every later `Lp`, Sobolev, and weak PDE
module.
-/

@[expose] public section

namespace PDE

/-- Lebesgue volume restricted to a native-vector domain. -/
noncomputable abbrev volumeOn {d : ℕ} (U : Set (Vec d)) :=
  MeasureTheory.volume.restrict U

/-- Compatibility name used by the existing LIH Sobolev layer. -/
noncomputable abbrev volumeMeasureOn {d : ℕ} (U : Set (Vec d)) :=
  volumeOn U

theorem IsBoundedDomain.volume_lt_top {d : ℕ}
    {U : Set (Vec d)} (hU : IsBoundedDomain U) :
    MeasureTheory.volume U < ⊤ :=
  hU.isBounded.measure_lt_top

theorem IsBoundedDomain.isFiniteMeasure_volumeOn {d : ℕ}
    {U : Set (Vec d)} (hU : IsBoundedDomain U) :
    MeasureTheory.IsFiniteMeasure (volumeOn U) := by
  let : Fact (MeasureTheory.volume U < ⊤) :=
    ⟨hU.volume_lt_top⟩
  infer_instance

namespace IsOpenBoundedConvexDomain

theorem volume_pos {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty) :
    0 < MeasureTheory.volume U :=
  hU.isOpen.measure_pos MeasureTheory.volume hne

theorem volume_lt_top {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) :
    MeasureTheory.volume U < ⊤ :=
  hU.isBoundedDomain.volume_lt_top

theorem volume_ne_top {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) :
    MeasureTheory.volume U ≠ ⊤ :=
  hU.volume_lt_top.ne

theorem volume_toReal_pos {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty) :
    0 < (MeasureTheory.volume U).toReal :=
  ENNReal.toReal_pos (hU.volume_pos hne).ne' hU.volume_ne_top

theorem isFiniteMeasure_volumeOn {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) :
    MeasureTheory.IsFiniteMeasure (PDE.volumeOn U) :=
  hU.isBoundedDomain.isFiniteMeasure_volumeOn

end IsOpenBoundedConvexDomain

namespace IsSobolevRegularDomain

theorem volume_lt_top {d : ℕ} {U : Set (Vec d)}
    (hU : IsSobolevRegularDomain U) :
    MeasureTheory.volume U < ⊤ :=
  hU.isBoundedDomain.volume_lt_top

theorem isFiniteMeasure_volumeOn {d : ℕ} {U : Set (Vec d)}
    (hU : IsSobolevRegularDomain U) :
    MeasureTheory.IsFiniteMeasure (PDE.volumeOn U) :=
  hU.isBoundedDomain.isFiniteMeasure_volumeOn

end IsSobolevRegularDomain

end PDE

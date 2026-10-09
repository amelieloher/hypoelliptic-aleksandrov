module

public import HypoellipticAleksandrov.Geometry.KineticPointMeasure
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Compact finiteness of the existing kinetic volume

The existing volume is the pushforward of product Lebesgue measure under the
coordinate homeomorphism. This supplies compact finiteness without changing it.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov MeasureTheory

/-- The existing coordinate topology on kinetic points is locally compact. -/
instance kineticPoint_locallyCompactSpace (n : ℕ) : LocallyCompactSpace (KineticPoint n) :=
  (KineticPoint.homeomorphProd n).locallyCompactSpace_iff.mpr inferInstance

/-- The existing, exactly normalized kinetic volume is finite on compact sets. -/
instance kineticVolume_isFiniteMeasureOnCompacts (n : ℕ) :
    IsFiniteMeasureOnCompacts (volume : Measure (KineticPoint n)) where
  lt_top_of_isCompact K hK := by
    change Measure.map (KineticPoint.equivProd n).symm volume K < ⊤
    rw [Measure.map_apply (KineticPoint.measurable_equivProd_symm n) hK.measurableSet]
    exact ((KineticPoint.homeomorphProd n).symm.isCompact_preimage.mpr hK).measure_lt_top

end HypoellipticAleksandrov.KineticAleksandrov

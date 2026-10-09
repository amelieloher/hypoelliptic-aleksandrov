module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.AssemblyA
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.SmoothHolder
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.SpatialDerivatives

/-! # Time–velocity Hölder estimate from the proved spatial derivative bounds -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set MeasureTheory Holder LocalA
open scoped MatrixOrder

namespace LocalA

/-- The joint smooth local statement follows from the spatial derivative theorem. -/
theorem smoothLocalRegularityStatement_holds : SmoothLocalRegularityStatement :=
  smoothLocalRegularityStatement_holds_of_spatial_bounds smooth_timeVelocity_spatial_bounds

end LocalA

end HypoellipticAleksandrov.KineticAleksandrov

module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningWeakSource
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningGeTwo

/-! # The complete conditional flattened-profile source theorem

All representatives are explicit functions of the same jointly selected profile
witnesses. Their weak identities and source equation are proved here, rather than
assumed as an additional profile field.
-/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- The literal flattening has the complete selected weak-jet and source interface. -/
theorem flatProfile_source_of_profile {d : ℕ} (hd : 1 ≤ d) {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r) :
    FlatProfileSourceStatement h r := by
  obtain ⟨hmx, hmv, hmh⟩ := measurable_flatProfile_jets h r
  obtain ⟨hx, hv, hh⟩ := flatProfile_jets_locallyIntegrable_of_profile h r hr
  exact ⟨continuous_selectedFlatProfile h r, hmx, hmv, hmh,
    flatProfile_jets_compact_bound_of_profile h r hr, hx, hv, hh,
    flatProfile_jets_ae_of_profile h r hr, flatProfile_weak_of_profile hd h r hr,
    flatProfile_representatives_source h r, flatProfile_operator_ae_of_profile h r hr⟩

/-- The requested source-range facade for the complete conditional flattened-profile theorem. -/
theorem flatProfile_source {d : ℕ} (hd : 1 ≤ d) {alpha : ℝ}
    (_ha : 0 < alpha) (_ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r) :
    FlatProfileSourceStatement h r :=
  flatProfile_source_of_profile hd h r hr

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

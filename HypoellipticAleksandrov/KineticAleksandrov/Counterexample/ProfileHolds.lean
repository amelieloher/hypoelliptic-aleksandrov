module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileAssembly
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileGeTwoBridge
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarAssembly
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningSourceProfile
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningProperties
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.SourceNorm

/-! # The internally constructed shared profile and its unconditional flattening consequences -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Set

/-- The scalar and higher-dimensional constructions supply the complete shared profile. -/
theorem counterProfile_holds (d : ℕ) (hd : 1 ≤ d) (alpha : ℝ)
    (ha : 0 < alpha) (ha1 : alpha < 1) : CounterProfileStatement d alpha :=
  counterProfile_of_branches d hd alpha ha ha1
    (fun _ => counterProfileOne_exists alpha ha ha1)
    (fun hd2 => counterProfileGeTwo_holds d hd2 alpha ha ha1)

/-- The constructed profile has the complete literal flattened-source interface. -/
theorem flatProfile_source_holds (d : ℕ) (hd : 1 ≤ d) (alpha : ℝ)
    (ha : 0 < alpha) (ha1 : alpha < 1) (r : ℝ) (hr : 0 < r) :
    FlatProfileSourceStatement (counterProfile_holds d hd alpha ha ha1) r :=
  flatProfile_source_of_profile hd (counterProfile_holds d hd alpha ha ha1) r hr

/-- The constructed profile satisfies all small-scale flattening properties. -/
theorem flatProfile_properties (d : ℕ) (hd : 1 ≤ d) (alpha : ℝ)
    (ha : 0 < alpha) (ha1 : alpha < 1) :
    let h := counterProfile_holds d hd alpha ha ha1
    ∃ r0 : ℝ, 0 < r0 ∧ ∀ r : ℝ, 0 < r → r < r0 →
      Continuous (selectedFlatProfile h r) ∧
      (∀ q, profileFunction h q ≤ 1 →
        0 ≤ selectedFlatProfile h r q ∧ selectedFlatProfile h r q ≤ 1) ∧
      (∀ q, profileFunction h q = 1 → selectedFlatProfile h r q = 0) ∧
      (selectedFlatProfile h r =ᶠ[nhds 0]
        (fun _ => 1 - flatteningOffset * Real.rpow r alpha)) ∧
      (∀ q, 2 * Real.rpow r alpha ≤ profileFunction h q →
        selectedFlatProfile h r q = 1 - profileFunction h q) ∧
      selectedFlatProfile h r 0 = 1 - flatteningOffset * Real.rpow r alpha := by
  let h := counterProfile_holds d hd alpha ha ha1
  exact flatProfile_properties_of_profile ha h

/-- The constructed profile has the kinetic shell volume bound. -/
theorem shell_volume_bound_holds (d : ℕ) (hd : 1 ≤ d) (alpha : ℝ)
    (ha : 0 < alpha) (ha1 : alpha < 1) :
    let h := counterProfile_holds d hd alpha ha ha1
    ∃ C r₀ : ℝ, 0 < C ∧ 0 < r₀ ∧
      ∀ r : ℝ, 0 < r → r < r₀ →
        volume (profileShell (profileFunction h) alpha r) ≤
          ENNReal.ofReal (C * r ^ (4 * d)) := by
  let h := counterProfile_holds d hd alpha ha ha1
  exact shell_volume_bound_of_profile d alpha ha h

/-- The constructed source is nonnegative, shell-supported, and uniformly bounded. -/
theorem shell_source_bound_holds (d : ℕ) (hd : 1 ≤ d) (alpha : ℝ)
    (ha : 0 < alpha) (ha1 : alpha < 1) :
    let h := counterProfile_holds d hd alpha ha ha1
    ∃ K : ℝ, 0 < K ∧ ∀ r : ℝ, 0 < r → ∀ᵐ q ∂volume,
      0 ≤ flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha r q ∧
      flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha r q ≤
        K * Real.rpow r (alpha - 2) ∧
      (q ∉ profileShell (profileFunction h) alpha r →
        flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha r q = 0) := by
  let h := counterProfile_holds d hd alpha ha ha1
  exact shell_source_bound_of_profile ha ha1 h

/-- The constructed literal source satisfies the precise subcritical source norm bound. -/
theorem flat_source_eLpNorm_le (d : ℕ) (hd : 1 ≤ d) (alpha p : ℝ)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hp : 1 ≤ p) :
    let h := counterProfile_holds d hd alpha ha ha1
    ∃ C r₀ : ℝ, 0 < C ∧ 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      eLpNorm
        (flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha r)
        (ENNReal.ofReal p) (volume.restrict {q | profileFunction h q < 1}) ≤
          ENNReal.ofReal (C * Real.rpow r (alpha - 2 + 4 * (d : ℝ) / p)) := by
  let h := counterProfile_holds d hd alpha ha ha1
  exact flat_source_eLpNorm_le_of_profile d alpha p ha ha1 hp h

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

module

public import Mathlib.Topology.Order.Compact
public import HypoellipticAleksandrov.Parabolic.LocalClassical
public import HypoellipticAleksandrov.Parabolic.MinimumPrinciple

/-!
# Compact moving-domain parabolic minimum principle

This module turns the pointwise past-local minimum principle into a compact
moving-domain nonnegativity result.  A negative value attains a minimum on the
compact set; the boundary condition places that minimizer in the active domain,
where its past-relative neighborhood yields the pointwise operator contradiction.

## Main results

* `isNonnegativeOn_of_strict_parabolicOperator_of_compact`: strict positivity of
  the forward parabolic operator and nonnegative compact boundary data imply
  nonnegativity on the compact set.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter Set
open scoped MatrixOrder Topology

/-- A function with strictly positive forward parabolic operator on an active
past neighborhood cannot be negative on a compact set with nonnegative boundary data. -/
theorem isNonnegativeOn_of_strict_parabolicOperator_of_compact
    {d : ℕ} {K D : Set (TimeVelocity d)} {A : CoefficientField d}
    {w : TimeVelocity d → ℝ}
    (hDK : D ⊆ K)
    (hKcompact : IsCompact K)
    (hwcont : ContinuousOn w K)
    (hDpast : ∀ z ∈ D, D ∈ 𝓝[Set.Iic z.1 ×ˢ Set.univ] z)
    (hwDiff : ∀ z ∈ D, ContDiffAt ℝ 2 w z)
    (hApsd : ∀ z ∈ D, (coefficientAt A z).PosSemidef)
    (hPpos : ∀ z ∈ D, 0 < parabolicOperator A w z)
    (hboundary : ∀ z ∈ K \ D, 0 ≤ w z) :
    IsNonnegativeOn w K := by
  intro z hzK
  by_contra hneg
  have hwzneg : w z < 0 := lt_of_not_ge hneg
  obtain ⟨zMin, hzMinK, hzMin⟩ :=
    hKcompact.exists_isMinOn ⟨z, hzK⟩ hwcont
  have hwMinNeg : w zMin < 0 :=
    lt_of_le_of_lt (hzMin hzK) hwzneg
  have hzMinD : zMin ∈ D := by
    by_contra hzMinNotD
    exact (not_lt_of_ge (hboundary zMin ⟨hzMinK, hzMinNotD⟩)) hwMinNeg
  have hPastMin : IsLocalMinOn w (Set.Iic zMin.1 ×ˢ Set.univ) zMin := by
    show ∀ᶠ y in 𝓝[Set.Iic zMin.1 ×ˢ Set.univ] zMin, w zMin ≤ w y
    filter_upwards [hDpast zMin hzMinD] with y hyD
    exact hzMin (hDK hyD)
  have hPnonpos : parabolicOperator A w zMin ≤ 0 :=
    parabolicOperator_nonpos_of_past_localMin
      (hwDiff zMin hzMinD) hPastMin (hApsd zMin hzMinD)
  exact (not_lt_of_ge hPnonpos) (hPpos zMin hzMinD)

end HypoellipticAleksandrov.Parabolic

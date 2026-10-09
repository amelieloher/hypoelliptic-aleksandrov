module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.AdmissibilityAffine
import Mathlib.Tactic

/-! # Pointwise minimum principle supplied by source admissibility -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set

/-- Nonnegative kinetic boundary values give nonnegative values on the whole closed cylinder. -/
theorem admissible_nonnegative_of_boundary {d : ℕ} {A : FullKineticCoefficient d}
    {O : Set (KineticPoint d)} {p C_A : ℝ} {u : KineticPoint d → ℝ}
    (hu : IsAdmissibleSupersolution A O p C_A u)
    (P₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (hQ : closure (backwardCylinder P₀ R) ⊆ O)
    (hb : ∀ P ∈ kineticBoundary P₀ R, 0 ≤ u P) :
    ∀ P ∈ closure (backwardCylinder P₀ R), 0 ≤ u P := by
  have hcont := (hu.1.mono hQ).neg
  have hbounded := (isCompact_closure_backwardCylinder P₀ R hR).bddAbove_image hcont
  have hsup : sSup ((fun P => max (-u P) 0) '' kineticBoundary P₀ R) ≤ 0 := by
    apply csSup_le ((kineticBoundary_nonempty P₀ hR).image _)
    rintro _ ⟨P, hP, rfl⟩
    exact max_le (neg_nonpos.mpr (hb P hP)) le_rfl
  intro P hP
  have h := (le_sup_values hbounded hP).trans
    ((admissible_zero_comparison hu P₀ R hR hQ).trans hsup)
  change -u P ≤ 0 at h
  exact neg_nonpos.mp h

/-- Every constant lower bound on the kinetic boundary propagates to the closed cylinder. -/
theorem admissible_minimum {d : ℕ} {A : FullKineticCoefficient d}
    {O : Set (KineticPoint d)} {p C_A : ℝ} {u : KineticPoint d → ℝ}
    (hu : IsAdmissibleSupersolution A O p C_A u)
    (P₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (hQ : closure (backwardCylinder P₀ R) ⊆ O)
    (ell : ℝ) (hb : ∀ P ∈ kineticBoundary P₀ R, ell ≤ u P) :
    ∀ P ∈ closure (backwardCylinder P₀ R), ell ≤ u P := by
  have hv := admissible_pos_affine hu 1 (-ell) (by norm_num)
  have h := admissible_nonnegative_of_boundary hv P₀ R hR hQ (fun P hP => by
    have hp := hb P hP
    linarith)
  intro P hP
  have hp := h P hP
  linarith

end HypoellipticAleksandrov.KineticAleksandrov.Holder

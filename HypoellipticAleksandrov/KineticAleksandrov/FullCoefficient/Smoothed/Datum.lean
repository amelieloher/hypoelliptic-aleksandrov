module

public import HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient.Smoothed.Densities
import HypoellipticAleksandrov.LinearAlgebra.LoewnerEntryBound

/-!
# The smoothing datum

The hypotheses on `(Γ', B)` under which the time-averaged slices, the averaged coefficient and the
smoothed equation are built: `Γ'` is a finite measure on `ℝ × ℝ^{2d}` whose time marginal is
dominated by Lebesgue measure (the slices of the Green measure have mass at most one), and `B` is
a measurable, symmetric matrix field with Loewner bounds `λ I ≤ B ≤ Λ I`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

open MeasureTheory
open scoped MatrixOrder

variable {d : ℕ}

/-- The hypotheses on the pair `(Γ', B_t)` of the smoothed equation. -/
structure IsSmoothingDatum (lam Lam : ℝ) (Bt : ℝ → EvolutionAmbientState d → PDE.Mat d)
    (Γ' : Measure (ℝ × EvolutionAmbientState d)) : Prop where
  /-- Ellipticity constant. -/
  lam_pos : 0 < lam
  /-- Ordering of the ellipticity constants. -/
  lam_le : lam ≤ Lam
  /-- Finite total mass. -/
  finite : IsFiniteMeasure Γ'
  /-- The time marginal is dominated by Lebesgue measure. -/
  marginal : Γ'.map Prod.fst ≤ volume
  /-- Measurable entries. -/
  measurable : ∀ i j, Measurable fun q : ℝ × EvolutionAmbientState d => Bt q.1 q.2 i j
  /-- Symmetry. -/
  symm : ∀ t y, (Bt t y).IsSymm
  /-- Loewner bounds. -/
  loewner : ∀ t y, lam • (1 : PDE.Mat d) ≤ Bt t y ∧ Bt t y ≤ Lam • (1 : PDE.Mat d)

namespace IsSmoothingDatum

variable {lam Lam : ℝ} {Bt : ℝ → EvolutionAmbientState d → PDE.Mat d}
  {Γ' : Measure (ℝ × EvolutionAmbientState d)}

theorem lam_nonneg_Lam (hD : IsSmoothingDatum lam Lam Bt Γ') : 0 ≤ Lam :=
  hD.lam_pos.le.trans hD.lam_le

theorem abs_apply_le (hD : IsSmoothingDatum lam Lam Bt Γ') (t : ℝ)
    (y : EvolutionAmbientState d) (i j : Fin d) : |Bt t y i j| ≤ Lam :=
  HypoellipticAleksandrov.abs_apply_le_of_loewner hD.lam_pos (hD.loewner t y).1
    (hD.loewner t y).2 i j

end IsSmoothingDatum

end HypoellipticAleksandrov.KineticAleksandrov.FullCoefficient

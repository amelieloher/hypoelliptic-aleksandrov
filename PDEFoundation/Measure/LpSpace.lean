module

public import PDEFoundation.Ambient.HilbertVec
public import PDEFoundation.Measure.RestrictedVolume
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Quotient `L^p` spaces on restricted volume

This file names the scalar and internal Hilbert-vector `L^p` spaces used by
closed Sobolev graph constructions. Their measure is always volume restricted
to the displayed domain.
-/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace PDE

/-- Scalar `L^p(U)` modulo equality almost everywhere. -/
abbrev ScalarLp {d : ℕ} (U : Set (Vec d)) (p : ℝ≥0∞) :=
  MeasureTheory.Lp ℝ p (volumeOn U)

/-- `L^p(U)` fields valued in the internal Euclidean Hilbert realization.

Native vector representatives are recovered through the exact bridges in
`PDEFoundation.Ambient.HilbertVec`.
-/
abbrev HilbertVectorLp {d : ℕ} (U : Set (Vec d)) (p : ℝ≥0∞) :=
  MeasureTheory.Lp (HilbertVec d) p (volumeOn U)

end PDE

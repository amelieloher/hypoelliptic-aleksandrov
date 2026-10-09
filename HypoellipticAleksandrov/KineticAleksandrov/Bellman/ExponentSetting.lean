module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Order.Bounds.Basic

/-! # Admissible degrees of the homogeneous adjoint exponent

Source: companion paper, Appendix B.
The coefficient bounds are normalized to 1 and ratio. The invertible
position rescaling of Appendix B justifies that normalization.
These are the literal definitions; the exponent itself is defined
only after its well-definedness is proved.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set MeasureTheory

/-- The real position-velocity plane with its origin removed. No time coordinate is present. -/
abbrev BellmanPuncturedPlane := {q : ℝ × ℝ // q ≠ (0, 0)}

/-- The source's kinetic dilation, defined only for strictly positive scales. -/
def bellmanDilation (r : ℝ) (hr : 0 < r) :
    BellmanPuncturedPlane → BellmanPuncturedPlane := fun q =>
  ⟨(r ^ 3 * q.1.1, r * q.1.2), by
    intro h
    have hx : r ^ 3 * q.1.1 = 0 := congrArg Prod.fst h
    have hv : r * q.1.2 = 0 := congrArg Prod.snd h
    apply q.2
    apply Prod.ext
    · exact (mul_eq_zero.mp hx).resolve_left (pow_ne_zero 3 hr.ne')
    · exact (mul_eq_zero.mp hv).resolve_left hr.ne'⟩

/-- Literal measure-scaling meaning of density degree; no density is assumed to exist. -/
def HasBellmanDensityDegree (β : ℝ) (μ : Measure BellmanPuncturedPlane) : Prop :=
  ∀ (r : ℝ) (hr : 0 < r) (E : Set BellmanPuncturedPlane), MeasurableSet E →
    μ (bellmanDilation r hr '' E) = ENNReal.ofReal (r ^ (4 - β)) * μ E

/-- The stationary adjoint equation on the punctured plane, tested against smooth
compactly supported functions whose support avoids the origin. Both signs are positive
in the weak identity, corresponding to -∂X(vμ) + ∂vvη = 0. -/
def IsBellmanStationaryAdjointPair
    (μ η : Measure BellmanPuncturedPlane) : Prop :=
  ∀ (φ : ℝ × ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    tsupport φ ⊆ {q : ℝ × ℝ | q ≠ (0, 0)} →
      (∫ q, q.1.2 * fderiv ℝ φ q.1 (1, 0) ∂μ) +
        (∫ q, fderiv ℝ (fun z => fderiv ℝ φ z (0, 1)) q.1 (0, 1) ∂η) = 0

/-- The exact admissible degrees after normalizing the ellipticity interval to [1, ratio].
Positive Radon measures mean nonnegative Borel measures, inner regular and finite on
compact sets, on the actual punctured plane. The pair, not its density, is nonzero. -/
def bellmanAdmissibleDegrees (ratio : ℝ) : Set ℝ :=
  {β | ∃ μ η : Measure BellmanPuncturedPlane,
    IsFiniteMeasureOnCompacts μ ∧ Measure.InnerRegular μ ∧
    IsFiniteMeasureOnCompacts η ∧ Measure.InnerRegular η ∧
    (μ ≠ 0 ∨ η ≠ 0) ∧ μ ≤ η ∧ η ≤ ENNReal.ofReal ratio • μ ∧
    IsBellmanStationaryAdjointPair μ η ∧
    HasBellmanDensityDegree β μ ∧ HasBellmanDensityDegree β η}

end HypoellipticAleksandrov.KineticAleksandrov

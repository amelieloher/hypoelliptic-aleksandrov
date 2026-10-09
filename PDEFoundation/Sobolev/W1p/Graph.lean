module

public import PDEFoundation.Measure.LpSpace
public import PDEFoundation.Sobolev.WeakDerivative
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# The closed weak-gradient graph in `L^p`

For `1 ≤ p`, weak differentiation is encoded by continuous scalar constraints
on a product of quotient `L^p` spaces. Intersecting their kernels gives a
closed submodule, hence a complete subtype.

The vector-valued factor uses the internal Hilbert realization from
`PDEFoundation.Ambient.HilbertVec`; its coordinate and norm bridges keep the
native `PDE.Vec` convention at the project boundary.
-/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace PDE

open MeasureTheory

/-- The conjugate exponent of an exponent at least one is at least one. -/
instance factOneLeConjExponent (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Fact (1 ≤ p.conjExponent) :=
  ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩

namespace WeakTestFunction

/-- A bundled test function belongs to every scalar `L^r(U)`. -/
theorem memLp_toFun {d : ℕ} {U : Set (Vec d)}
    (φ : WeakTestFunction U) (r : ℝ≥0∞) :
    MemLp φ.toFun r (volumeOn U) :=
  (φ.contDiff.continuous.memLp_of_hasCompactSupport
    φ.hasCompactSupport).restrict U

/-- A directional derivative of a bundled test function belongs to every
scalar `L^r(U)`. -/
theorem memLp_partialDeriv {d : ℕ} {U : Set (Vec d)}
    (φ : WeakTestFunction U) (i : Fin d) (r : ℝ≥0∞) :
    MemLp (φ.partialDeriv i) r (volumeOn U) := by
  have hcontinuous :
      Continuous (φ.partialDeriv i) := by
    simpa only [WeakTestFunction.partialDeriv] using!
      (φ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcompact :
      HasCompactSupport (φ.partialDeriv i) := by
    simpa only [WeakTestFunction.partialDeriv] using!
      φ.hasCompactSupport.fderiv_apply (𝕜 := ℝ) (basisVec i)
  exact (hcontinuous.memLp_of_hasCompactSupport hcompact).restrict U

/-- A bundled test function as an element of scalar `L^r(U)`. -/
def toScalarLp {d : ℕ} {U : Set (Vec d)}
    (φ : WeakTestFunction U) (r : ℝ≥0∞) :
    ScalarLp U r :=
  (φ.memLp_toFun r).toLp φ.toFun

/-- A directional derivative of a bundled test function as an element of
scalar `L^r(U)`. -/
def partialDerivToScalarLp {d : ℕ} {U : Set (Vec d)}
    (φ : WeakTestFunction U) (i : Fin d) (r : ℝ≥0∞) :
    ScalarLp U r :=
  (φ.memLp_partialDeriv i r).toLp (φ.partialDeriv i)

theorem coeFn_toScalarLp {d : ℕ} {U : Set (Vec d)}
    (φ : WeakTestFunction U) (r : ℝ≥0∞) :
    ⇑(φ.toScalarLp r) =ᵐ[volumeOn U] φ.toFun :=
  (φ.memLp_toFun r).coeFn_toLp

theorem coeFn_partialDerivToScalarLp {d : ℕ} {U : Set (Vec d)}
    (φ : WeakTestFunction U) (i : Fin d) (r : ℝ≥0∞) :
    ⇑(φ.partialDerivToScalarLp i r) =ᵐ[volumeOn U]
      φ.partialDeriv i :=
  (φ.memLp_partialDeriv i r).coeFn_toLp

end WeakTestFunction

/-- The ambient product containing value and weak-gradient `L^p` classes. -/
abbrev WeakGradientLpPair {d : ℕ} (U : Set (Vec d)) (p : ℝ≥0∞) :=
  ScalarLp U p × HilbertVectorLp U p

/-- Coordinate projection on Hilbert-vector-valued `L^p` classes. -/
def hilbertVectorLpCoord {d : ℕ} (U : Set (Vec d)) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (i : Fin d) :
    HilbertVectorLp U p →L[ℝ] ScalarLp U p :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i).compLpL p (volumeOn U)

theorem coeFn_hilbertVectorLpCoord {d : ℕ} (U : Set (Vec d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (i : Fin d)
    (F : HilbertVectorLp U p) :
    ⇑(hilbertVectorLpCoord U p i F) =ᵐ[volumeOn U]
      fun x => F x i := by
  simpa only [hilbertVectorLpCoord] using!
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i).coeFn_compLpL F

/-- The scalar Hölder pairing between `L^p(U)` and `L^{p'}(U)`. -/
def scalarLpDualPairing {d : ℕ} (U : Set (Vec d)) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] :
    ScalarLp U p →L[ℝ] ScalarLp U p.conjExponent →L[ℝ] ℝ := by
  exact (ContinuousLinearMap.mul ℝ ℝ).lpPairing
    (volumeOn U) p p.conjExponent

theorem scalarLpDualPairing_apply_eq_integral
    {d : ℕ} (U : Set (Vec d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : ScalarLp U p) (g : ScalarLp U p.conjExponent) :
    scalarLpDualPairing U p f g =
      ∫ x, f x * g x ∂(volumeOn U) := by
  exact ContinuousLinearMap.lpPairing_eq_integral
    (ContinuousLinearMap.mul ℝ ℝ) f g

/-- The integration-by-parts constraint for coordinate `i` and test function
`φ`. Membership in its kernel says
`∫ u ∂ᵢφ + ∫ (Dᵢu) φ = 0`. -/
def weakGradientConstraint {d : ℕ} (U : Set (Vec d)) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (i : Fin d) (φ : WeakTestFunction U) :
    WeakGradientLpPair U p →L[ℝ] ℝ :=
  ((scalarLpDualPairing U p).flip
      (φ.partialDerivToScalarLp i p.conjExponent)).comp
      (ContinuousLinearMap.fst ℝ (ScalarLp U p) (HilbertVectorLp U p)) +
    ((scalarLpDualPairing U p).flip
      (φ.toScalarLp p.conjExponent)).comp
      ((hilbertVectorLpCoord U p i).comp
        (ContinuousLinearMap.snd ℝ (ScalarLp U p) (HilbertVectorLp U p)))

/-- Evaluation of a weak-gradient constraint as the two restricted-volume
integrals in the distributional integration-by-parts identity. -/
theorem weakGradientConstraint_apply_eq_integral
    {d : ℕ} (U : Set (Vec d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (i : Fin d) (φ : WeakTestFunction U) (v : WeakGradientLpPair U p) :
    weakGradientConstraint U p i φ v =
      (∫ x, v.1 x * φ.partialDeriv i x ∂(volumeOn U)) +
        ∫ x, v.2 x i * φ x ∂(volumeOn U) := by
  simp only [weakGradientConstraint, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  rw [scalarLpDualPairing_apply_eq_integral,
    scalarLpDualPairing_apply_eq_integral]
  congr 1
  · apply integral_congr_ae
    filter_upwards [φ.coeFn_partialDerivToScalarLp i p.conjExponent]
      with x hx
    rw [hx]
  · apply integral_congr_ae
    filter_upwards [coeFn_hilbertVectorLpCoord U p i v.2,
      φ.coeFn_toScalarLp p.conjExponent] with x hcoord hφ
    rw [hcoord, hφ]

/-- The closed submodule of value-gradient pairs satisfying every weak
integration-by-parts constraint. -/
def weakGradientGraph {d : ℕ} (U : Set (Vec d)) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] :
    ClosedSubmodule ℝ (WeakGradientLpPair U p) :=
  ⨅ i : Fin d, ⨅ φ : WeakTestFunction U,
    (⊥ : ClosedSubmodule ℝ ℝ).comap (weakGradientConstraint U p i φ)

/-- Membership in the weak-gradient graph is exactly vanishing of every
coordinate test-function constraint. -/
theorem mem_weakGradientGraph_iff {d : ℕ} {U : Set (Vec d)}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (v : WeakGradientLpPair U p) :
    v ∈ weakGradientGraph U p ↔
      ∀ i : Fin d, ∀ φ : WeakTestFunction U,
        weakGradientConstraint U p i φ v = 0 := by
  simp only [weakGradientGraph, ClosedSubmodule.mem_iInf,
    ClosedSubmodule.mem_comap, ClosedSubmodule.mem_bot]

/-- Integral form of membership in the closed weak-gradient graph. -/
theorem mem_weakGradientGraph_iff_integral
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (v : WeakGradientLpPair U p) :
    v ∈ weakGradientGraph U p ↔
      ∀ i : Fin d, ∀ φ : WeakTestFunction U,
        (∫ x, v.1 x * φ.partialDeriv i x ∂(volumeOn U)) +
          ∫ x, v.2 x i * φ x ∂(volumeOn U) = 0 := by
  rw [mem_weakGradientGraph_iff]
  constructor
  · intro h i φ
    rw [← weakGradientConstraint_apply_eq_integral U p i φ v]
    exact h i φ
  · intro h i φ
    rw [weakGradientConstraint_apply_eq_integral]
    exact h i φ

/-- Complete quotient-level `W^{1,p}` carrier, realized as the closed
weak-gradient graph. -/
abbrev W1pGraph {d : ℕ} (U : Set (Vec d)) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] :=
  ↥(weakGradientGraph U p).toSubmodule

noncomputable instance w1pGraphCompleteSpace {d : ℕ}
    (U : Set (Vec d)) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    CompleteSpace (W1pGraph U p) :=
  (weakGradientGraph U p).isClosed.completeSpace_coe

namespace W1pGraph

/-- The inherited graph norm is the product maximum, not an additive
value-plus-gradient norm. -/
theorem norm_eq_max {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (v : W1pGraph U p) :
    ‖v‖ = max ‖v.1.1‖ ‖v.1.2‖ :=
  rfl

/-- Every element of the graph satisfies every weak derivative constraint. -/
theorem constraint_eq_zero {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (v : W1pGraph U p)
    (i : Fin d) (φ : WeakTestFunction U) :
    weakGradientConstraint U p i φ v.1 = 0 :=
  (mem_weakGradientGraph_iff v.1).1 v.2 i φ

end W1pGraph

end PDE

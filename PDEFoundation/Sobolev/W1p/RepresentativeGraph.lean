module

public import PDEFoundation.Sobolev.W1p.EuclideanGradient
public import PDEFoundation.Sobolev.W1p.Graph

/-!
# From Sobolev representatives to the closed weak-gradient graph

This file packages a concrete scalar representative and its native coordinate
gradient into the quotient `L^p` product used by `PDE.W1pGraph`.  Graph
membership is proved from the literal integral characterization
`PDE.mem_weakGradientGraph_iff_integral`; no distributional condition is
hidden in a new assumption.
-/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace PDE

open MeasureTheory

/-- The quotient `L^p` value-gradient pair associated with concrete
representatives. -/
def weakGradientLpPairOfRepresentatives
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemLpOn U p u) (hDu : GradMemLpOn U p Du) :
    WeakGradientLpPair U p :=
  (hu.toScalarLp, hDu.toHilbertVectorLp)

/-- The value component of
`PDE.weakGradientLpPairOfRepresentatives` has the original representative. -/
theorem coeFn_weakGradientLpPairOfRepresentatives_fst
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemLpOn U p u) (hDu : GradMemLpOn U p Du) :
    ⇑(weakGradientLpPairOfRepresentatives hu hDu).1
      =ᵐ[volumeOn U] u :=
  hu.coeFn_toScalarLp

/-- The gradient component of
`PDE.weakGradientLpPairOfRepresentatives` has the original Euclidean Hilbert
lift as representative. -/
theorem coeFn_weakGradientLpPairOfRepresentatives_snd
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemLpOn U p u) (hDu : GradMemLpOn U p Du) :
    ⇑(weakGradientLpPairOfRepresentatives hu hDu).2
      =ᵐ[volumeOn U] toHilbertVecField Du :=
  hDu.coeFn_toHilbertVectorLp

/-- Coordinatewise a.e. representative identity for the gradient component
of `PDE.weakGradientLpPairOfRepresentatives`. -/
theorem coeFn_weakGradientLpPairOfRepresentatives_snd_apply
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemLpOn U p u) (hDu : GradMemLpOn U p Du)
    (i : Fin d) :
    (fun x => (weakGradientLpPairOfRepresentatives hu hDu).2 x i)
      =ᵐ[volumeOn U] fun x => Du x i :=
  hDu.coeFn_toHilbertVectorLp_apply i

/-- Concrete weak-gradient representatives determine an element of the
closed weak-gradient graph. -/
theorem weakGradientLpPairOfRepresentatives_mem_weakGradientGraph
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    [Fact (1 ≤ p)]
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemLpOn U p u) (hDu : GradMemLpOn U p Du)
    (hweak : HasWeakGradientOn U u Du) :
    weakGradientLpPairOfRepresentatives hu hDu ∈
      weakGradientGraph U p := by
  rw [mem_weakGradientGraph_iff_integral]
  intro i φ
  have hvalueIntegral :
      (∫ x,
          (weakGradientLpPairOfRepresentatives hu hDu).1 x *
            φ.partialDeriv i x ∂(volumeOn U)) =
        ∫ x, u x * φ.partialDeriv i x ∂(volumeOn U) := by
    apply integral_congr_ae
    filter_upwards
      [coeFn_weakGradientLpPairOfRepresentatives_fst hu hDu]
      with x hx
    rw [hx]
  have hgradIntegral :
      (∫ x,
          (weakGradientLpPairOfRepresentatives hu hDu).2 x i *
            φ x ∂(volumeOn U)) =
        ∫ x, Du x i * φ x ∂(volumeOn U) := by
    apply integral_congr_ae
    filter_upwards
      [coeFn_weakGradientLpPairOfRepresentatives_snd_apply hu hDu i]
      with x hx
    rw [hx]
  have hweakTest :
      (∫ x, u x * φ.partialDeriv i x ∂(volumeOn U)) =
        -∫ x, Du x i * φ x ∂(volumeOn U) := by
    exact
      (hasWeakPartialDerivOn_iff_forall_testFunction.mp
        (hweak i)) φ
  rw [hvalueIntegral, hgradIntegral]
  exact eq_neg_iff_add_eq_zero.mp hweakTest

/-- Membership of a representative pair in the closed weak-gradient graph
recovers the raw distributional weak-gradient identity.  Together with
`weakGradientLpPairOfRepresentatives_mem_weakGradientGraph`, this is the exact
bridge between representative-level weak derivatives and the quotient
closed-graph carrier. -/
theorem hasWeakGradientOn_of_weakGradientLpPairOfRepresentatives_mem
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    [Fact (1 ≤ p)]
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemLpOn U p u) (hDu : GradMemLpOn U p Du)
    (hmem :
      weakGradientLpPairOfRepresentatives hu hDu ∈
        weakGradientGraph U p) :
    HasWeakGradientOn U u Du := by
  intro i
  rw [hasWeakPartialDerivOn_iff_forall_testFunction]
  intro φ
  have hconstraint :=
    (mem_weakGradientGraph_iff_integral
      (weakGradientLpPairOfRepresentatives hu hDu)).mp
      hmem i φ
  have hvalueIntegral :
      (∫ x,
          (weakGradientLpPairOfRepresentatives hu hDu).1 x *
            φ.partialDeriv i x ∂(volumeOn U)) =
        ∫ x, u x * φ.partialDeriv i x ∂(volumeOn U) := by
    apply integral_congr_ae
    filter_upwards
      [coeFn_weakGradientLpPairOfRepresentatives_fst hu hDu]
      with x hx
    rw [hx]
  have hgradIntegral :
      (∫ x,
          (weakGradientLpPairOfRepresentatives hu hDu).2 x i *
            φ x ∂(volumeOn U)) =
        ∫ x, Du x i * φ x ∂(volumeOn U) := by
    apply integral_congr_ae
    filter_upwards
      [coeFn_weakGradientLpPairOfRepresentatives_snd_apply
        hu hDu i]
      with x hx
    rw [hx]
  rw [hvalueIntegral, hgradIntegral] at hconstraint
  exact eq_neg_iff_add_eq_zero.mpr hconstraint

/-- Package concrete weak-gradient representatives as an element of the
complete quotient-level `W^{1,p}` graph. -/
def w1pGraphOfRepresentatives
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    [Fact (1 ≤ p)]
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemLpOn U p u) (hDu : GradMemLpOn U p Du)
    (hweak : HasWeakGradientOn U u Du) :
    W1pGraph U p :=
  ⟨weakGradientLpPairOfRepresentatives hu hDu,
    weakGradientLpPairOfRepresentatives_mem_weakGradientGraph
      hu hDu hweak⟩

/-- The value component of `PDE.w1pGraphOfRepresentatives` agrees a.e. with
the concrete value representative. -/
theorem coeFn_w1pGraphOfRepresentatives_fst
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    [Fact (1 ≤ p)]
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemLpOn U p u) (hDu : GradMemLpOn U p Du)
    (hweak : HasWeakGradientOn U u Du) :
    ⇑(w1pGraphOfRepresentatives hu hDu hweak).1.1
      =ᵐ[volumeOn U] u :=
  coeFn_weakGradientLpPairOfRepresentatives_fst hu hDu

/-- The gradient component of `PDE.w1pGraphOfRepresentatives` agrees a.e.
with the Euclidean Hilbert lift of the concrete gradient. -/
theorem coeFn_w1pGraphOfRepresentatives_snd
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    [Fact (1 ≤ p)]
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemLpOn U p u) (hDu : GradMemLpOn U p Du)
    (hweak : HasWeakGradientOn U u Du) :
    ⇑(w1pGraphOfRepresentatives hu hDu hweak).1.2
      =ᵐ[volumeOn U] toHilbertVecField Du :=
  coeFn_weakGradientLpPairOfRepresentatives_snd hu hDu

/-- Coordinatewise a.e. representative identity for the gradient component
of `PDE.w1pGraphOfRepresentatives`. -/
theorem coeFn_w1pGraphOfRepresentatives_snd_apply
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    [Fact (1 ≤ p)]
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (hu : MemLpOn U p u) (hDu : GradMemLpOn U p Du)
    (hweak : HasWeakGradientOn U u Du) (i : Fin d) :
    (fun x => (w1pGraphOfRepresentatives hu hDu hweak).1.2 x i)
      =ᵐ[volumeOn U] fun x => Du x i :=
  coeFn_weakGradientLpPairOfRepresentatives_snd_apply hu hDu i

namespace W1pFunction

/-- Send a concrete representative-level Sobolev function to the complete
closed-graph carrier. -/
def toW1pGraph
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (u : W1pFunction U p) :
    W1pGraph U p :=
  w1pGraphOfRepresentatives u.memLp u.gradMemLp u.hasWeakGradient

/-- The value component of `PDE.W1pFunction.toW1pGraph` agrees a.e. with the
original concrete value representative. -/
theorem coeFn_toW1pGraph_fst
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (u : W1pFunction U p) :
    ⇑u.toW1pGraph.1.1 =ᵐ[volumeOn U] u.toFun :=
  coeFn_w1pGraphOfRepresentatives_fst
    u.memLp u.gradMemLp u.hasWeakGradient

/-- The gradient component of `PDE.W1pFunction.toW1pGraph` agrees a.e. with
the Euclidean Hilbert lift of the original native gradient. -/
theorem coeFn_toW1pGraph_snd
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (u : W1pFunction U p) :
    ⇑u.toW1pGraph.1.2 =ᵐ[volumeOn U] toHilbertVecField u.grad :=
  coeFn_w1pGraphOfRepresentatives_snd
    u.memLp u.gradMemLp u.hasWeakGradient

/-- Coordinatewise a.e. representative identity for the gradient component
of `PDE.W1pFunction.toW1pGraph`. -/
theorem coeFn_toW1pGraph_snd_apply
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (u : W1pFunction U p) (i : Fin d) :
    (fun x => u.toW1pGraph.1.2 x i) =ᵐ[volumeOn U]
      fun x => u.grad x i :=
  coeFn_w1pGraphOfRepresentatives_snd_apply
    u.memLp u.gradMemLp u.hasWeakGradient i

end W1pFunction

end PDE

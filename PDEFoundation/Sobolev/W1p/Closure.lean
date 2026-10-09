module

public import PDEFoundation.Measure.FiniteVectorConvergence
public import PDEFoundation.Sobolev.W1p.RepresentativeGraph

/-!
# Closure of representative weak gradients under `L^p` convergence

This file exposes the closed-graph limit principle behind Sobolev
composition and truncation arguments.  If values and every native gradient
coordinate converge in `L^p`, then a limit of weak-gradient pairs is again a
weak-gradient pair.

The proof passes through the quotient `L^p` closed graph.  The native gradient
is lifted internally to `HilbertVec`; the public assumptions and conclusion
remain on `Vec d`, and coordinatewise convergence is converted to the exact
Euclidean-gradient norm without a dimension-dependent loss.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE

open Filter MeasureTheory

/-- Weak gradients are closed under value and coordinatewise gradient
convergence in `L^p`, for every exponent `p ≥ 1`. -/
theorem HasWeakGradientOn.of_tendsto_eLpNorm
    {d : ℕ} {U : Set (Vec d)} {p : ℝ≥0∞}
    [Fact (1 ≤ p)]
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    {uSeq : ℕ → Vec d → ℝ}
    {DuSeq : ℕ → Vec d → Vec d}
    (hu : MemLpOn U p u) (hDu : GradMemLpOn U p Du)
    (huSeq : ∀ n, MemLpOn U p (uSeq n))
    (hDuSeq : ∀ n, GradMemLpOn U p (DuSeq n))
    (hweak :
      ∀ n, HasWeakGradientOn U (uSeq n) (DuSeq n))
    (hValue :
      Tendsto
        (fun n =>
          eLpNorm (uSeq n - u) p (volumeOn U))
        atTop (𝓝 0))
    (hGradient :
      ∀ i,
        Tendsto
          (fun n =>
            eLpNorm
              (fun x => DuSeq n x i - Du x i)
              p (volumeOn U))
          atTop (𝓝 0)) :
    HasWeakGradientOn U u Du := by
  have hValueLp :
      Tendsto
        (fun n => (huSeq n).toScalarLp)
        atTop (𝓝 hu.toScalarLp) := by
    exact
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
        uSeq huSeq u hu).mpr hValue
  have hGradientEuclidean :
      Tendsto
        (fun n =>
          eLpNorm
            (fun x =>
              vecEuclideanNorm (DuSeq n x - Du x))
            p (volumeOn U))
        atTop (𝓝 0) := by
    apply
      tendsto_eLpNorm_vecEuclideanNorm_sub_zero_of_coordinate
        Fact.out
    · intro n i
      exact
        ((hDuSeq n i).aestronglyMeasurable.sub
          (hDu i).aestronglyMeasurable)
    · exact hGradient
  have hGradientHilbert :
      Tendsto
        (fun n =>
          eLpNorm
            (toHilbertVecField (DuSeq n) -
              toHilbertVecField Du)
            p (volumeOn U))
        atTop (𝓝 0) := by
    have hEq : ∀ n,
        eLpNorm (toHilbertVecField fun x => DuSeq n x - Du x) p (volumeOn U) =
          eLpNorm (fun x => vecEuclideanNorm (DuSeq n x - Du x)) p (volumeOn U) :=
      fun n => eLpNorm_toHilbertVecField_eq _ _ _
        (aemeasurable_pi_iff.2 fun i =>
          ((hDuSeq n i).aestronglyMeasurable.sub
            (hDu i).aestronglyMeasurable).aemeasurable).aestronglyMeasurable
    simpa only [toHilbertVecField_sub, hEq] using
      hGradientEuclidean
  have hGradientLp :
      Tendsto
        (fun n => (hDuSeq n).toHilbertVectorLp)
        atTop (𝓝 hDu.toHilbertVectorLp) := by
    exact
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
        (fun n => toHilbertVecField (DuSeq n))
        (fun n =>
          gradMemLpOn_iff_memLp_toHilbertVecField.mp
            (hDuSeq n))
        (toHilbertVecField Du)
        (gradMemLpOn_iff_memLp_toHilbertVecField.mp hDu)).mpr
        hGradientHilbert
  have hPair :
      Tendsto
        (fun n =>
          weakGradientLpPairOfRepresentatives
            (huSeq n) (hDuSeq n))
        atTop
        (𝓝
          (weakGradientLpPairOfRepresentatives hu hDu)) := by
    simpa only [weakGradientLpPairOfRepresentatives] using
      hValueLp.prodMk_nhds hGradientLp
  have hPairMem :
      weakGradientLpPairOfRepresentatives hu hDu ∈
        weakGradientGraph U p := by
    exact
      (weakGradientGraph U p).isClosed.mem_of_tendsto
        hPair
        (Eventually.of_forall fun n =>
          weakGradientLpPairOfRepresentatives_mem_weakGradientGraph
            (huSeq n) (hDuSeq n) (hweak n))
  exact
    hasWeakGradientOn_of_weakGradientLpPairOfRepresentatives_mem
      hu hDu hPairMem

end PDE

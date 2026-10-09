module

public import PDEFoundation.Geometry.EuclideanBall.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# Topology of round balls on native vectors

Continuity, openness, closedness, and compactness for the explicit round
balls. Any occurrence of the inherited metric below is explicitly a
finite-product supremum-metric comparison.
-/

@[expose] public section

open Set

namespace PDE

theorem contDiff_vecNormSq {d : ℕ} :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => vecNormSq x) := by
  unfold vecNormSq vecDot
  exact ContDiff.sum (s := Finset.univ) fun i _hi =>
    (contDiff_apply ℝ ℝ i).mul (contDiff_apply ℝ ℝ i)

theorem continuous_vecNormSq {d : ℕ} :
    Continuous (fun x : Vec d => vecNormSq x) :=
  contDiff_vecNormSq.continuous

theorem continuous_vecEuclideanNorm {d : ℕ} :
    Continuous (fun x : Vec d => vecEuclideanNorm x) := by
  exact Real.continuous_sqrt.comp continuous_vecNormSq

theorem measurable_vecEuclideanNorm {d : ℕ} :
    Measurable (fun x : Vec d => vecEuclideanNorm x) :=
  continuous_vecEuclideanNorm.measurable

theorem contDiff_euclideanSqDist_left {d : ℕ} (x₀ : Vec d) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec d => euclideanSqDist x x₀) := by
  unfold euclideanSqDist
  exact contDiff_vecNormSq.comp (contDiff_id.sub contDiff_const)

theorem continuous_euclideanSqDist_left {d : ℕ} (x₀ : Vec d) :
    Continuous (fun x : Vec d => euclideanSqDist x x₀) :=
  (contDiff_euclideanSqDist_left x₀).continuous

theorem isOpen_euclideanBall {d : ℕ} (x₀ : Vec d) (R : ℝ) :
    IsOpen (euclideanBall x₀ R) := by
  change IsOpen
    ((fun x : Vec d => euclideanSqDist x x₀) ⁻¹' Iio (R ^ 2))
  exact isOpen_Iio.preimage (continuous_euclideanSqDist_left x₀)

theorem measurableSet_euclideanBall {d : ℕ}
    (x₀ : Vec d) (R : ℝ) :
    MeasurableSet (euclideanBall x₀ R) :=
  (isOpen_euclideanBall x₀ R).measurableSet

theorem isClosed_euclideanClosedBall {d : ℕ}
    (x₀ : Vec d) (R : ℝ) :
    IsClosed (euclideanClosedBall x₀ R) := by
  change IsClosed
    ((fun x : Vec d => euclideanSqDist x x₀) ⁻¹' Iic (R ^ 2))
  exact isClosed_Iic.preimage (continuous_euclideanSqDist_left x₀)

theorem measurableSet_euclideanClosedBall {d : ℕ}
    (x₀ : Vec d) (R : ℝ) :
    MeasurableSet (euclideanClosedBall x₀ R) :=
  (isClosed_euclideanClosedBall x₀ R).measurableSet

theorem isClosed_euclideanSphere {d : ℕ}
    (x₀ : Vec d) (R : ℝ) :
    IsClosed (euclideanSphere x₀ R) := by
  change IsClosed
    ((fun x : Vec d => euclideanSqDist x x₀) ⁻¹' {R ^ 2})
  exact isClosed_singleton.preimage
    (continuous_euclideanSqDist_left x₀)

theorem sq_coord_sub_le_euclideanSqDist {d : ℕ}
    (x y : Vec d) (i : Fin d) :
    (x i - y i) ^ 2 ≤ euclideanSqDist x y := by
  simpa [euclideanSqDist, Pi.sub_apply] using
    sq_apply_le_vecNormSq (x - y) i

/-- A round closed ball is contained in the inherited supremum-metric
closed ball with the same nonnegative radius. -/
theorem euclideanClosedBall_subset_supClosedBall {d : ℕ}
    {x₀ : Vec d} {R : ℝ} (hR : 0 ≤ R) :
    euclideanClosedBall x₀ R ⊆ Metric.closedBall x₀ R := by
  intro x hx
  rw [Metric.mem_closedBall, dist_pi_le_iff hR]
  intro i
  have hsqi : (x i - x₀ i) ^ 2 ≤ R ^ 2 :=
    (sq_coord_sub_le_euclideanSqDist x x₀ i).trans hx
  have habs : |x i - x₀ i| ≤ R :=
    abs_le_of_sq_le_sq hsqi hR
  simpa [Real.dist_eq, abs_sub_comm] using habs

/-- A round open ball is contained in the inherited supremum-metric open
ball with the same positive radius. -/
theorem euclideanBall_subset_supBall {d : ℕ}
    {x₀ : Vec d} {R : ℝ} (hR : 0 < R) :
    euclideanBall x₀ R ⊆ Metric.ball x₀ R := by
  intro x hx
  rw [Metric.mem_ball, dist_pi_lt_iff hR]
  intro i
  have hsqi : (x i - x₀ i) ^ 2 < R ^ 2 :=
    (sq_coord_sub_le_euclideanSqDist x x₀ i).trans_lt hx
  have habs : |x i - x₀ i| < R :=
    abs_lt_of_sq_lt_sq hsqi hR.le
  simpa [Real.dist_eq, abs_sub_comm] using habs

theorem isCompact_euclideanClosedBall {d : ℕ}
    (x₀ : Vec d) {R : ℝ} (hR : 0 ≤ R) :
    IsCompact (euclideanClosedBall x₀ R) :=
  (ProperSpace.isCompact_closedBall x₀ R).of_isClosed_subset
    (isClosed_euclideanClosedBall x₀ R)
    (euclideanClosedBall_subset_supClosedBall hR)

end PDE

module

public import HypoellipticAleksandrov.Ambient.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Parabolic time--velocity geometry

This module fixes the explicit Euclidean time--velocity cylinders and their
forward parabolic boundary. The terminal open-ball face is deliberately not a
boundary component.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

/-- Time--velocity points in dimension `d`. -/
abbrev TimeVelocity (d : ℕ) := ℝ × PDE.Vec d

/-- The analytic interior `(0, T) × B₁(y₀)` of a parabolic cylinder. -/
def parabolicInterior {d : ℕ} (T : ℝ) (y₀ : PDE.Vec d) : Set (TimeVelocity d) :=
  Set.Ioo 0 T ×ˢ PDE.euclideanBall y₀ 1

/-- The forward-reachable cylinder `(0, T] × B₁(y₀)`. -/
def parabolicReachable {d : ℕ} (T : ℝ) (y₀ : PDE.Vec d) : Set (TimeVelocity d) :=
  Set.Ioc 0 T ×ˢ PDE.euclideanBall y₀ 1

/-- The compact closure `[0, T] × \overline{B₁(y₀)}` of a parabolic cylinder. -/
def closedParabolicCylinder {d : ℕ} (T : ℝ) (y₀ : PDE.Vec d) :
    Set (TimeVelocity d) :=
  Set.Icc 0 T ×ˢ PDE.euclideanClosedBall y₀ 1

/-- The initial boundary face `{0} × \overline{B₁(y₀)}`. -/
def initialParabolicBoundary {d : ℕ} (y₀ : PDE.Vec d) : Set (TimeVelocity d) :=
  ({0} : Set ℝ) ×ˢ PDE.euclideanClosedBall y₀ 1

/-- The lateral boundary face `[0, T] × ∂B₁(y₀)`. -/
def lateralParabolicBoundary {d : ℕ} (T : ℝ) (y₀ : PDE.Vec d) :
    Set (TimeVelocity d) :=
  Set.Icc 0 T ×ˢ PDE.euclideanSphere y₀ 1

/-- The forward parabolic boundary: precisely its initial and lateral faces. -/
def forwardParabolicBoundary {d : ℕ} (T : ℝ) (y₀ : PDE.Vec d) :
    Set (TimeVelocity d) :=
  initialParabolicBoundary y₀ ∪ lateralParabolicBoundary T y₀

/-- Membership in the analytic parabolic interior. -/
@[simp] theorem mem_parabolicInterior_iff {d : ℕ} {T t : ℝ} {y₀ v : PDE.Vec d} :
    (t, v) ∈ parabolicInterior T y₀ ↔
      0 < t ∧ t < T ∧ v ∈ PDE.euclideanBall y₀ 1 := by
  constructor
  · rintro ⟨⟨hzero, hT⟩, hv⟩
    exact ⟨hzero, hT, hv⟩
  · rintro ⟨hzero, hT, hv⟩
    exact ⟨⟨hzero, hT⟩, hv⟩

/-- Membership in the forward-reachable parabolic cylinder. -/
@[simp] theorem mem_parabolicReachable_iff {d : ℕ} {T t : ℝ} {y₀ v : PDE.Vec d} :
    (t, v) ∈ parabolicReachable T y₀ ↔
      0 < t ∧ t ≤ T ∧ v ∈ PDE.euclideanBall y₀ 1 := by
  constructor
  · rintro ⟨⟨hzero, hT⟩, hv⟩
    exact ⟨hzero, hT, hv⟩
  · rintro ⟨hzero, hT, hv⟩
    exact ⟨⟨hzero, hT⟩, hv⟩

/-- Membership in the closed parabolic cylinder. -/
@[simp] theorem mem_closedParabolicCylinder_iff {d : ℕ} {T t : ℝ} {y₀ v : PDE.Vec d} :
    (t, v) ∈ closedParabolicCylinder T y₀ ↔
      0 ≤ t ∧ t ≤ T ∧ v ∈ PDE.euclideanClosedBall y₀ 1 := by
  constructor
  · rintro ⟨⟨hzero, hT⟩, hv⟩
    exact ⟨hzero, hT, hv⟩
  · rintro ⟨hzero, hT, hv⟩
    exact ⟨⟨hzero, hT⟩, hv⟩

/-- Membership in the initial parabolic boundary face. -/
@[simp] theorem mem_initialParabolicBoundary_iff {d : ℕ} {t : ℝ} {y₀ v : PDE.Vec d} :
    (t, v) ∈ initialParabolicBoundary y₀ ↔
      t = 0 ∧ v ∈ PDE.euclideanClosedBall y₀ 1 := by
  simp [initialParabolicBoundary]

/-- Membership in the lateral parabolic boundary face. -/
@[simp] theorem mem_lateralParabolicBoundary_iff {d : ℕ} {T t : ℝ} {y₀ v : PDE.Vec d} :
    (t, v) ∈ lateralParabolicBoundary T y₀ ↔
      0 ≤ t ∧ t ≤ T ∧ v ∈ PDE.euclideanSphere y₀ 1 := by
  constructor
  · rintro ⟨⟨hzero, hT⟩, hv⟩
    exact ⟨hzero, hT, hv⟩
  · rintro ⟨hzero, hT, hv⟩
    exact ⟨⟨hzero, hT⟩, hv⟩

/-- Membership in the forward parabolic boundary. -/
@[simp] theorem mem_forwardParabolicBoundary_iff {d : ℕ} {T t : ℝ} {y₀ v : PDE.Vec d} :
    (t, v) ∈ forwardParabolicBoundary T y₀ ↔
      (t = 0 ∧ v ∈ PDE.euclideanClosedBall y₀ 1) ∨
        (0 ≤ t ∧ t ≤ T ∧ v ∈ PDE.euclideanSphere y₀ 1) := by
  simp [forwardParabolicBoundary]

/-- The analytic parabolic interior is measurable. -/
theorem measurableSet_parabolicInterior {d : ℕ} (T : ℝ) (y₀ : PDE.Vec d) :
    MeasurableSet (parabolicInterior T y₀) :=
  measurableSet_Ioo.prod (PDE.measurableSet_euclideanBall y₀ 1)

/-- The forward-reachable parabolic cylinder is measurable. -/
theorem measurableSet_parabolicReachable {d : ℕ} (T : ℝ) (y₀ : PDE.Vec d) :
    MeasurableSet (parabolicReachable T y₀) :=
  measurableSet_Ioc.prod (PDE.measurableSet_euclideanBall y₀ 1)

/-- The closed parabolic cylinder is measurable. -/
theorem measurableSet_closedParabolicCylinder {d : ℕ} (T : ℝ) (y₀ : PDE.Vec d) :
    MeasurableSet (closedParabolicCylinder T y₀) :=
  measurableSet_Icc.prod (PDE.measurableSet_euclideanClosedBall y₀ 1)

/-- The initial parabolic boundary face is measurable. -/
theorem measurableSet_initialParabolicBoundary {d : ℕ} (y₀ : PDE.Vec d) :
    MeasurableSet (initialParabolicBoundary y₀) :=
  (MeasurableSet.singleton 0).prod (PDE.measurableSet_euclideanClosedBall y₀ 1)

/-- The lateral parabolic boundary face is measurable. -/
theorem measurableSet_lateralParabolicBoundary {d : ℕ} (T : ℝ) (y₀ : PDE.Vec d) :
    MeasurableSet (lateralParabolicBoundary T y₀) :=
  measurableSet_Icc.prod (PDE.isClosed_euclideanSphere y₀ 1).measurableSet

/-- The forward parabolic boundary is measurable. -/
theorem measurableSet_forwardParabolicBoundary {d : ℕ} (T : ℝ) (y₀ : PDE.Vec d) :
    MeasurableSet (forwardParabolicBoundary T y₀) :=
  (measurableSet_initialParabolicBoundary y₀).union
    (measurableSet_lateralParabolicBoundary T y₀)

/-- The closed parabolic cylinder is compact. -/
theorem isCompact_closedParabolicCylinder {d : ℕ} (T : ℝ) (y₀ : PDE.Vec d) :
    IsCompact (closedParabolicCylinder T y₀) :=
  isCompact_Icc.prod (PDE.isCompact_euclideanClosedBall y₀ (by norm_num))

/-- A closed parabolic cylinder is nonempty when its time height is nonnegative. -/
theorem closedParabolicCylinder_nonempty {d : ℕ} {T : ℝ} {y₀ : PDE.Vec d}
    (hT : 0 ≤ T) :
    (closedParabolicCylinder T y₀).Nonempty := by
  refine ⟨(0, y₀), ?_⟩
  rw [mem_closedParabolicCylinder_iff]
  refine ⟨le_rfl, hT, ?_⟩
  change PDE.euclideanSqDist y₀ y₀ ≤ 1 ^ 2
  simp

/-- The analytic interior is contained in the closed parabolic cylinder. -/
theorem parabolicInterior_subset_closedParabolicCylinder {d : ℕ} (T : ℝ)
    (y₀ : PDE.Vec d) :
    parabolicInterior T y₀ ⊆ closedParabolicCylinder T y₀ := by
  intro p hp
  rcases mem_parabolicInterior_iff.mp hp with ⟨hzero, hT, hv⟩
  exact mem_closedParabolicCylinder_iff.mpr
    ⟨hzero.le, hT.le, PDE.euclideanBall_subset_euclideanClosedBall y₀ 1 hv⟩

/-- The forward-reachable cylinder is contained in the closed parabolic cylinder. -/
theorem parabolicReachable_subset_closedParabolicCylinder {d : ℕ} (T : ℝ)
    (y₀ : PDE.Vec d) :
    parabolicReachable T y₀ ⊆ closedParabolicCylinder T y₀ := by
  intro p hp
  rcases mem_parabolicReachable_iff.mp hp with ⟨hzero, hT, hv⟩
  exact mem_closedParabolicCylinder_iff.mpr
    ⟨hzero.le, hT, PDE.euclideanBall_subset_euclideanClosedBall y₀ 1 hv⟩

/-- A terminal open-ball point is not on the forward parabolic boundary. -/
theorem terminalInterior_not_mem_forwardParabolicBoundary {d : ℕ} {T : ℝ}
    {y₀ v : PDE.Vec d} (hT : 0 < T) (hv : v ∈ PDE.euclideanBall y₀ 1) :
    (T, v) ∉ forwardParabolicBoundary T y₀ := by
  intro hboundary
  rcases mem_forwardParabolicBoundary_iff.mp hboundary with hinitial | hlateral
  · exact (ne_of_gt hT) hinitial.1
  · change PDE.euclideanSqDist v y₀ < 1 ^ 2 at hv
    rcases hlateral with ⟨_hzero, _hT, hsphere⟩
    change PDE.euclideanSqDist v y₀ = 1 ^ 2 at hsphere
    linarith

end HypoellipticAleksandrov.Parabolic

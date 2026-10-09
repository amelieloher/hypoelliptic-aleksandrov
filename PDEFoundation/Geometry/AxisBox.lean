module

public import PDEFoundation.Geometry.AxisCube

/-!
# Axis-aligned boxes

This file extracts the open coordinate-box geometry already used by the
application repositories into the shared native-vector foundation. An
`axisBox a b` is the product `∏ i, (a i, b i)`. Axis cubes remain the
equal-side special case.
-/

@[expose] public section

namespace PDE

/-- The open axis box `∏ i, (a i, b i)` in the native `Vec d` ambient
space. -/
def axisBox {d : ℕ} (a b : Vec d) : Set (Vec d) :=
  Set.pi Set.univ fun i => Set.Ioo (a i) (b i)

/-- The open axis cube with coordinate center `x₀` and half-side `R`. -/
def centeredAxisCube {d : ℕ}
    (x₀ : Vec d) (R : ℝ) : Set (Vec d) :=
  axisBox (fun i => x₀ i - R) (fun i => x₀ i + R)

/-- The closed axis cube with coordinate center `x₀` and half-side `R`. -/
def closedCenteredAxisCube {d : ℕ}
    (x₀ : Vec d) (R : ℝ) : Set (Vec d) :=
  Set.pi Set.univ fun i => Set.Icc (x₀ i - R) (x₀ i + R)

/-- The existing axis cube is definitionally the equal-side axis box. -/
theorem axisCube_eq_axisBox {d : ℕ} (z : Vec d) (L : ℝ) :
    axisCube z L = axisBox z (fun i => z i + L) :=
  rfl

theorem isOpen_axisBox {d : ℕ} (a b : Vec d) :
    IsOpen (axisBox a b) := by
  dsimp [axisBox]
  exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo

theorem isOpen_centeredAxisCube {d : ℕ}
    (x₀ : Vec d) (R : ℝ) :
    IsOpen (centeredAxisCube x₀ R) :=
  isOpen_axisBox _ _

theorem isClosed_closedCenteredAxisCube {d : ℕ}
    (x₀ : Vec d) (R : ℝ) :
    IsClosed (closedCenteredAxisCube x₀ R) := by
  dsimp [closedCenteredAxisCube]
  exact isClosed_set_pi fun _ _ => isClosed_Icc

/-- The closed native axis cube is the closed ball for the inherited product
supremum metric. This is a cube bridge, not a round Euclidean ball. -/
theorem closedCenteredAxisCube_eq_metric_closedBall {d : ℕ}
    (x₀ : Vec d) {R : ℝ} (hR : 0 ≤ R) :
    closedCenteredAxisCube x₀ R = Metric.closedBall x₀ R := by
  rw [closedBall_pi x₀ hR]
  ext x
  simp [closedCenteredAxisCube, Real.closedBall_eq_Icc]

/-- The open native axis cube is the open ball for the inherited product
supremum metric. This is a cube bridge, not a round Euclidean ball. -/
theorem centeredAxisCube_eq_metric_ball {d : ℕ}
    (x₀ : Vec d) {R : ℝ} (hR : 0 < R) :
    centeredAxisCube x₀ R = Metric.ball x₀ R := by
  rw [ball_pi x₀ hR]
  ext x
  simp [centeredAxisCube, axisBox, Real.ball_eq_Ioo]

theorem isBoundedDomain_axisBox {d : ℕ} (a b : Vec d) :
    IsBoundedDomain (axisBox a b) := by
  dsimp [axisBox]
  exact Bornology.IsBounded.isBoundedDomain <|
    Bornology.IsBounded.pi fun _ => Metric.isBounded_Ioo _ _

theorem convex_axisBox {d : ℕ} (a b : Vec d) :
    Convex ℝ (axisBox a b) := by
  dsimp [axisBox]
  refine convex_pi ?_
  intro _ _
  exact convex_Ioo _ _

theorem isOpenBoundedConvexDomain_axisBox {d : ℕ}
    (a b : Vec d) :
    IsOpenBoundedConvexDomain (axisBox a b) :=
  ⟨isOpen_axisBox a b, isBoundedDomain_axisBox a b,
    convex_axisBox a b⟩

theorem isOpenBoundedConvexDomain_centeredAxisCube {d : ℕ}
    (x₀ : Vec d) (R : ℝ) :
    IsOpenBoundedConvexDomain (centeredAxisCube x₀ R) :=
  isOpenBoundedConvexDomain_axisBox _ _

/-- The coordinate center lies in its open axis cube whenever the half-side
is positive. -/
theorem center_mem_centeredAxisCube {d : ℕ}
    (x₀ : Vec d) {R : ℝ} (hR : 0 < R) :
    x₀ ∈ centeredAxisCube x₀ R := by
  intro i _
  change x₀ i - R < x₀ i ∧ x₀ i < x₀ i + R
  constructor <;> linarith

/-- Strict coordinatewise side inequalities give an explicit midpoint in
the box. -/
theorem axisBox_nonempty {d : ℕ} (a b : Vec d)
    (hab : ∀ i, a i < b i) :
    (axisBox a b).Nonempty := by
  let x : Vec d := fun i => (a i + b i) / 2
  refine ⟨x, ?_⟩
  intro i _
  change a i < x i ∧ x i < b i
  dsimp [x]
  constructor <;> linarith [hab i]

/-- Coordinatewise containment of endpoints gives containment of open axis
boxes. -/
theorem axisBox_mono {d : ℕ} {a b c e : Vec d}
    (hca : c ≤ a) (hbe : b ≤ e) :
    axisBox a b ⊆ axisBox c e := by
  intro x hx i _
  have hxi := hx i (Set.mem_univ i)
  exact ⟨lt_of_le_of_lt (hca i) hxi.1,
    lt_of_lt_of_le hxi.2 (hbe i)⟩

/-- Centered open axis cubes are monotone in their half-side. -/
theorem centeredAxisCube_mono {d : ℕ} (x₀ : Vec d)
    {r R : ℝ} (hrR : r ≤ R) :
    centeredAxisCube x₀ r ⊆ centeredAxisCube x₀ R := by
  apply axisBox_mono
  · intro i
    dsimp
    linarith
  · intro i
    dsimp
    linarith

/-- If every side length is at most `L`, the Euclidean diameter is at most
`sqrt d * L`. -/
theorem hasEuclideanDiameterLE_axisBox_of_side_le {d : ℕ}
    (a b : Vec d) {L : ℝ} (hL : 0 ≤ L)
    (hsides : ∀ i, b i - a i ≤ L) :
    HasEuclideanDiameterLE (axisBox a b)
      (Real.sqrt d * L) := by
  intro x hx y hy
  have hsup : ‖x - y‖ ≤ L := by
    rw [pi_norm_le_iff_of_nonneg hL]
    intro i
    have hxi := hx i (Set.mem_univ i)
    have hyi := hy i (Set.mem_univ i)
    change a i < x i ∧ x i < b i at hxi
    change a i < y i ∧ y i < b i at hyi
    have hcoord : |x i - y i| ≤ b i - a i := by
      rw [abs_le]
      constructor <;> linarith [hxi.1, hxi.2, hyi.1, hyi.2]
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using
      hcoord.trans (hsides i)
  exact
    (vecEuclideanNorm_le_sqrt_natCast_mul_norm (x - y)).trans
      (mul_le_mul_of_nonneg_left hsup (Real.sqrt_nonneg d))

/-- The native centered cube has Euclidean diameter at most
`sqrt d * (2 * R)`. -/
theorem hasEuclideanDiameterLE_centeredAxisCube {d : ℕ}
    (x₀ : Vec d) {R : ℝ} (hR : 0 ≤ R) :
    HasEuclideanDiameterLE (centeredAxisCube x₀ R)
      (Real.sqrt d * (2 * R)) := by
  apply hasEuclideanDiameterLE_axisBox_of_side_le _ _
    (mul_nonneg (by norm_num) hR)
  intro i
  ring_nf
  rfl

end PDE

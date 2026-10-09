module

public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import HypoellipticAleksandrov.Ambient.MatrixContraction
public import HypoellipticAleksandrov.Coefficients.Ellipticity
public import HypoellipticAleksandrov.Geometry.KineticPoint
public import PDEFoundation.Sobolev.ClassicalGradient

/-!
# Classical kinetic product API

This module fixes the product-cylinder geometry, anisotropic classical
regularity, and plus-sign kinetic operator used in the time-velocity estimates.  The kinetic points
retain their explicit time, position, and velocity fields; product sets are transported only through
`KineticPoint.homeomorphProd`.

No maximum theorem is proved here.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

/-- The open kinetic product cylinder `(r₀, r₁) × (Ωx × Ωv)`. -/
def kineticProductOpenCylinder {d : ℕ} (r₀ r₁ : ℝ) (Ωx Ωv : Set (PDE.Vec d)) :
    Set (KineticPoint d) :=
  (KineticPoint.homeomorphProd d) ⁻¹' (Set.Ioo r₀ r₁ ×ˢ (Ωx ×ˢ Ωv))

/-- The closed kinetic product cylinder `[r₀, r₁] × (closure Ωx × closure Ωv)`. -/
def kineticProductClosedCylinder {d : ℕ} (r₀ r₁ : ℝ) (Ωx Ωv : Set (PDE.Vec d)) :
    Set (KineticPoint d) :=
  (KineticPoint.homeomorphProd d) ⁻¹'
    (Set.Icc r₀ r₁ ×ˢ (closure Ωx ×ˢ closure Ωv))

/-- The terminal face `{r₁} × (closure Ωx × closure Ωv)`. -/
def kineticProductTerminalFace {d : ℕ} (r₁ : ℝ) (Ωx Ωv : Set (PDE.Vec d)) :
    Set (KineticPoint d) :=
  (KineticPoint.homeomorphProd d) ⁻¹'
    (({r₁} : Set ℝ) ×ˢ (closure Ωx ×ˢ closure Ωv))

/-- The spatial lateral face `[r₀, r₁] × (frontier Ωx × closure Ωv)`. -/
def kineticProductSpatialLateralFace {d : ℕ} (r₀ r₁ : ℝ) (Ωx Ωv : Set (PDE.Vec d)) :
    Set (KineticPoint d) :=
  (KineticPoint.homeomorphProd d) ⁻¹'
    (Set.Icc r₀ r₁ ×ˢ (frontier Ωx ×ˢ closure Ωv))

/-- The velocity lateral face `[r₀, r₁] × (closure Ωx × frontier Ωv)`. -/
def kineticProductVelocityLateralFace {d : ℕ} (r₀ r₁ : ℝ) (Ωx Ωv : Set (PDE.Vec d)) :
    Set (KineticPoint d) :=
  (KineticPoint.homeomorphProd d) ⁻¹'
    (Set.Icc r₀ r₁ ×ˢ (closure Ωx ×ˢ frontier Ωv))

/-- The terminal and spatial/velocity lateral boundary, associated as `(T ∪ X) ∪ V`. -/
def kineticProductTerminalLateralBoundary {d : ℕ} (r₀ r₁ : ℝ)
    (Ωx Ωv : Set (PDE.Vec d)) : Set (KineticPoint d) :=
  (kineticProductTerminalFace r₁ Ωx Ωv ∪
    kineticProductSpatialLateralFace r₀ r₁ Ωx Ωv) ∪
      kineticProductVelocityLateralFace r₀ r₁ Ωx Ωv

/-- Membership in an open kinetic product cylinder. -/
@[simp] theorem mem_kineticProductOpenCylinder_iff {d : ℕ} {r₀ r₁ : ℝ}
    {Ωx Ωv : Set (PDE.Vec d)} {z : KineticPoint d} :
    z ∈ kineticProductOpenCylinder r₀ r₁ Ωx Ωv ↔
      r₀ < z.time ∧ z.time < r₁ ∧ z.position ∈ Ωx ∧ z.velocity ∈ Ωv := by
  change (z.time, (z.position, z.velocity)) ∈ Set.Ioo r₀ r₁ ×ˢ (Ωx ×ˢ Ωv) ↔ _
  constructor
  · rintro ⟨⟨hr₀, hr₁⟩, hx, hv⟩
    exact ⟨hr₀, hr₁, hx, hv⟩
  · rintro ⟨hr₀, hr₁, hx, hv⟩
    exact ⟨⟨hr₀, hr₁⟩, hx, hv⟩

/-- Membership in a closed kinetic product cylinder. -/
@[simp] theorem mem_kineticProductClosedCylinder_iff {d : ℕ} {r₀ r₁ : ℝ}
    {Ωx Ωv : Set (PDE.Vec d)} {z : KineticPoint d} :
    z ∈ kineticProductClosedCylinder r₀ r₁ Ωx Ωv ↔
      r₀ ≤ z.time ∧ z.time ≤ r₁ ∧ z.position ∈ closure Ωx ∧ z.velocity ∈ closure Ωv := by
  change (z.time, (z.position, z.velocity)) ∈
    Set.Icc r₀ r₁ ×ˢ (closure Ωx ×ˢ closure Ωv) ↔ _
  constructor
  · rintro ⟨⟨hr₀, hr₁⟩, hx, hv⟩
    exact ⟨hr₀, hr₁, hx, hv⟩
  · rintro ⟨hr₀, hr₁, hx, hv⟩
    exact ⟨⟨hr₀, hr₁⟩, hx, hv⟩

/-- Membership in the terminal face of a kinetic product cylinder. -/
@[simp] theorem mem_kineticProductTerminalFace_iff {d : ℕ} {r₁ : ℝ}
    {Ωx Ωv : Set (PDE.Vec d)} {z : KineticPoint d} :
    z ∈ kineticProductTerminalFace r₁ Ωx Ωv ↔
      z.time = r₁ ∧ z.position ∈ closure Ωx ∧ z.velocity ∈ closure Ωv := by
  change (z.time, (z.position, z.velocity)) ∈
    ({r₁} : Set ℝ) ×ˢ (closure Ωx ×ˢ closure Ωv) ↔ _
  rfl

/-- Membership in the spatial lateral face of a kinetic product cylinder. -/
@[simp] theorem mem_kineticProductSpatialLateralFace_iff {d : ℕ} {r₀ r₁ : ℝ}
    {Ωx Ωv : Set (PDE.Vec d)} {z : KineticPoint d} :
    z ∈ kineticProductSpatialLateralFace r₀ r₁ Ωx Ωv ↔
      r₀ ≤ z.time ∧ z.time ≤ r₁ ∧ z.position ∈ frontier Ωx ∧ z.velocity ∈ closure Ωv := by
  change (z.time, (z.position, z.velocity)) ∈
    Set.Icc r₀ r₁ ×ˢ (frontier Ωx ×ˢ closure Ωv) ↔ _
  constructor
  · rintro ⟨⟨hr₀, hr₁⟩, hx, hv⟩
    exact ⟨hr₀, hr₁, hx, hv⟩
  · rintro ⟨hr₀, hr₁, hx, hv⟩
    exact ⟨⟨hr₀, hr₁⟩, hx, hv⟩

/-- Membership in the velocity lateral face of a kinetic product cylinder. -/
@[simp] theorem mem_kineticProductVelocityLateralFace_iff {d : ℕ} {r₀ r₁ : ℝ}
    {Ωx Ωv : Set (PDE.Vec d)} {z : KineticPoint d} :
    z ∈ kineticProductVelocityLateralFace r₀ r₁ Ωx Ωv ↔
      r₀ ≤ z.time ∧ z.time ≤ r₁ ∧ z.position ∈ closure Ωx ∧ z.velocity ∈ frontier Ωv := by
  change (z.time, (z.position, z.velocity)) ∈
    Set.Icc r₀ r₁ ×ˢ (closure Ωx ×ˢ frontier Ωv) ↔ _
  constructor
  · rintro ⟨⟨hr₀, hr₁⟩, hx, hv⟩
    exact ⟨hr₀, hr₁, hx, hv⟩
  · rintro ⟨hr₀, hr₁, hx, hv⟩
    exact ⟨⟨hr₀, hr₁⟩, hx, hv⟩

/-- Membership in the terminal and lateral boundary of a kinetic product cylinder. -/
@[simp] theorem mem_kineticProductTerminalLateralBoundary_iff {d : ℕ} {r₀ r₁ : ℝ}
    {Ωx Ωv : Set (PDE.Vec d)} {z : KineticPoint d} :
    z ∈ kineticProductTerminalLateralBoundary r₀ r₁ Ωx Ωv ↔
      (z.time = r₁ ∧ z.position ∈ closure Ωx ∧ z.velocity ∈ closure Ωv) ∨
        (r₀ ≤ z.time ∧ z.time ≤ r₁ ∧ z.position ∈ frontier Ωx ∧
          z.velocity ∈ closure Ωv) ∨
        (r₀ ≤ z.time ∧ z.time ≤ r₁ ∧ z.position ∈ closure Ωx ∧
          z.velocity ∈ frontier Ωv) := by
  simp only [kineticProductTerminalLateralBoundary, Set.mem_union,
    mem_kineticProductTerminalFace_iff, mem_kineticProductSpatialLateralFace_iff,
    mem_kineticProductVelocityLateralFace_iff, or_assoc]

/-- The time derivative with position and velocity held fixed. -/
def kineticTimeDerivative {d : ℕ} (u : KineticPoint d → ℝ) (z : KineticPoint d) : ℝ :=
  deriv (fun r => u ⟨r, z.position, z.velocity⟩) z.time

/-- The position gradient with time and velocity held fixed. -/
def kineticPositionGradient {d : ℕ} (u : KineticPoint d → ℝ) (z : KineticPoint d) :
    PDE.Vec d :=
  PDE.classicalGradient (fun x => u ⟨z.time, x, z.velocity⟩) z.position

/-- The velocity gradient with time and position held fixed. -/
def kineticVelocityGradient {d : ℕ} (u : KineticPoint d → ℝ) (z : KineticPoint d) :
    PDE.Vec d :=
  PDE.classicalGradient (fun v => u ⟨z.time, z.position, v⟩) z.velocity

/-- The velocity Hessian indexed as `D_i(D_j u)`. -/
def kineticVelocityHessian {d : ℕ} (u : KineticPoint d → ℝ) (z : KineticPoint d) :
    PDE.Mat d :=
  fun i j =>
    (fderiv ℝ (fun v : PDE.Vec d =>
      PDE.classicalGradient (fun w : PDE.Vec d => u ⟨z.time, z.position, w⟩) v)
      z.velocity (PDE.basisVec i)) j

/--
The anisotropic kinetic `C^{1,1,2}` regularity predicate. It asks only for
one time, one position, and two velocity derivatives on separate slices.
-/
def IsKineticC112On {d : ℕ} (u : KineticPoint d → ℝ) (D : Set (KineticPoint d)) : Prop :=
  ContinuousOn u D ∧
    (∀ z ∈ D, DifferentiableAt ℝ (fun r => u ⟨r, z.position, z.velocity⟩) z.time) ∧
    (∀ z ∈ D, ContDiffAt ℝ 1 (fun x => u ⟨z.time, x, z.velocity⟩) z.position) ∧
    (∀ z ∈ D, ContDiffAt ℝ 2 (fun v => u ⟨z.time, z.position, v⟩) z.velocity) ∧
    ContinuousOn (kineticTimeDerivative u) D ∧
    ContinuousOn (kineticPositionGradient u) D ∧
    ContinuousOn (kineticVelocityGradient u) D ∧
    ContinuousOn (kineticVelocityHessian u) D

namespace IsKineticC112On

/-- The function itself is continuous on the specified set. -/
theorem continuousOn {d : ℕ} {u : KineticPoint d → ℝ} {D : Set (KineticPoint d)}
    (h : IsKineticC112On u D) : ContinuousOn u D :=
  h.1

/-- Each fixed-position-and-velocity time slice is differentiable on the set. -/
theorem timeSlice_differentiableAt {d : ℕ} {u : KineticPoint d → ℝ}
    {D : Set (KineticPoint d)} (h : IsKineticC112On u D) {z : KineticPoint d}
    (hz : z ∈ D) :
    DifferentiableAt ℝ (fun r => u ⟨r, z.position, z.velocity⟩) z.time :=
  h.2.1 z hz

/-- Each fixed-time-and-velocity position slice is `C¹` on the set. -/
theorem positionSlice_contDiffAt {d : ℕ} {u : KineticPoint d → ℝ}
    {D : Set (KineticPoint d)} (h : IsKineticC112On u D) {z : KineticPoint d}
    (hz : z ∈ D) :
    ContDiffAt ℝ 1 (fun x => u ⟨z.time, x, z.velocity⟩) z.position :=
  h.2.2.1 z hz

/-- Each fixed-time-and-position velocity slice is `C²` on the set. -/
theorem velocitySlice_contDiffAt {d : ℕ} {u : KineticPoint d → ℝ}
    {D : Set (KineticPoint d)} (h : IsKineticC112On u D) {z : KineticPoint d}
    (hz : z ∈ D) :
    ContDiffAt ℝ 2 (fun v => u ⟨z.time, z.position, v⟩) z.velocity :=
  h.2.2.2.1 z hz

/-- The kinetic time derivative is continuous on the specified set. -/
theorem continuousOn_kineticTimeDerivative {d : ℕ} {u : KineticPoint d → ℝ}
    {D : Set (KineticPoint d)} (h : IsKineticC112On u D) :
    ContinuousOn (kineticTimeDerivative u) D :=
  h.2.2.2.2.1

/-- The kinetic position gradient is continuous on the specified set. -/
theorem continuousOn_kineticPositionGradient {d : ℕ} {u : KineticPoint d → ℝ}
    {D : Set (KineticPoint d)} (h : IsKineticC112On u D) :
    ContinuousOn (kineticPositionGradient u) D :=
  h.2.2.2.2.2.1

/-- The kinetic velocity gradient is continuous on the specified set. -/
theorem continuousOn_kineticVelocityGradient {d : ℕ} {u : KineticPoint d → ℝ}
    {D : Set (KineticPoint d)} (h : IsKineticC112On u D) :
    ContinuousOn (kineticVelocityGradient u) D :=
  h.2.2.2.2.2.2.1

/-- The kinetic velocity Hessian is continuous on the specified set. -/
theorem continuousOn_kineticVelocityHessian {d : ℕ} {u : KineticPoint d → ℝ}
    {D : Set (KineticPoint d)} (h : IsKineticC112On u D) :
    ContinuousOn (kineticVelocityHessian u) D :=
  h.2.2.2.2.2.2.2

/-- The fixed-position-and-velocity time slice has its kinetic time derivative. -/
theorem timeSlice_hasDerivAt {d : ℕ} {u : KineticPoint d → ℝ}
    {D : Set (KineticPoint d)} (h : IsKineticC112On u D) {z : KineticPoint d}
    (hz : z ∈ D) :
    HasDerivAt (fun r => u ⟨r, z.position, z.velocity⟩) (kineticTimeDerivative u z)
      z.time := by
  exact (h.timeSlice_differentiableAt hz).hasDerivAt

end IsKineticC112On

/-- The plus-sign kinetic product operator `∂ᵣ + v · ∇ₓ + A : D²ᵥ`. -/
def kineticProductOperator {d : ℕ} (A : CoefficientField d) (u : KineticPoint d → ℝ)
    (z : KineticPoint d) : ℝ :=
  kineticTimeDerivative u z +
    PDE.vecDot z.velocity (kineticPositionGradient u z) +
      matrixContraction (A z.time z.velocity) (kineticVelocityHessian u z)

/-- Evaluation of the plus-sign kinetic product operator. -/
@[simp] theorem kineticProductOperator_apply {d : ℕ} (A : CoefficientField d)
    (u : KineticPoint d → ℝ) (z : KineticPoint d) :
    kineticProductOperator A u z =
      kineticTimeDerivative u z +
        PDE.vecDot z.velocity (kineticPositionGradient u z) +
          matrixContraction (A z.time z.velocity) (kineticVelocityHessian u z) :=
  rfl

end HypoellipticAleksandrov.Parabolic

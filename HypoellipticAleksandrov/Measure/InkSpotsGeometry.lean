module

public import HypoellipticAleksandrov.Parabolic.ScalingMeasure

/-!
# Source geometry for parabolic ink spots

This module fixes the box geometry in Section 2 of Krylov--Safonov used by
the crawling-of-ink-spots argument.  It contains only the source boxes,
their three enlargements, their ambient unions, and their elementary
topological and measure properties.  It does not contain the density
saturation lemma or either wind estimate.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal Topology

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/-- Parameters of a source box \(Q_{1,R}(t_0,v_0)\).  Positivity is deliberately
kept out of the data and belongs to the strict-dense predicate. -/
structure InkSpotsBox (d : ℕ) where
  radius : ℝ
  baseTime : ℝ
  center : PDE.Vec d

/-- The source reference box \(Q_1=Q_{1,1}(0,0)\). -/
def inkSpotsUnitBox (d : ℕ) : Set (TimeVelocity d) :=
  parabolicBox 1 1 0 0

/-- The source box \(Q=Q_{1,R}(t_0,v_0)\). -/
def inkSpotsSourceBox {d : ℕ} (q : InkSpotsBox d) : Set (TimeVelocity d) :=
  parabolicBox 1 q.radius q.baseTime q.center

/-- The first source enlargement \(Q^1\), including its required clipping by
the reference box. -/
def inkSpotsQ1 {d : ℕ} (q : InkSpotsBox d) : Set (TimeVelocity d) :=
  parabolicBox (7 / 9 : ℝ) (3 * q.radius)
    (q.baseTime - 3 * q.radius ^ 2) q.center ∩ inkSpotsUnitBox d

/-- The forward source enlargement \(Q^2\).  Its time interval is not clipped
by the reference box. -/
def inkSpotsQ2 {d : ℕ} (eta : ℝ) (q : InkSpotsBox d) :
    Set (TimeVelocity d) :=
  Ioo (q.baseTime + q.radius ^ 2)
      (q.baseTime + q.radius ^ 2 + 4 * q.radius ^ 2 / eta) ×ˢ
    (velocityCube q.center (3 * q.radius) ∩ velocityCube 0 1)

/-- The terminal time at the right edge of \(Q^2\). -/
def inkSpotsTerminalTime {d : ℕ} (eta : ℝ) (q : InkSpotsBox d) : ℝ :=
  q.baseTime + q.radius ^ 2 + 4 * q.radius ^ 2 / eta

/-- The source terminal contraction \(S_\zeta\). -/
def inkSpotsContraction {d : ℕ} (eta zeta : ℝ) (q : InkSpotsBox d) :
    TimeVelocity d → TimeVelocity d :=
  fun z ↦
    (inkSpotsTerminalTime eta q - zeta ^ 2 *
        (inkSpotsTerminalTime eta q - z.1),
      q.center + zeta • (z.2 - q.center))

/-- The source set \(Q^3=S_\zeta(Q^2)\). -/
def inkSpotsQ3 {d : ℕ} (eta zeta : ℝ) (q : InkSpotsBox d) :
    Set (TimeVelocity d) :=
  inkSpotsContraction eta zeta q '' inkSpotsQ2 eta q

/-- The strict source density condition.  Radius positivity is visible here,
not hidden in the box parameter structure. -/
def inkSpotsStrictDense {d : ℕ} (Gamma : Set (TimeVelocity d)) (xi : ℝ)
    (q : InkSpotsBox d) : Prop :=
  0 < q.radius ∧
    inkSpotsSourceBox q ⊆ inkSpotsUnitBox d ∧
    xi * (volume (inkSpotsSourceBox q)).toReal <
      (volume (inkSpotsSourceBox q ∩ Gamma)).toReal

/-- The actual source family of strict dense boxes. -/
def inkSpotsDenseBoxes {d : ℕ} (Gamma : Set (TimeVelocity d)) (xi : ℝ) :
    Set (InkSpotsBox d) :=
  {q | inkSpotsStrictDense Gamma xi q}

/-- The source union \(D^1=\bigcup_{Q\in\mathcal B}Q^1\). -/
def inkSpotsD1 {d : ℕ} (Gamma : Set (TimeVelocity d)) (xi : ℝ) :
    Set (TimeVelocity d) :=
  ⋃ q ∈ inkSpotsDenseBoxes Gamma xi, inkSpotsQ1 q

/-- The source union \(D^2=\bigcup_{Q\in\mathcal B}Q^2\). -/
def inkSpotsD2 {d : ℕ} (Gamma : Set (TimeVelocity d)) (xi eta : ℝ) :
    Set (TimeVelocity d) :=
  ⋃ q ∈ inkSpotsDenseBoxes Gamma xi, inkSpotsQ2 eta q

/-- The source union \(D^3=\bigcup_{Q\in\mathcal B}Q^3\). -/
def inkSpotsD3 {d : ℕ} (Gamma : Set (TimeVelocity d)) (xi eta zeta : ℝ) :
    Set (TimeVelocity d) :=
  ⋃ q ∈ inkSpotsDenseBoxes Gamma xi, inkSpotsQ3 eta zeta q

/-- The uncut time span from the left edge of the source first enlargement to
the terminal edge of the forward enlargement. -/
def stackSpan {d : ℕ} (eta : ℝ) (q : InkSpotsBox d) : ℝ :=
  4 * q.radius ^ 2 + 4 * q.radius ^ 2 / eta

/-- The time span of the forward source enlargement \(Q^2\). -/
def forwardSpan {d : ℕ} (eta : ℝ) (q : InkSpotsBox d) : ℝ :=
  4 * q.radius ^ 2 / eta

@[simp] theorem mem_inkSpotsSourceBox_iff {d : ℕ} {q : InkSpotsBox d}
    {t : ℝ} {v : PDE.Vec d} :
    (t, v) ∈ inkSpotsSourceBox q ↔
      q.baseTime < t ∧ t < q.baseTime + q.radius ^ 2 ∧
        v ∈ velocityCube q.center q.radius :=
  by
    simpa only [inkSpotsSourceBox, one_mul] using
      (mem_parabolicBox_iff (vartheta := (1 : ℝ)) (r := q.radius)
        (t₀ := q.baseTime) (t := t) (v₀ := q.center) (v := v))

@[simp] theorem mem_inkSpotsQ1_iff {d : ℕ} {q : InkSpotsBox d}
    {t : ℝ} {v : PDE.Vec d} :
    (t, v) ∈ inkSpotsQ1 q ↔
      q.baseTime - 3 * q.radius ^ 2 < t ∧
        t < q.baseTime - 3 * q.radius ^ 2 +
          (7 / 9 : ℝ) * (3 * q.radius) ^ 2 ∧
        v ∈ velocityCube q.center (3 * q.radius) ∧
        (t, v) ∈ inkSpotsUnitBox d :=
  by
    rw [inkSpotsQ1, mem_inter_iff, mem_parabolicBox_iff]
    constructor
    · rintro ⟨⟨htLower, htUpper, hv⟩, hz⟩
      exact ⟨htLower, htUpper, hv, hz⟩
    · rintro ⟨htLower, htUpper, hv, hz⟩
      exact ⟨⟨htLower, htUpper, hv⟩, hz⟩

@[simp] theorem mem_inkSpotsQ2_iff {d : ℕ} {eta : ℝ} {q : InkSpotsBox d}
    {t : ℝ} {v : PDE.Vec d} :
    (t, v) ∈ inkSpotsQ2 eta q ↔
      q.baseTime + q.radius ^ 2 < t ∧
        t < inkSpotsTerminalTime eta q ∧
        v ∈ velocityCube q.center (3 * q.radius) ∧
        v ∈ velocityCube 0 1 :=
  by
    constructor
    · rintro ⟨⟨htLower, htUpper⟩, hvCenter, hvUnit⟩
      exact ⟨htLower, htUpper, hvCenter, hvUnit⟩
    · rintro ⟨htLower, htUpper, hvCenter, hvUnit⟩
      exact ⟨⟨htLower, htUpper⟩, hvCenter, hvUnit⟩

@[simp] theorem mem_inkSpotsQ3_iff {d : ℕ} {eta zeta : ℝ}
    {q : InkSpotsBox d} {z : TimeVelocity d} :
    z ∈ inkSpotsQ3 eta zeta q ↔
      ∃ y ∈ inkSpotsQ2 eta q, inkSpotsContraction eta zeta q y = z :=
  Iff.rfl

@[simp] theorem inkSpotsTerminalTime_eq {d : ℕ} (eta : ℝ) (q : InkSpotsBox d) :
    inkSpotsTerminalTime eta q =
      q.baseTime + q.radius ^ 2 + 4 * q.radius ^ 2 / eta :=
  rfl

/-- The source box is contained in its clipped first enlargement whenever it
is a genuine positive-radius subbox of the reference box. -/
theorem inkSpotsSourceBox_subset_Q1 {d : ℕ} {q : InkSpotsBox d}
    (hr : 0 < q.radius) (hq : inkSpotsSourceBox q ⊆ inkSpotsUnitBox d) :
    inkSpotsSourceBox q ⊆ inkSpotsQ1 q := by
  intro z hz
  refine ⟨?_, hq hz⟩
  rcases z with ⟨t, v⟩
  rw [mem_inkSpotsSourceBox_iff] at hz
  rw [mem_parabolicBox_iff]
  constructor
  · nlinarith [sq_pos_of_pos hr]
  constructor
  · norm_num
    nlinarith [sq_pos_of_pos hr]
  · intro i
    have hi := hz.2.2 i
    calc
      |v i - q.center i| < q.radius := hi
      _ < 3 * q.radius := by linarith

/-- Every strict dense source box is contained in its first source
enlargement. -/
theorem inkSpotsSourceBox_subset_Q1_of_strictDense {d : ℕ}
    {Gamma : Set (TimeVelocity d)} {xi : ℝ} {q : InkSpotsBox d}
    (hq : inkSpotsStrictDense Gamma xi q) :
    inkSpotsSourceBox q ⊆ inkSpotsQ1 q :=
  inkSpotsSourceBox_subset_Q1 hq.1 hq.2.1

/-- The first source enlargement is open. -/
theorem isOpen_inkSpotsQ1 {d : ℕ} (q : InkSpotsBox d) :
    IsOpen (inkSpotsQ1 q) :=
  (isOpen_parabolicBox _ _ _ _).inter (isOpen_parabolicBox _ _ _ _)

/-- The first source enlargement is measurable. -/
theorem measurableSet_inkSpotsQ1 {d : ℕ} (q : InkSpotsBox d) :
    MeasurableSet (inkSpotsQ1 q) :=
  (isOpen_inkSpotsQ1 q).measurableSet

/-- The forward source enlargement is open. -/
theorem isOpen_inkSpotsQ2 {d : ℕ} (eta : ℝ) (q : InkSpotsBox d) :
    IsOpen (inkSpotsQ2 eta q) :=
  isOpen_Ioo.prod ((isOpen_velocityCube _ _).inter (isOpen_velocityCube _ _))

/-- The forward source enlargement is measurable. -/
theorem measurableSet_inkSpotsQ2 {d : ℕ} (eta : ℝ) (q : InkSpotsBox d) :
    MeasurableSet (inkSpotsQ2 eta q) :=
  (isOpen_inkSpotsQ2 eta q).measurableSet

/-- The terminal contraction is the parabolic affine map with terminal
translation data. -/
theorem inkSpotsContraction_eq_parabolicAffine {d : ℕ} (eta zeta : ℝ)
    (q : InkSpotsBox d) :
    inkSpotsContraction eta zeta q =
      parabolicAffine ((1 - zeta ^ 2) * inkSpotsTerminalTime eta q)
        ((1 - zeta) • q.center) zeta := by
  funext z
  rcases z with ⟨t, v⟩
  apply Prod.ext
  · dsimp [inkSpotsContraction, parabolicAffine]
    ring
  · funext i
    dsimp [inkSpotsContraction, parabolicAffine]
    ring

/-- A positive terminal contraction is injective. -/
theorem inkSpotsContraction_injective {d : ℕ} {eta zeta : ℝ}
    {q : InkSpotsBox d} (hzeta : 0 < zeta) :
    Function.Injective (inkSpotsContraction eta zeta q) := by
  rw [inkSpotsContraction_eq_parabolicAffine]
  exact parabolicAffine_injective hzeta

/-- A positive terminal contraction is a measurable embedding. -/
theorem inkSpotsContraction_measurableEmbedding {d : ℕ} {eta zeta : ℝ}
    {q : InkSpotsBox d} (hzeta : 0 < zeta) :
    MeasurableEmbedding (inkSpotsContraction eta zeta q) := by
  rw [inkSpotsContraction_eq_parabolicAffine]
  exact parabolicAffine_measurableEmbedding hzeta

/-- The inverse of the terminal contraction, exposed for the open-map bridge. -/
def inkSpotsContractionInverse {d : ℕ} (eta zeta : ℝ) (q : InkSpotsBox d) :
    TimeVelocity d → TimeVelocity d :=
  fun z ↦
    (inkSpotsTerminalTime eta q + zeta⁻¹ ^ 2 *
        (z.1 - inkSpotsTerminalTime eta q),
      q.center + zeta⁻¹ • (z.2 - q.center))

/-- The displayed inverse is itself a parabolic affine map. -/
theorem inkSpotsContractionInverse_eq_parabolicAffine {d : ℕ} (eta zeta : ℝ)
    (q : InkSpotsBox d) :
    inkSpotsContractionInverse eta zeta q =
      parabolicAffine ((1 - zeta⁻¹ ^ 2) * inkSpotsTerminalTime eta q)
        ((1 - zeta⁻¹) • q.center) zeta⁻¹ := by
  funext z
  rcases z with ⟨t, v⟩
  apply Prod.ext
  · dsimp [inkSpotsContractionInverse, parabolicAffine]
    ring
  · funext i
    dsimp [inkSpotsContractionInverse, parabolicAffine]
    ring

private theorem inkSpotsContraction_leftInverse {d : ℕ} {eta zeta : ℝ}
    {q : InkSpotsBox d} (hzeta : zeta ≠ 0) :
    Function.LeftInverse (inkSpotsContractionInverse eta zeta q)
      (inkSpotsContraction eta zeta q) := by
  intro z
  rcases z with ⟨t, v⟩
  apply Prod.ext
  · dsimp [inkSpotsContractionInverse, inkSpotsContraction]
    field_simp
    ring
  · funext i
    dsimp [inkSpotsContractionInverse, inkSpotsContraction]
    field_simp
    ring

private theorem inkSpotsContraction_rightInverse {d : ℕ} {eta zeta : ℝ}
    {q : InkSpotsBox d} (hzeta : zeta ≠ 0) :
    Function.RightInverse (inkSpotsContractionInverse eta zeta q)
      (inkSpotsContraction eta zeta q) := by
  intro z
  rcases z with ⟨t, v⟩
  apply Prod.ext
  · dsimp [inkSpotsContractionInverse, inkSpotsContraction]
    field_simp
    ring
  · funext i
    dsimp [inkSpotsContractionInverse, inkSpotsContraction]
    field_simp
    ring

/-- A positive terminal contraction is an open map. -/
theorem isOpenMap_inkSpotsContraction {d : ℕ} {eta zeta : ℝ}
    {q : InkSpotsBox d} (hzeta : 0 < zeta) :
    IsOpenMap (inkSpotsContraction eta zeta q) := by
  let e : TimeVelocity d ≃ₜ TimeVelocity d :=
    { toFun := inkSpotsContraction eta zeta q
      invFun := inkSpotsContractionInverse eta zeta q
      left_inv := inkSpotsContraction_leftInverse hzeta.ne'
      right_inv := inkSpotsContraction_rightInverse hzeta.ne'
      continuous_toFun := by
        rw [inkSpotsContraction_eq_parabolicAffine]
        exact (contDiff_infty_parabolicAffine
          ((1 - zeta ^ 2) * inkSpotsTerminalTime eta q)
          ((1 - zeta) • q.center) zeta).continuous
      continuous_invFun := by
        rw [inkSpotsContractionInverse_eq_parabolicAffine]
        exact (contDiff_infty_parabolicAffine
          ((1 - zeta⁻¹ ^ 2) * inkSpotsTerminalTime eta q)
          ((1 - zeta⁻¹) • q.center) zeta⁻¹).continuous }
  exact e.isOpenMap

/-- The terminal source enlargement is open for positive contraction factor. -/
theorem isOpen_inkSpotsQ3 {d : ℕ} {eta zeta : ℝ} (q : InkSpotsBox d)
    (hzeta : 0 < zeta) :
    IsOpen (inkSpotsQ3 eta zeta q) := by
  exact isOpenMap_inkSpotsContraction hzeta (inkSpotsQ2 eta q)
    (isOpen_inkSpotsQ2 eta q)

/-- The terminal source enlargement is measurable for positive contraction
factor. -/
theorem measurableSet_inkSpotsQ3 {d : ℕ} {eta zeta : ℝ} (q : InkSpotsBox d)
    (hzeta : 0 < zeta) :
    MeasurableSet (inkSpotsQ3 eta zeta q) :=
  (isOpen_inkSpotsQ3 q hzeta).measurableSet

/-- Exact volume scaling of one terminally contracted source box. -/
theorem volume_inkSpotsQ3 {d : ℕ} {eta zeta : ℝ} (q : InkSpotsBox d)
    (hzeta : 0 < zeta) :
    volume (inkSpotsQ3 eta zeta q) =
      ENNReal.ofReal (zeta ^ (d + 2)) * volume (inkSpotsQ2 eta q) := by
  rw [inkSpotsQ3, inkSpotsContraction_eq_parabolicAffine]
  exact volume_parabolicAffine_image_eq
    ((1 - zeta ^ 2) * inkSpotsTerminalTime eta q) ((1 - zeta) • q.center)
    hzeta (inkSpotsQ2 eta q)

/-- The source \(D^1\) is open. -/
theorem isOpen_inkSpotsD1 {d : ℕ} (Gamma : Set (TimeVelocity d)) (xi : ℝ) :
    IsOpen (inkSpotsD1 Gamma xi) := by
  unfold inkSpotsD1
  apply isOpen_iUnion
  intro q
  apply isOpen_iUnion
  intro hq
  exact isOpen_inkSpotsQ1 q

/-- The source \(D^1\) is measurable. -/
theorem measurableSet_inkSpotsD1 {d : ℕ} (Gamma : Set (TimeVelocity d)) (xi : ℝ) :
    MeasurableSet (inkSpotsD1 Gamma xi) :=
  (isOpen_inkSpotsD1 Gamma xi).measurableSet

/-- The source \(D^2\) is open. -/
theorem isOpen_inkSpotsD2 {d : ℕ} (Gamma : Set (TimeVelocity d))
    (xi eta : ℝ) :
    IsOpen (inkSpotsD2 Gamma xi eta) := by
  unfold inkSpotsD2
  apply isOpen_iUnion
  intro q
  apply isOpen_iUnion
  intro hq
  exact isOpen_inkSpotsQ2 eta q

/-- The source \(D^2\) is measurable. -/
theorem measurableSet_inkSpotsD2 {d : ℕ} (Gamma : Set (TimeVelocity d))
    (xi eta : ℝ) :
    MeasurableSet (inkSpotsD2 Gamma xi eta) :=
  (isOpen_inkSpotsD2 Gamma xi eta).measurableSet

/-- The source \(D^3\) is open for positive terminal contraction factor. -/
theorem isOpen_inkSpotsD3 {d : ℕ} (Gamma : Set (TimeVelocity d))
    (xi eta zeta : ℝ) (hzeta : 0 < zeta) :
    IsOpen (inkSpotsD3 Gamma xi eta zeta) := by
  unfold inkSpotsD3
  apply isOpen_iUnion
  intro q
  apply isOpen_iUnion
  intro hq
  exact isOpen_inkSpotsQ3 q hzeta

/-- The source \(D^3\) is measurable for positive terminal contraction factor. -/
theorem measurableSet_inkSpotsD3 {d : ℕ} (Gamma : Set (TimeVelocity d))
    (xi eta zeta : ℝ) (hzeta : 0 < zeta) :
    MeasurableSet (inkSpotsD3 Gamma xi eta zeta) :=
  (isOpen_inkSpotsD3 Gamma xi eta zeta hzeta).measurableSet

/-- The uncut stack span has the exact source \((1+\eta)\) algebra. -/
theorem stackSpan_eq_one_add_eta_mul_forwardSpan {d : ℕ} {eta : ℝ}
    (q : InkSpotsBox d) (heta : 0 < eta) :
    stackSpan eta q = (1 + eta) * forwardSpan eta q := by
  unfold stackSpan forwardSpan
  field_simp
  ring

end

end HypoellipticAleksandrov.Parabolic

module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.LocalizedKrylovCalculus
public import HypoellipticAleksandrov.Parabolic.ScalingMeasure
public import HypoellipticAleksandrov.Measure.TimeVelocity
public import PDEFoundation.Geometry.EuclideanBall.Topology

/-!
# Geometry and `L^{d+1}` scaling of the localized occupation reflection

With `h = (1 - α) / R²`, the map `reflectScale R v_*` carries the Krylov cylinder
`(0, h) × B_1(0)` (written `krylovCylinder h h 0`) onto the source cylinder
`(α, 1) × B_R(v_*)`, the bottom and lateral faces onto the terminal and lateral faces, and
rescales the source's restricted `L^{d+1}` norm by exactly `R^(d/(d+1))`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic MeasureTheory Set Filter
open scoped Topology ENNReal

variable {d : ℕ}

/-- The scaled height `h = (1 - α) / R²` of the reflected cylinder. -/
def localHeight (α R : ℝ) : ℝ := (1 - α) / R ^ 2

theorem localHeight_pos {α R : ℝ} (hα : α < 1) (hR : 0 < R) : 0 < localHeight α R :=
  div_pos (sub_pos.mpr hα) (pow_pos hR 2)

theorem localHeight_le_one {α R : ℝ} (hα : 0 ≤ α) (hR : 1 ≤ R) : localHeight α R ≤ 1 := by
  unfold localHeight
  rw [div_le_one (by positivity)]
  nlinarith

theorem mul_localHeight {α R : ℝ} (hR : 0 < R) : R ^ 2 * localHeight α R = 1 - α := by
  unfold localHeight
  field_simp

/-- A closed Euclidean ball lies in the closure of the open ball of the same radius. -/
theorem euclideanClosedBall_subset_closure_euclideanBall {x : PDE.Vec d} {R : ℝ}
    (hR : 0 < R) : PDE.euclideanClosedBall x R ⊆ closure (PDE.euclideanBall x R) := by
  intro y hy
  have hpath : Tendsto (fun t : ℝ => t • (y - x) + x) (𝓝[<] 1) (𝓝 y) := by
    have h1 : Tendsto (fun t : ℝ => t • (y - x) + x) (𝓝 1) (𝓝 ((1 : ℝ) • (y - x) + x)) :=
      ((continuous_id.smul continuous_const).add continuous_const).tendsto 1
    simpa using h1.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hpath ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht
  change PDE.euclideanSqDist (t • (y - x) + x) x < R ^ 2
  rw [PDE.euclideanSqDist_affine_center]
  have hy' : PDE.euclideanSqDist y x ≤ R ^ 2 := hy
  have hs : PDE.euclideanSqDist (y - x) 0 = PDE.euclideanSqDist y x := by
    simp [PDE.euclideanSqDist]
  rw [hs]
  have hR2 : 0 < R ^ 2 := pow_pos hR 2
  have ht2 : t ^ 2 < 1 := by nlinarith [ht.1, ht.2]
  nlinarith [PDE.euclideanSqDist_nonneg y x, sq_nonneg t]

/-- The open Euclidean ball is bounded. -/
theorem isBounded_euclideanBall (x : PDE.Vec d) {R : ℝ} (hR : 0 < R) :
    Bornology.IsBounded (PDE.euclideanBall x R) :=
  (Metric.isBounded_ball (x := x) (r := R)).subset (PDE.euclideanBall_subset_supBall hR)

section Cylinders

variable {α R : ℝ} {vStar : PDE.Vec d}

/-- The ball part: `v_* + R y` lies in `B_R(v_*)` iff `y ∈ B_1(0)`. -/
theorem vStar_add_smul_mem_ball_iff (hR : 0 < R) (y : PDE.Vec d) :
    vStar + R • y ∈ PDE.euclideanBall vStar R ↔ y ∈ PDE.euclideanBall (0 : PDE.Vec d) 1 := by
  rw [add_comm]
  exact PDE.affine_mem_euclideanBall_iff_of_pos vStar y hR

/-- The closed-ball part of the same correspondence. -/
theorem vStar_add_smul_mem_closedBall_iff (hR : 0 < R) (y : PDE.Vec d) :
    vStar + R • y ∈ PDE.euclideanClosedBall vStar R ↔
      y ∈ PDE.euclideanClosedBall (0 : PDE.Vec d) 1 := by
  rw [add_comm]
  exact PDE.affine_mem_euclideanClosedBall_iff_of_pos vStar y hR

/-- The Krylov cylinder is exactly the preimage of the source cylinder. -/
theorem mem_krylovCylinder_iff_reflectScale (hR : 0 < R) (z : TimeVelocity d) :
    z ∈ krylovCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d) ↔
      reflectScale R vStar z ∈ scalarParabolicOpenCylinder α 1 (PDE.euclideanBall vStar R) := by
  rcases z with ⟨t, y⟩
  rw [mem_krylovCylinder_iff]
  change _ ↔ (1 - R ^ 2 * t, vStar + R • y) ∈
    scalarParabolicOpenCylinder α 1 (PDE.euclideanBall vStar R)
  rw [mem_scalarParabolicOpenCylinder_iff, vStar_add_smul_mem_ball_iff hR,
    sub_self]
  have hR2 : 0 < R ^ 2 := pow_pos hR 2
  have hh : R ^ 2 * localHeight α R = 1 - α := mul_localHeight hR
  constructor
  · rintro ⟨h0, h1, h2⟩
    refine ⟨?_, ?_, h2⟩ <;> nlinarith
  · rintro ⟨h0, h1, h2⟩
    refine ⟨?_, ?_, h2⟩
    · by_contra hcon
      nlinarith
    · by_contra hcon
      nlinarith

/-- The closed Krylov cylinder maps into the closed source cylinder. -/
theorem krylovClosedCylinder_subset_preimage (hR : 0 < R) :
    krylovClosedCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d) ⊆
      reflectScale R vStar ⁻¹'
        scalarParabolicClosedCylinder α 1 (PDE.euclideanBall vStar R) := by
  rintro ⟨t, y⟩ ⟨⟨h0, h1⟩, hy⟩
  rw [sub_self] at h0
  change (1 - R ^ 2 * t, vStar + R • y) ∈
    scalarParabolicClosedCylinder α 1 (PDE.euclideanBall vStar R)
  rw [mem_scalarParabolicClosedCylinder_iff]
  have hh : R ^ 2 * localHeight α R = 1 - α := mul_localHeight hR
  have hR2 : 0 < R ^ 2 := pow_pos hR 2
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  exact euclideanClosedBall_subset_closure_euclideanBall hR
    ((vStar_add_smul_mem_closedBall_iff hR y).mpr hy)

/-- The bottom and lateral Krylov faces map to the terminal and lateral faces. -/
theorem krylovParabolicBoundary_subset_preimage (hR : 0 < R) :
    krylovParabolicBoundary (localHeight α R) (localHeight α R) (0 : PDE.Vec d) ⊆
      reflectScale R vStar ⁻¹'
        (scalarParabolicTerminalFace 1 (PDE.euclideanBall vStar R) ∪
          scalarParabolicLateralFace α 1 (PDE.euclideanBall vStar R)) := by
  have hh : R ^ 2 * localHeight α R = 1 - α := mul_localHeight hR
  have hR2 : 0 < R ^ 2 := pow_pos hR 2
  rintro ⟨t, y⟩ hz
  change (1 - R ^ 2 * t, vStar + R • y) ∈
    scalarParabolicTerminalFace 1 (PDE.euclideanBall vStar R) ∪
      scalarParabolicLateralFace α 1 (PDE.euclideanBall vStar R)
  rcases hz with ⟨ht, hy⟩ | ⟨ht, hy⟩
  · have ht' : t = localHeight α R - localHeight α R := ht
    rw [sub_self] at ht'
    left
    rw [mem_scalarParabolicTerminalFace_iff]
    refine ⟨by rw [ht']; ring, ?_⟩
    exact euclideanClosedBall_subset_closure_euclideanBall hR
      ((vStar_add_smul_mem_closedBall_iff hR y).mpr hy)
  · obtain ⟨h0, h1⟩ := ht
    rw [sub_self] at h0
    right
    rw [mem_scalarParabolicLateralFace_iff]
    refine ⟨by nlinarith, by nlinarith, ?_⟩
    rw [(PDE.isOpen_euclideanBall vStar R).frontier_eq]
    have hsph : vStar + R • y ∈ PDE.euclideanSphere vStar R := by
      change PDE.euclideanSqDist (vStar + R • y) vStar = R ^ 2
      rw [add_comm, PDE.euclideanSqDist_affine_center]
      have : PDE.euclideanSqDist y 0 = 1 ^ 2 := hy
      rw [this]
      ring
    refine ⟨euclideanClosedBall_subset_closure_euclideanBall hR (le_of_eq hsph), ?_⟩
    intro hlt
    have h1 : PDE.euclideanSqDist (vStar + R • y) vStar < R ^ 2 := hlt
    have h2 : PDE.euclideanSqDist (vStar + R • y) vStar = R ^ 2 := hsph
    exact lt_irrefl _ (h2 ▸ h1)

/-- The inverse of `reflectScale` on points of the source cylinder. -/
def reflectScaleInv (R : ℝ) (vStar : PDE.Vec d) (w : TimeVelocity d) : TimeVelocity d :=
  ((1 - w.1) / R ^ 2, R⁻¹ • (w.2 - vStar))

theorem reflectScale_reflectScaleInv (hR : 0 < R) (w : TimeVelocity d) :
    reflectScale R vStar (reflectScaleInv R vStar w) = w := by
  rcases w with ⟨r, y⟩
  apply Prod.ext
  · change 1 - R ^ 2 * ((1 - r) / R ^ 2) = r
    field_simp
    ring
  · ext i
    change vStar i + R * (R⁻¹ * (y i - vStar i)) = y i
    field_simp
    ring

/-- A point of the source cylinder is the image of a point of the Krylov cylinder. -/
theorem exists_mem_krylovCylinder (hR : 0 < R) {w : TimeVelocity d}
    (hw : w ∈ scalarParabolicOpenCylinder α 1 (PDE.euclideanBall vStar R)) :
    ∃ z ∈ krylovCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d),
      reflectScale R vStar z = w := by
  refine ⟨reflectScaleInv R vStar w, ?_, reflectScale_reflectScaleInv hR w⟩
  rw [mem_krylovCylinder_iff_reflectScale hR (vStar := vStar) (α := α),
    reflectScale_reflectScaleInv hR]
  exact hw

theorem parabolicAffine_surjective {t₀ : ℝ} (hR : 0 < R) :
    Function.Surjective (parabolicAffine t₀ vStar R) := by
  rintro ⟨s, y⟩
  refine ⟨((s - t₀) / R ^ 2, R⁻¹ • (y - vStar)), ?_⟩
  apply Prod.ext
  · change t₀ + R ^ 2 * ((s - t₀) / R ^ 2) = s
    field_simp
    ring
  · ext i
    change vStar i + R * (R⁻¹ * (y i - vStar i)) = y i
    field_simp
    ring

/-- The image of the Krylov cylinder under the forward parabolic affine map. -/
theorem parabolicAffine_image_krylovCylinder (hR : 0 < R) :
    parabolicAffine 0 vStar R ''
        krylovCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d) =
      timeReflection ⁻¹' scalarParabolicOpenCylinder α 1 (PDE.euclideanBall vStar R) := by
  have hpre : krylovCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d) =
      parabolicAffine 0 vStar R ⁻¹'
        (timeReflection ⁻¹' scalarParabolicOpenCylinder α 1 (PDE.euclideanBall vStar R)) := by
    ext z
    rw [mem_krylovCylinder_iff_reflectScale hR (vStar := vStar) (α := α), reflectScale_eq]
    rfl
  rw [hpre]
  exact Set.image_preimage_eq _ (parabolicAffine_surjective hR)

end Cylinders

section Norms

variable {α R : ℝ} {vStar : PDE.Vec d}

/-- Reflection preserves the global `L^{d+1}` extended norm. -/
theorem parabolicELpNorm_timeReflectedScalar {F : TimeVelocity d → ℝ} (hF : Continuous F) :
    eLpNorm (timeReflectedScalar F) (parabolicExponent d) volume =
      eLpNorm F (parabolicExponent d) volume := by
  unfold timeReflectedScalar
  exact eLpNorm_comp_measurePreserving hF.aestronglyMeasurable timeReflection_measurePreserving

/-- Reflection of a measurable set preserves the restricted `L^{d+1}` extended norm. -/
theorem parabolicELpNormOn_timeReflectedScalar_preimage {F : TimeVelocity d → ℝ}
    (hF : Continuous F) {S : Set (TimeVelocity d)} (hS : MeasurableSet S) :
    parabolicELpNormOn d (timeReflectedScalar F) (timeReflection ⁻¹' S) =
      parabolicELpNormOn d F S := by
  unfold parabolicELpNormOn timeReflectedScalar
  exact eLpNorm_comp_measurePreserving hF.aestronglyMeasurable
    (timeReflection_measurePreserving.restrict_preimage hS)

/-- The source cylinder is measurable. -/
theorem measurableSet_sourceCylinder (α R : ℝ) (vStar : PDE.Vec d) :
    MeasurableSet (scalarParabolicOpenCylinder α 1 (PDE.euclideanBall vStar R)) :=
  measurableSet_Ioo.prod (PDE.measurableSet_euclideanBall vStar R)

/-- The localized source `f(t, y) = R² F(1 - R² t, v_* + R y)`. -/
def localizedSource (R : ℝ) (vStar : PDE.Vec d) (F : TimeVelocity d → ℝ) :
    TimeVelocity d → ℝ :=
  fun z => R ^ 2 * F (reflectScale R vStar z)

theorem localizedSource_eq (R : ℝ) (vStar : PDE.Vec d) (F : TimeVelocity d → ℝ) :
    localizedSource R vStar F =
      fun z => R ^ 2 * timeReflectedScalar F (parabolicAffine 0 vStar R z) := by
  funext z
  unfold localizedSource
  rw [reflectScale_eq]
  rfl

/-- The extended `L^{d+1}` norm of the localized source is the rescaled source norm. -/
theorem parabolicELpNormOn_localizedSource (hR : 0 < R) {F : TimeVelocity d → ℝ}
    (hF : Continuous F) :
    parabolicELpNormOn d (localizedSource R vStar F)
        (krylovCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d)) =
      ‖R ^ 2‖ₑ * (ENNReal.ofReal ((R ^ (d + 2))⁻¹) ^ (1 / parabolicExponent d).toReal) *
        parabolicELpNormOn d F (scalarParabolicOpenCylinder α 1 (PDE.euclideanBall vStar R)) := by
  rw [localizedSource_eq, parabolicELpNormOn_pullback_raw 0 vStar hR,
    parabolicAffine_image_krylovCylinder hR,
    parabolicELpNormOn_timeReflectedScalar_preimage hF (measurableSet_sourceCylinder α R vStar)]

/-- The real `L^{d+1}` norm of the localized source: Jacobian factor `R^(d/(d+1))`. -/
theorem parabolicLpNormOn_localizedSource (hR : 0 < R) {F : TimeVelocity d → ℝ}
    (hF : Continuous F) :
    parabolicLpNormOn d (localizedSource R vStar F)
        (krylovCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d)) =
      R ^ ((d : ℝ) / ((d : ℝ) + 1)) *
        parabolicLpNormOn d F (scalarParabolicOpenCylinder α 1 (PDE.euclideanBall vStar R)) := by
  rw [localizedSource_eq, parabolicLpNormOn_pullback 0 vStar hR,
    parabolicAffine_image_krylovCylinder hR]
  unfold parabolicLpNormOn
  rw [parabolicELpNormOn_timeReflectedScalar_preimage hF (measurableSet_sourceCylinder α R vStar)]

/-- The localized source is in `L^{d+1}` of the Krylov cylinder when `F` is in `L^{d+1}`. -/
theorem memLp_localizedSource (hR : 0 < R) {F : TimeVelocity d → ℝ}
    (hF : Continuous F) (hFp : MemLp F (parabolicExponent d) volume) :
    MemLp (localizedSource R vStar F) (parabolicExponent d)
      (volume.restrict
        (krylovCylinder (localHeight α R) (localHeight α R) (0 : PDE.Vec d))) := by
  change parabolicELpNormOn d (localizedSource R vStar F) _ < ⊤
  rw [parabolicELpNormOn_localizedSource hR hF]
  have hfin : parabolicELpNormOn d F
      (scalarParabolicOpenCylinder α 1 (PDE.euclideanBall vStar R)) < ⊤ := by
    refine lt_of_le_of_lt ?_ hFp
    exact eLpNorm_mono_measure F Measure.restrict_le_self
  refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ?_ ?_) hfin
  · exact ENNReal.coe_lt_top
  · exact ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top

end Norms

end HypoellipticAleksandrov.KineticAleksandrov.Occupation

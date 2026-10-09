module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ReflectionAPI
public import PDEFoundation.Geometry.EuclideanBall.Topology
public import Mathlib.Topology.UniformSpace.HeineCantor

/-! # Inner-cylinder scales, shifted centres and compact coordinate bounds -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set

/-- Free-transport coordinates as a homeomorphism, preserving the existing carrier. -/
def relativeHomeomorph {d : ℕ} (Z₀ : KineticPoint d) :
    KineticPoint d ≃ₜ ℝ × (PDE.Vec d × PDE.Vec d) where
  toFun P := (P.time, (relativePosition Z₀ P, relativeVelocity Z₀ P))
  invFun q := ⟨q.1, Z₀.position + (q.1-Z₀.time) • Z₀.velocity + q.2.1,
    Z₀.velocity + q.2.2⟩
  left_inv P := by
    ext i <;> simp [relativePosition, relativeVelocity] <;> ring
  right_inv q := by
    rcases q with ⟨s,Y,V⟩
    apply Prod.ext
    · rfl
    · apply Prod.ext <;> ext i <;> simp [relativePosition, relativeVelocity] <;> ring
  continuous_toFun := continuous_time.prodMk
    ((continuous_position.sub continuous_const |>.sub
      ((continuous_time.sub continuous_const).smul continuous_const)).prodMk
      (continuous_velocity.sub continuous_const))
  continuous_invFun := KineticPoint.continuous_mk continuous_fst
    ((continuous_const.add ((continuous_fst.sub continuous_const).smul continuous_const)).add
      continuous_snd.fst) (continuous_const.add continuous_snd.snd)

/-- A compact closed rectangle in free-transport coordinates. -/
def relativeClosedBox {d : ℕ} (Z₀ : KineticPoint d) (a b rv rx : ℝ) :
    Set (KineticPoint d) :=
  (relativeHomeomorph Z₀) ⁻¹'
    (Icc a b ×ˢ (PDE.euclideanClosedBall 0 rx ×ˢ PDE.euclideanClosedBall 0 rv))

/-- Closed relative-coordinate rectangles are compact for nonnegative radii. -/
theorem isCompact_relativeClosedBox {d : ℕ} (Z₀ : KineticPoint d)
    (a b rv rx : ℝ) (hv : 0 ≤ rv) (hx : 0 ≤ rx) :
    IsCompact (relativeClosedBox Z₀ a b rv rx) := by
  have hc := (isCompact_Icc : IsCompact (Icc a b)).prod
    ((PDE.isCompact_euclideanClosedBall (0 : PDE.Vec d) hx).prod
      (PDE.isCompact_euclideanClosedBall (0 : PDE.Vec d) hv))
  simpa only [relativeClosedBox, Homeomorph.image_symm] using
    hc.image (relativeHomeomorph Z₀).symm.continuous

/-- Positivity and the exact squared-radius identity for inner scaling. -/
theorem innerRatio_spec (R : ℝ) (hR : 0 < R) (δ : ℝ)
    (hδ0 : 0 < δ) (hδlt : δ < R ^ 2 / 2) :
    0 < innerRatio R hR δ hδ0 hδlt ∧ innerRatio R hR δ hδ0 hδlt < 1 ∧
      (innerRatio R hR δ hδ0 hδlt) ^ 2 * R ^ 2 = R ^ 2 - 2 * δ := by
  have hr2 : 0 < R ^ 2 := sq_pos_of_pos hR
  have hdiv : 0 < 2 * δ / R ^ 2 := div_pos (by linarith) hr2
  have hdivlt : 2 * δ / R ^ 2 < 1 := (div_lt_one hr2).2 (by linarith)
  have hb : 0 < 1 - 2 * δ / R ^ 2 := by linarith
  unfold innerRatio
  refine ⟨Real.sqrt_pos.2 hb, ?_, ?_⟩
  · exact (Real.sqrt_lt' (by norm_num : (0:ℝ)<1)).2 (by linarith)
  · rw [Real.sq_sqrt hb.le]
    field_simp

/-- Shifting to the inner centre does not change the relative coordinates. -/
theorem innerCentre_relative {d : ℕ} (Z₀ P : KineticPoint d) (δ : ℝ) :
    relativePosition (innerCentre Z₀ δ) P = relativePosition Z₀ P ∧
      relativeVelocity (innerCentre Z₀ δ) P = relativeVelocity Z₀ P := by
  constructor
  · ext i
    simp [innerCentre, relativePosition]
    ring
  · rfl

/-- Inner cylinder identification, with radius positivity supplied as part of the result. -/
theorem innerCylinder_eq_forwardCylinder {d : ℕ}
    (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (δ : ℝ) (hδ0 : 0 < δ) (hδlt : δ < R ^ 2 / 2) :
    ∃ hr : 0 < innerRatio R hR δ hδ0 hδlt * R,
      innerCylinder Z₀ R hR δ hδ0 hδlt =
        forwardCylinder (innerCentre Z₀ δ) (innerRatio R hR δ hδ0 hδlt * R) hr := by
  obtain ⟨hρ, _, hs⟩ := innerRatio_spec R hR δ hδ0 hδlt
  refine ⟨mul_pos hρ hR, ?_⟩
  ext P
  rw [mem_innerCylinder_iff, mem_forwardCylinder_iff, (innerCentre_relative Z₀ P δ).1]
  have hv : P.velocity ∈ PDE.euclideanBall (innerCentre Z₀ δ).velocity
      (innerRatio R hR δ hδ0 hδlt * R) ↔
      relativeVelocity Z₀ P ∈ PDE.euclideanBall 0 (innerRatio R hR δ hδ0 hδlt * R) := by
    simp [PDE.euclideanBall, PDE.euclideanSqDist, relativeVelocity, innerCentre]
  rw [hv, mul_pow]
  simp only [innerCentre]
  have ht : Z₀.time + δ + (innerRatio R hR δ hδ0 hδlt)^2 * R^2 =
      Z₀.time + R^2 - δ := by linarith
  simp only [ht, mul_pow]

/-- Inner cylinders shrink as the trimming parameter increases. -/
theorem innerCylinder_nested {d : ℕ} (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (δ₁ δ₂ : ℝ) (hδ₁0 : 0 < δ₁) (hδ₁lt : δ₁ < R ^ 2 / 2)
    (hδ₂0 : 0 < δ₂) (hδ₂lt : δ₂ < R ^ 2 / 2) (hδ : δ₁ ≤ δ₂) :
    innerCylinder Z₀ R hR δ₂ hδ₂0 hδ₂lt ⊆
      innerCylinder Z₀ R hR δ₁ hδ₁0 hδ₁lt := by
  have h1 := (innerRatio_spec R hR δ₁ hδ₁0 hδ₁lt).1
  have h2 := (innerRatio_spec R hR δ₂ hδ₂0 hδ₂lt).1
  have hρ : innerRatio R hR δ₂ hδ₂0 hδ₂lt ≤ innerRatio R hR δ₁ hδ₁0 hδ₁lt := by
    unfold innerRatio
    apply Real.sqrt_le_sqrt
    gcongr
  intro P hP
  rcases hP with ⟨ht1,ht2,hv,hx⟩
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · exact PDE.euclideanBall_mono (mul_pos h2 hR).le (mul_le_mul_of_nonneg_right hρ hR.le) hv
  · apply PDE.euclideanBall_mono (mul_nonneg (pow_nonneg h2.le 3) (pow_nonneg hR.le 3)) _ hx
    gcongr

/-- Inner closures obey the explicit weak coordinate bounds. -/
theorem closure_innerCylinder_bounds {d : ℕ}
    (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (δ : ℝ) (hδ0 : 0 < δ) (hδlt : δ < R ^ 2 / 2) :
    closure (innerCylinder Z₀ R hR δ hδ0 hδlt) ⊆
      relativeClosedBox Z₀ (Z₀.time+δ) (Z₀.time+R^2-δ)
        (innerRatio R hR δ hδ0 hδlt * R)
        ((innerRatio R hR δ hδ0 hδlt)^3 * R^3) := by
  have hρ := (innerRatio_spec R hR δ hδ0 hδlt).1
  apply closure_minimal
  · intro P hP
    rcases hP with ⟨h1,h2,hv,hx⟩
    exact ⟨⟨h1.le,h2.le⟩, PDE.euclideanBall_subset_euclideanClosedBall _ _ hx,
      PDE.euclideanBall_subset_euclideanClosedBall _ _ hv⟩
  · exact (isCompact_relativeClosedBox Z₀ _ _ _ _ (mul_pos hρ hR).le
      (mul_nonneg (pow_nonneg hρ.le 3) (pow_nonneg hR.le 3))).isClosed

/-- Inner-cylinder closure is contained in the original open cylinder. -/
theorem closure_innerCylinder_subset {d : ℕ}
    (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (δ : ℝ) (hδ0 : 0 < δ) (hδlt : δ < R ^ 2 / 2) :
    closure (innerCylinder Z₀ R hR δ hδ0 hδlt) ⊆ forwardCylinder Z₀ R hR := by
  obtain ⟨hρ,hρ1,hs⟩ := innerRatio_spec R hR δ hδ0 hδlt
  intro P hP
  rcases closure_innerCylinder_bounds Z₀ R hR δ hδ0 hδlt hP with ⟨⟨h1,h2⟩,hx,hv⟩
  change Z₀.time + δ ≤ P.time at h1
  change P.time ≤ Z₀.time + R^2 - δ at h2
  change relativeVelocity Z₀ P ∈ PDE.euclideanClosedBall 0
    (innerRatio R hR δ hδ0 hδlt * R) at hv
  refine ⟨by linarith,by linarith,?_,?_⟩
  · have hb := PDE.euclideanClosedBall_subset_euclideanBall (mul_pos hρ hR).le
      (show innerRatio R hR δ hδ0 hδlt * R < R by nlinarith) hv
    simpa [PDE.euclideanBall, PDE.euclideanSqDist, relativeVelocity] using hb
  · apply PDE.euclideanClosedBall_subset_euclideanBall
      (mul_nonneg (pow_nonneg hρ.le 3) (pow_nonneg hR.le 3)) _ hx
    have hp : (innerRatio R hR δ hδ0 hδlt)^3 < 1 := by
      exact pow_lt_one₀ hρ.le hρ1 (by norm_num)
    nlinarith [pow_pos hR 3]

/-- Inner closures are compact in the existing finite-dimensional coordinate topology. -/
theorem isCompact_closure_innerCylinder {d : ℕ}
    (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (δ : ℝ) (hδ0 : 0 < δ) (hδlt : δ < R ^ 2 / 2) :
    IsCompact (closure (innerCylinder Z₀ R hR δ hδ0 hδlt)) := by
  have hρ := (innerRatio_spec R hR δ hδ0 hδlt).1
  exact (isCompact_relativeClosedBox Z₀ _ _ _ _ (mul_pos hρ hR).le
    (mul_nonneg (pow_nonneg hρ.le 3) (pow_nonneg hR.le 3))).of_isClosed_subset
      isClosed_closure (closure_innerCylinder_bounds Z₀ R hR δ hδ0 hδlt)

/-- Original forward closures satisfy the weak coordinate bounds. -/
theorem closure_forwardCylinder_bounds {d : ℕ}
    (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) :
    closure (forwardCylinder Z₀ R hR) ⊆
      relativeClosedBox Z₀ Z₀.time (Z₀.time + R^2) R (R^3) := by
  apply closure_minimal
  · intro P hP
    rcases hP with ⟨h1,h2,hv,hx⟩
    refine ⟨⟨h1.le,h2.le⟩, PDE.euclideanBall_subset_euclideanClosedBall _ _ hx, ?_⟩
    have hb := PDE.euclideanBall_subset_euclideanClosedBall _ _ hv
    simpa [relativeHomeomorph, relativeVelocity, PDE.euclideanClosedBall,
      PDE.euclideanSqDist] using hb
  · exact (isCompact_relativeClosedBox Z₀ _ _ _ _ hR.le (pow_nonneg hR.le 3)).isClosed

/-- Original forward closures are compact in the coordinate topology. -/
theorem isCompact_closure_forwardCylinder {d : ℕ}
    (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) :
    IsCompact (closure (forwardCylinder Z₀ R hR)) :=
  (isCompact_relativeClosedBox Z₀ _ _ _ _ hR.le (pow_nonneg hR.le 3)).of_isClosed_subset
    isClosed_closure (closure_forwardCylinder_bounds Z₀ R hR)

/-- Every interior point lies in all sufficiently near-to-original inner cylinders. -/
theorem innerCylinder_exhaustion {d : ℕ}
    (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) :
    ∀ P ∈ forwardCylinder Z₀ R hR, ∃ η : ℝ, 0 < η ∧
      ∀ (δ : ℝ) (hδ0 : 0 < δ) (hδlt : δ < R ^ 2 / 2), δ < η →
        P ∈ innerCylinder Z₀ R hR δ hδ0 hδlt := by
  intro P hP
  let ρ : ℝ → ℝ := fun δ => Real.sqrt (1 - 2 * δ / R^2)
  have hc : Continuous ρ :=
    Real.continuous_sqrt.comp (continuous_const.sub
      ((continuous_const.mul continuous_id).div_const _))
  let E : Set ℝ := {δ | Z₀.time + δ < P.time ∧ P.time < Z₀.time + R^2 - δ ∧
    PDE.euclideanSqDist (relativeVelocity Z₀ P) 0 < (ρ δ * R)^2 ∧
    PDE.euclideanSqDist (relativePosition Z₀ P) 0 < ((ρ δ)^3 * R^3)^2}
  have ho : IsOpen E :=
    (isOpen_lt (continuous_const.add continuous_id) continuous_const).inter
      ((isOpen_lt continuous_const ((continuous_const.add continuous_const).sub
        continuous_id)).inter
      ((isOpen_lt continuous_const ((hc.mul continuous_const).pow 2)).inter
        (isOpen_lt continuous_const (((hc.pow 3).mul continuous_const).pow 2))))
  have h0 : (0 : ℝ) ∈ E := by
    rcases hP with ⟨h1,h2,hv,hx⟩
    have hv' : PDE.euclideanSqDist (relativeVelocity Z₀ P) 0 < R^2 := by
      simpa [PDE.euclideanBall, PDE.euclideanSqDist, relativeVelocity] using hv
    change PDE.euclideanSqDist (relativePosition Z₀ P) 0 < (R^3)^2 at hx
    simpa [E,ρ] using And.intro h1 (And.intro h2 (And.intro hv' hx))
  obtain ⟨η,hη,he⟩ := Metric.mem_nhds_iff.mp (ho.mem_nhds h0)
  refine ⟨η,hη,?_⟩
  intro δ hδ0 hδlt hδη
  have hδE := he (show δ ∈ Metric.ball 0 η by simpa [Real.dist_eq,abs_of_pos hδ0])
  exact hδE

end HypoellipticAleksandrov.KineticAleksandrov

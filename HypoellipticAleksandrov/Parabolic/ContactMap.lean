module

public import HypoellipticAleksandrov.Parabolic.Derivatives

/-!
# Parabolic contact-map data

This module defines the affine velocity functions, slope--intercept wedge,
parabolic normal map, and measurable-sign-set candidate used in the smooth
parabolic ABP argument.  Coverage and Jacobian results belong to later modules.
-/

@[expose] public section

namespace HypoellipticAleksandrov.Parabolic

open Matrix

/-- The affine velocity function with intercept `h`, slope `p`, and center `y₀`. -/
def affineVelocity {d : ℕ} (y₀ : PDE.Vec d) (h : ℝ) (p : PDE.Vec d)
    (v : PDE.Vec d) : ℝ :=
  h + PDE.vecDot p (v - y₀)

/-- Evaluation of an affine velocity function. -/
@[simp] theorem affineVelocity_apply {d : ℕ} (y₀ : PDE.Vec d) (h : ℝ)
    (p v : PDE.Vec d) :
    affineVelocity y₀ h p v = h + PDE.vecDot p (v - y₀) :=
  rfl

/-- The open slope--intercept wedge associated with a height `M`. -/
def slopeInterceptWedge (d : ℕ) (M : ℝ) : Set (TimeVelocity d) :=
  Set.Ioo (M / 2) (3 * M / 4) ×ˢ PDE.euclideanBall (0 : PDE.Vec d) (M / 4)

/-- Membership in the slope--intercept wedge. -/
@[simp] theorem mem_slopeInterceptWedge_iff {d : ℕ} {M h : ℝ} {p : PDE.Vec d} :
    (h, p) ∈ slopeInterceptWedge d M ↔
      M / 2 < h ∧ h < 3 * M / 4 ∧ p ∈ PDE.euclideanBall (0 : PDE.Vec d) (M / 4) := by
  change (M / 2 < h ∧ h < 3 * M / 4) ∧ p ∈ PDE.euclideanBall (0 : PDE.Vec d) (M / 4) ↔
    M / 2 < h ∧ h < 3 * M / 4 ∧ p ∈ PDE.euclideanBall (0 : PDE.Vec d) (M / 4)
  constructor
  · rintro ⟨⟨hlower, hupper⟩, hp⟩
    exact ⟨hlower, hupper, hp⟩
  · rintro ⟨hlower, hupper, hp⟩
    exact ⟨⟨hlower, hupper⟩, hp⟩

/-- The parabolic normal map built from the velocity gradient of `u`. -/
noncomputable def parabolicNormalMap {d : ℕ} (u : TimeVelocity d → ℝ) (y₀ : PDE.Vec d) :
    TimeVelocity d → TimeVelocity d :=
  fun z ↦
    (u z - PDE.vecDot (velocityGradient u z) (z.2 - y₀), velocityGradient u z)

/-- Evaluation of the parabolic normal map. -/
@[simp] theorem parabolicNormalMap_apply {d : ℕ} (u : TimeVelocity d → ℝ)
    (y₀ : PDE.Vec d) (z : TimeVelocity d) :
    parabolicNormalMap u y₀ z =
      (u z - PDE.vecDot (velocityGradient u z) (z.2 - y₀), velocityGradient u z) :=
  rfl

/-- The interior sign set on which the parabolic Jacobian has the required sign. -/
def parabolicSignSet {d : ℕ} (T : ℝ) (y₀ : PDE.Vec d) (u : TimeVelocity d → ℝ) :
    Set (TimeVelocity d) :=
  {z | z ∈ parabolicInterior T y₀ ∧ 0 < u z ∧
    0 ≤ timeDerivative u z ∧ (-velocityHessian u z).PosSemidef}

/-- Membership in the parabolic sign set. -/
@[simp] theorem mem_parabolicSignSet_iff {d : ℕ} {T : ℝ} {y₀ : PDE.Vec d}
    {u : TimeVelocity d → ℝ} {z : TimeVelocity d} :
    z ∈ parabolicSignSet T y₀ u ↔
      z ∈ parabolicInterior T y₀ ∧ 0 < u z ∧
        0 ≤ timeDerivative u z ∧ (-velocityHessian u z).PosSemidef :=
  Iff.rfl

private theorem isClosed_isHermitian (d : ℕ) :
    IsClosed {H : PDE.Mat d | H.IsHermitian} := by
  have hset :
      {H : PDE.Mat d | H.IsHermitian} =
        ⋂ i : Fin d, ⋂ j : Fin d, {H : PDE.Mat d | H j i = H i j} := by
    ext H
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro h i j
      simpa using h.apply i j
    · intro h
      apply Matrix.IsHermitian.ext
      intro i j
      simpa using h i j
  rw [hset]
  refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
  exact isClosed_eq (continuous_id.matrix_elem j i) (continuous_id.matrix_elem i j)

private theorem isClosed_posSemidef (d : ℕ) :
    IsClosed {H : PDE.Mat d | H.PosSemidef} := by
  have hset :
      {H : PDE.Mat d | H.PosSemidef} =
        {H : PDE.Mat d | H.IsHermitian} ∩
          ⋂ q : PDE.Vec d, {H : PDE.Mat d | 0 ≤ q ⬝ᵥ (H *ᵥ q)} := by
    ext H
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    simpa using (Matrix.posSemidef_iff_dotProduct_mulVec (M := H))
  rw [hset]
  refine (isClosed_isHermitian d).inter (isClosed_iInter fun q => ?_)
  have hquad : Continuous (fun H : PDE.Mat d => q ⬝ᵥ (H *ᵥ q)) :=
    continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
  exact isClosed_le continuous_const hquad

/-- A globally `C²` scalar function has continuous time derivative. -/
theorem continuous_timeDerivative {d : ℕ} {u : TimeVelocity d → ℝ}
    (hu : ContDiff ℝ 2 u) : Continuous (timeDerivative u) := by
  change Continuous (fun z : TimeVelocity d ↦ fderiv ℝ u z (1, 0))
  exact ((hu.contDiff_fderiv_apply (m := 0) (by norm_num)).comp
    (contDiff_id.prodMk contDiff_const)).continuous

/-- A globally `C²` scalar function has continuous velocity Hessian. -/
theorem continuous_velocityHessian {d : ℕ} {u : TimeVelocity d → ℝ}
    (hu : ContDiff ℝ 2 u) : Continuous (velocityHessian u) := by
  apply continuous_matrix
  intro i j
  change Continuous (fun z : TimeVelocity d ↦
    fderiv ℝ (fderiv ℝ u) z (0, Pi.single i 1) (0, Pi.single j 1))
  have hdu : ContDiff ℝ 1 (fderiv ℝ u) :=
    hu.fderiv_right (m := 1) (by norm_num)
  exact (((hdu.contDiff_fderiv_apply (m := 0) (by norm_num)).comp
    (contDiff_id.prodMk contDiff_const)).clm_apply contDiff_const).continuous

/-- A globally `C²` scalar function has a `C¹` parabolic normal map. -/
theorem contDiff_parabolicNormalMap {d : ℕ} {u : TimeVelocity d → ℝ}
    (hu : ContDiff ℝ 2 u) (y₀ : PDE.Vec d) :
    ContDiff ℝ 1 (parabolicNormalMap u y₀) := by
  have hu' : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hgrad : ContDiff ℝ 1 (velocityGradient u) := contDiff_velocityGradient hu
  have hshift : ContDiff ℝ 1 (fun z : TimeVelocity d ↦ z.2 - y₀) :=
    contDiff_snd.sub contDiff_const
  have hdot : ContDiff ℝ 1 (fun z : TimeVelocity d ↦
      PDE.vecDot (velocityGradient u z) (z.2 - y₀)) := by
    unfold PDE.vecDot
    fun_prop
  exact (hu'.sub hdot).prodMk hgrad

/-- A globally `C²` scalar function has a continuous parabolic normal map. -/
theorem continuous_parabolicNormalMap {d : ℕ} {u : TimeVelocity d → ℝ}
    (hu : ContDiff ℝ 2 u) (y₀ : PDE.Vec d) :
    Continuous (parabolicNormalMap u y₀) :=
  (contDiff_parabolicNormalMap hu y₀).continuous

/-- A globally `C²` scalar function has a measurable parabolic normal map. -/
theorem measurable_parabolicNormalMap {d : ℕ} {u : TimeVelocity d → ℝ}
    (hu : ContDiff ℝ 2 u) (y₀ : PDE.Vec d) :
    Measurable (parabolicNormalMap u y₀) :=
  (continuous_parabolicNormalMap hu y₀).measurable

/-- The parabolic sign set of a globally `C²` scalar function is measurable. -/
theorem measurableSet_parabolicSignSet {d : ℕ} {u : TimeVelocity d → ℝ}
    (hu : ContDiff ℝ 2 u) (T : ℝ) (y₀ : PDE.Vec d) :
    MeasurableSet (parabolicSignSet T y₀ u) := by
  have htime : Continuous (timeDerivative u) := continuous_timeDerivative hu
  have hhess : Continuous (velocityHessian u) := continuous_velocityHessian hu
  have hpsd : MeasurableSet {z : TimeVelocity d | (-velocityHessian u z).PosSemidef} :=
    ((isClosed_posSemidef d).preimage hhess.neg).measurableSet
  rw [show parabolicSignSet T y₀ u =
      parabolicInterior T y₀ ∩ {z | 0 < u z} ∩ {z | 0 ≤ timeDerivative u z} ∩
        {z | (-velocityHessian u z).PosSemidef} by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, mem_parabolicSignSet_iff]
    constructor
    · rintro ⟨hinterior, hpositive, htime, hpsd⟩
      exact ⟨⟨⟨hinterior, hpositive⟩, htime⟩, hpsd⟩
    · rintro ⟨⟨⟨hinterior, hpositive⟩, htime⟩, hpsd⟩
      exact ⟨hinterior, hpositive, htime, hpsd⟩]
  exact (((measurableSet_parabolicInterior T y₀).inter
    (isOpen_lt continuous_const hu.continuous).measurableSet).inter
      (isClosed_le continuous_const htime).measurableSet).inter hpsd

end HypoellipticAleksandrov.Parabolic

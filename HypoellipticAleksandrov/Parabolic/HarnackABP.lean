module

public import HypoellipticAleksandrov.Parabolic.ABP
public import HypoellipticAleksandrov.Parabolic.ExponentialConjugation
public import HypoellipticAleksandrov.Parabolic.LocalGluing
public import HypoellipticAleksandrov.Parabolic.ScalingMeasure

/-!
# The local ABP bridge for the parabolic Harnack argument

This file proves the translated, radius-one-half ABP consequence used in
Krylov--Safonov Lemma 3.2.  It turns local classical data on the inner
cylinder into the globally regular data required by the unit ABP
estimate, removes the zeroth-order term by exponential conjugation, and then
uses the exact parabolic restricted-norm scaling formula.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped MatrixOrder Topology

/-- The affine map from the unit cylinder to the local ABP cylinder centered
at `v0`. -/
def localABPAffine {d : ℕ} (v0 : PDE.Vec d) : TimeVelocity d → TimeVelocity d :=
  parabolicAffine (3 / 4) v0 (1 / 2)

/-- The open inner cylinder `(3/4, 1) × B_(1/2)(v0)`, presented as the affine
image of the reference parabolic interior. -/
def localABPInterior {d : ℕ} (v0 : PDE.Vec d) : Set (TimeVelocity d) :=
  localABPAffine v0 '' parabolicInterior 1 0

/-- The compact closure of the local inner ABP cylinder. -/
def localABPClosure {d : ℕ} (v0 : PDE.Vec d) : Set (TimeVelocity d) :=
  localABPAffine v0 '' closedParabolicCylinder 1 0

/-- The initial-plus-lateral, but not terminal, boundary of the local ABP
cylinder. -/
def localABPForwardBoundary {d : ℕ} (v0 : PDE.Vec d) : Set (TimeVelocity d) :=
  localABPAffine v0 '' forwardParabolicBoundary 1 0

/-- The local ABP closure is compact. -/
theorem isCompact_localABPClosure {d : ℕ} (v0 : PDE.Vec d) :
    IsCompact (localABPClosure v0) := by
  unfold localABPClosure localABPAffine
  exact (isCompact_closedParabolicCylinder 1 0).image
    (contDiff_parabolicAffine (3 / 4) v0 (1 / 2)).continuous

/-- The local ABP interior is contained in its compact closure. -/
theorem localABPInterior_subset_closure {d : ℕ} (v0 : PDE.Vec d) :
    localABPInterior v0 ⊆ localABPClosure v0 := by
  unfold localABPInterior localABPClosure
  exact Set.image_mono (parabolicInterior_subset_closedParabolicCylinder 1 0)

private theorem forwardParabolicBoundary_subset_closedParabolicCylinder_one
    {d : ℕ} :
    forwardParabolicBoundary 1 (0 : PDE.Vec d) ⊆
      closedParabolicCylinder 1 0 := by
  intro z hz
  rcases mem_forwardParabolicBoundary_iff.mp hz with hinitial | hlateral
  · rcases z with ⟨t, v⟩
    rcases hinitial with ⟨ht, hv⟩
    change t = 0 at ht
    change v ∈ PDE.euclideanClosedBall (0 : PDE.Vec d) 1 at hv
    subst t
    exact mem_closedParabolicCylinder_iff.mpr
      ⟨by norm_num, by norm_num, hv⟩
  · rcases z with ⟨t, v⟩
    rcases hlateral with ⟨ht0, ht1, hsphere⟩
    exact mem_closedParabolicCylinder_iff.mpr
      ⟨ht0, ht1, by
        change PDE.euclideanSqDist v (0 : PDE.Vec d) ≤ 1 ^ 2
        change PDE.euclideanSqDist v (0 : PDE.Vec d) = 1 ^ 2 at hsphere
        exact hsphere.le⟩

/-- The local forward boundary is contained in the compact local ABP closure. -/
theorem localABPForwardBoundary_subset_closure {d : ℕ} (v0 : PDE.Vec d) :
    localABPForwardBoundary v0 ⊆ localABPClosure v0 := by
  unfold localABPForwardBoundary localABPClosure
  exact Set.image_mono forwardParabolicBoundary_subset_closedParabolicCylinder_one

/-- The terminal centre is in the local ABP closure. -/
theorem localABPTarget_mem_closure {d : ℕ} (v0 : PDE.Vec d) :
    (1, v0) ∈ localABPClosure v0 := by
  refine ⟨(1, 0), ?_, ?_⟩
  · exact mem_closedParabolicCylinder_iff.mpr ⟨by norm_num, by norm_num, by
      change PDE.euclideanSqDist (0 : PDE.Vec d) 0 ≤ 1 ^ 2
      simp⟩
  · simp only [localABPAffine, parabolicAffine]
    ext
    · norm_num [div_pow]
    · simp

private theorem mapsTo_localABPInterior {d : ℕ} (v0 : PDE.Vec d) :
    MapsTo (localABPAffine v0) (parabolicInterior 1 0) (localABPInterior v0) :=
  Set.mapsTo_image _ _

private theorem mapsTo_localABPForwardBoundary {d : ℕ} (v0 : PDE.Vec d) :
    MapsTo (localABPAffine v0) (forwardParabolicBoundary 1 0)
      (localABPForwardBoundary v0) :=
  Set.mapsTo_image _ _

private theorem localABPAffine_referenceTarget {d : ℕ} (v0 : PDE.Vec d) :
    localABPAffine v0 (1, 0) = (1, v0) := by
  simp only [localABPAffine, parabolicAffine]
  ext
  · norm_num [div_pow]
  · simp

private theorem referenceTarget_mem_closedParabolicCylinder {d : ℕ} :
    (1, 0) ∈ closedParabolicCylinder 1 (0 : PDE.Vec d) := by
  exact mem_closedParabolicCylinder_iff.mpr ⟨by norm_num, by norm_num, by
    change PDE.euclideanSqDist (0 : PDE.Vec d) 0 ≤ 1 ^ 2
    simp⟩

private theorem eventualEq_nhds_of_eventualEq_nhdsSet {α : Type*}
    {β : Type*} [TopologicalSpace α] {K : Set α} {f g : α → β} {x : α}
    (hx : x ∈ K) (hfg : f =ᶠ[𝓝ˢ K] g) : f =ᶠ[𝓝 x] g :=
  (eventually_nhdsSet_iff_forall.mp hfg x hx)

/-- Common proof of the local ABP consequences with ellipticity on the compact
cylinder actually used by the cutoff-and-pullback construction. -/
private theorem exists_local_abp_inner_cylinder_core
    (d : ℕ) (hd : 0 < d) (lam : ℝ) (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (U : Set (TimeVelocity d)) (B : CoefficientField d)
        (w F : TimeVelocity d → ℝ) (v0 : PDE.Vec d) (rho : ℝ),
        IsOpen U →
        localABPClosure v0 ⊆ U →
        IsContinuousCoefficientOn B U →
        ContDiffOn ℝ 2 w U →
        ContinuousOn F U →
        HasLowerEllipticityOn lam B (localABPClosure v0) →
        IsNonnegativeOn F (localABPInterior v0) →
        (∀ z ∈ localABPInterior v0,
          parabolicOperator B w z + rho * w z ≤ F z) →
        (∀ z ∈ localABPForwardBoundary v0, w z ≤ 0) →
        w (1, v0) ≤
          C * (1 / 2 : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1)) *
            Real.exp (-rho / 4) *
              parabolicLpNormOn d
                (fun z => Real.exp (rho * (z.1 - 3 / 4)) * F z)
                (localABPInterior v0) := by
  obtain ⟨C, hC, hABP⟩ :=
    parabolic_abp_unit_of_lower_ellipticity d hd lam hlam
  refine ⟨C, hC, ?_⟩
  intro U B w F v0 rho hU hKU hB hw hF hLow hFnonneg hineq hboundary
  let K : Set (TimeVelocity d) := localABPClosure v0
  obtain ⟨b, hbSmooth, hbOne, hbSupport⟩ :=
    exists_smooth_cutoff_tsupport_subset (isCompact_localABPClosure v0) hU hKU
  let ew : TimeVelocity d → ℝ := exponentialConjugate rho (3 / 4) w
  let H : TimeVelocity d → ℝ := fun z => exponentialTimeWeight rho (3 / 4) z * F z
  let g : TimeVelocity d → ℝ := fun z => b z * ew z
  let G : TimeVelocity d → ℝ := fun z => b z * H z
  let Bbar : CoefficientField d := cutoffExtendCoefficient b B lam
  have hH : ContinuousOn H U := by
    dsimp only [H]
    exact (contDiff_exponentialTimeWeight rho (3 / 4)).continuous.continuousOn.mul hF
  have hEW : ContDiffOn ℝ 2 ew U := by
    dsimp only [ew]
    exact contDiffOn_exponentialConjugate hw
  have hconj : IsParabolicSubsolutionOn B H ew (localABPInterior v0) := by
    intro z hz
    have hzK : z ∈ K := localABPInterior_subset_closure v0 hz
    have hzU : z ∈ U := hKU hzK
    dsimp only [H, ew]
    rw [parabolicOperator_exponentialConjugate B
      (hw.contDiffAt (hU.mem_nhds hzU))]
    exact mul_le_mul_of_nonneg_left (hineq z hz)
      (exponentialTimeWeight_pos rho (3 / 4) z).le
  have hg : ContDiff ℝ 2 g := by
    dsimp only [g]
    exact contDiff_cutoff_mul_of_tsupport_subset hU
      (hbSmooth.of_le (by
        change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)) hbSupport hEW
  have hG : Continuous G := by
    dsimp only [G]
    exact continuous_cutoff_mul_of_tsupport_subset hU
      (hbSmooth.of_le (by
        change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)) hbSupport hH
  have hBbar : IsContinuousCoefficient Bbar := by
    dsimp only [Bbar]
    exact continuous_coefficientAt_cutoffExtendCoefficient hU
      (hbSmooth.of_le (by
        change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)) hbSupport hB
  have hgEq : g =ᶠ[𝓝ˢ K] ew := by
    dsimp only [g]
    exact cutoff_mul_eventuallyEq hbOne
  have hGEq : G =ᶠ[𝓝ˢ K] H := by
    dsimp only [G]
    exact cutoff_mul_eventuallyEq hbOne
  have hBbarEq : coefficientAt Bbar =ᶠ[𝓝ˢ K] coefficientAt B := by
    dsimp only [Bbar]
    exact coefficientAt_cutoffExtendCoefficient_eventuallyEq hbOne
  have hlocalSub : IsParabolicSubsolutionOn Bbar G g (localABPInterior v0) := by
    intro x hx
    have hxK : x ∈ K := localABPInterior_subset_closure v0 hx
    have hgx := eventualEq_nhds_of_eventualEq_nhdsSet hxK hgEq
    have hGx := eventualEq_nhds_of_eventualEq_nhdsSet hxK hGEq
    have hBx := eventualEq_nhds_of_eventualEq_nhdsSet hxK hBbarEq
    have hoperator : parabolicOperator Bbar g x = parabolicOperator B ew x :=
      parabolicOperator_congr_of_eventuallyEq_of_coefficientAt_eventuallyEq hBx hgx
    calc
      parabolicOperator Bbar g x = parabolicOperator B ew x := hoperator
      _ ≤ H x := hconj x hx
      _ = G x := (hGx.self_of_nhds).symm
  let a : TimeVelocity d → TimeVelocity d := localABPAffine v0
  let Bhat : CoefficientField d := pullbackCoefficient Bbar (3 / 4) v0 (1 / 2)
  let uhat : TimeVelocity d → ℝ := pullbackScalar g (3 / 4) v0 (1 / 2)
  let fhat : TimeVelocity d → ℝ := fun z => (1 / 2 : ℝ) ^ 2 * G (a z)
  have ha : a = parabolicAffine (3 / 4) v0 (1 / 2) := rfl
  have haCont : Continuous a := by
    dsimp only [a, localABPAffine]
    exact (contDiff_parabolicAffine (3 / 4) v0 (1 / 2)).continuous
  have hBhat : IsContinuousCoefficient Bhat := by
    dsimp only [Bhat]
    change Continuous ((coefficientAt Bbar) ∘ a)
    exact hBbar.comp haCont
  have huhat : ContDiff ℝ 2 uhat := by
    dsimp only [uhat]
    change ContDiff ℝ 2 (g ∘ a)
    exact hg.comp (contDiff_parabolicAffine (3 / 4) v0 (1 / 2))
  have hfhat : Continuous fhat := by
    dsimp only [fhat]
    exact continuous_const.mul (hG.comp haCont)
  have hLowHat : ∀ z ∈ closedParabolicCylinder 1 (0 : PDE.Vec d),
      lam • (1 : PDE.Mat d) ≤ coefficientAt Bhat z := by
    intro z hz
    have hzK : a z ∈ K := ⟨z, hz, rfl⟩
    have hBz := eventualEq_nhds_of_eventualEq_nhdsSet hzK hBbarEq
    change lam • (1 : PDE.Mat d) ≤ coefficientAt Bbar (a z)
    rw [hBz.self_of_nhds]
    exact hLow (a z) hzK
  have hsubHat : IsParabolicSubsolutionOn Bhat fhat uhat
      (parabolicInterior 1 (0 : PDE.Vec d)) := by
    intro z hz
    have hza : a z ∈ localABPInterior v0 := ⟨z, hz, rfl⟩
    change parabolicOperator Bhat uhat z ≤ (1 / 2 : ℝ) ^ 2 * G (a z)
    rw [show parabolicOperator Bhat uhat z =
        (1 / 2 : ℝ) ^ 2 * parabolicOperator Bbar g (a z) by
      dsimp only [Bhat, uhat, a]
      exact parabolicOperator_pullbackScalar hg.contDiffAt]
    exact mul_le_mul_of_nonneg_left (hlocalSub (a z) hza) (sq_nonneg (1 / 2 : ℝ))
  have hboundaryHat : ∀ z ∈ forwardParabolicBoundary 1 (0 : PDE.Vec d),
      uhat z ≤ 0 := by
    intro z hz
    have hza : a z ∈ localABPForwardBoundary v0 := ⟨z, hz, rfl⟩
    have hzaK : a z ∈ K := localABPForwardBoundary_subset_closure v0 hza
    have hgz := eventualEq_nhds_of_eventualEq_nhdsSet hzaK hgEq
    have hew : ew (a z) ≤ 0 := by
      dsimp only [ew]
      exact (exponentialConjugate_nonpos_iff rho (3 / 4) w (a z)).mpr
        (hboundary (a z) hza)
    change uhat z ≤ 0
    change g (a z) ≤ 0
    rw [hgz.self_of_nhds]
    exact hew
  have hABPPoint := hABP (T := 1) (by norm_num) (by norm_num)
    (0 : PDE.Vec d) Bhat fhat uhat hBhat hfhat huhat hLowHat hsubHat hboundaryHat
      (1, 0) referenceTarget_mem_closedParabolicCylinder
  have hmaxAE :
      (fun z => max (fhat z) 0) =ᵐ[volume.restrict (parabolicInterior 1 (0 : PDE.Vec d))]
        fun z => (1 / 2 : ℝ) ^ 2 * H (a z) := by
    filter_upwards [ae_restrict_mem (measurableSet_parabolicInterior 1 (0 : PDE.Vec d))]
      with z hz
    have hza : a z ∈ localABPInterior v0 := ⟨z, hz, rfl⟩
    have hzaK : a z ∈ K := localABPInterior_subset_closure v0 hza
    have hGz := eventualEq_nhds_of_eventualEq_nhdsSet hzaK hGEq
    have hHnonneg : 0 ≤ H (a z) := by
      dsimp only [H]
      exact mul_nonneg (exponentialTimeWeight_pos rho (3 / 4) (a z)).le
        (hFnonneg (a z) hza)
    dsimp only [fhat]
    rw [hGz.self_of_nhds, max_eq_left]
    exact mul_nonneg (sq_nonneg (1 / 2 : ℝ)) hHnonneg
  have hnormMax :
      parabolicLpNormOn d (fun z => max (fhat z) 0)
          (parabolicInterior 1 (0 : PDE.Vec d)) =
        parabolicLpNormOn d (fun z => (1 / 2 : ℝ) ^ 2 * H (a z))
          (parabolicInterior 1 (0 : PDE.Vec d)) := by
    unfold parabolicLpNormOn parabolicELpNormOn
    exact congrArg ENNReal.toReal (eLpNorm_congr_ae hmaxAE)
  have hnorm := parabolicLpNormOn_pullback (d := d) (3 / 4) v0
    (by norm_num : 0 < (1 / 2 : ℝ)) H (parabolicInterior 1 (0 : PDE.Vec d))
  have hnorm' :
      parabolicLpNormOn d (fun z => (1 / 2 : ℝ) ^ 2 * H (a z))
          (parabolicInterior 1 (0 : PDE.Vec d)) =
        (1 / 2 : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1)) *
          parabolicLpNormOn d H (localABPInterior v0) := by
    simpa only [a, H, localABPAffine, localABPInterior] using hnorm
  have htargetK : (1, v0) ∈ K := by
    dsimp only [K]
    exact localABPTarget_mem_closure v0
  have htargetg := eventualEq_nhds_of_eventualEq_nhdsSet htargetK hgEq
  have htargetWeight : exponentialTimeWeight rho (3 / 4) (1, v0) =
      Real.exp (rho / 4) := by
    rw [exponentialTimeWeight_apply]
    congr 1
    ring
  have hweighted :
      exponentialTimeWeight rho (3 / 4) (1, v0) * w (1, v0) ≤
        C * (1 / 2 : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1)) *
          parabolicLpNormOn d H (localABPInterior v0) := by
    have huTarget : uhat (1, 0) = g (1, v0) := by
      change g (parabolicAffine (3 / 4) v0 (1 / 2) (1, 0)) = g (1, v0)
      exact congrArg g (by
        simpa only [localABPAffine] using localABPAffine_referenceTarget v0)
    change uhat (1, 0) ≤ _ at hABPPoint
    rw [huTarget, htargetg.self_of_nhds] at hABPPoint
    change exponentialTimeWeight rho (3 / 4) (1, v0) * w (1, v0) ≤ _
      at hABPPoint
    rw [hnormMax, hnorm'] at hABPPoint
    simpa only [mul_assoc] using hABPPoint
  have hcancel : Real.exp (-rho / 4) * Real.exp (rho / 4) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  calc
    w (1, v0) = Real.exp (-rho / 4) *
        (exponentialTimeWeight rho (3 / 4) (1, v0) * w (1, v0)) := by
      rw [htargetWeight, ← mul_assoc, hcancel, one_mul]
    _ ≤ Real.exp (-rho / 4) *
        (C * (1 / 2 : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1)) *
          parabolicLpNormOn d H (localABPInterior v0)) :=
      mul_le_mul_of_nonneg_left hweighted (Real.exp_pos _).le
    _ = C * (1 / 2 : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1)) *
          Real.exp (-rho / 4) *
            parabolicLpNormOn d
              (fun z => Real.exp (rho * (z.1 - 3 / 4)) * F z)
              (localABPInterior v0) := by
      dsimp only [H, exponentialTimeWeight]
      ring

/-- The local ABP consequence on the source inner cylinder.  The constant is
chosen before the domain, coefficient, functions, centre, and spectral
parameter, and therefore depends only on `d` and the lower ellipticity
constant `lam`. -/
theorem exists_local_abp_inner_cylinder
    (d : ℕ) (hd : 0 < d) (lam : ℝ) (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (U : Set (TimeVelocity d)) (B : CoefficientField d)
        (w F : TimeVelocity d → ℝ) (v0 : PDE.Vec d) (rho : ℝ),
        IsOpen U →
        localABPClosure v0 ⊆ U →
        IsContinuousCoefficientOn B U →
        ContDiffOn ℝ 2 w U →
        ContinuousOn F U →
        HasLowerEllipticityOn lam B U →
        IsNonnegativeOn F (localABPInterior v0) →
        (∀ z ∈ localABPInterior v0,
          parabolicOperator B w z + rho * w z ≤ F z) →
        (∀ z ∈ localABPForwardBoundary v0, w z ≤ 0) →
        w (1, v0) ≤
          C * (1 / 2 : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1)) *
            Real.exp (-rho / 4) *
              parabolicLpNormOn d
                (fun z => Real.exp (rho * (z.1 - 3 / 4)) * F z)
                (localABPInterior v0) := by
  obtain ⟨C, hC, hcore⟩ :=
    exists_local_abp_inner_cylinder_core d hd lam hlam
  refine ⟨C, hC, ?_⟩
  intro U B w F v0 rho hU hKU hB hw hF hLow hFnonneg hineq hboundary
  exact hcore U B w F v0 rho hU hKU hB hw hF (hLow.mono hKU) hFnonneg hineq hboundary

/-- The local ABP consequence requiring lower ellipticity only on the compact
local cylinder used by its cutoff-and-pullback proof. -/
theorem exists_local_abp_inner_cylinder_of_lower_ellipticity_on_closure
    (d : ℕ) (hd : 0 < d) (lam : ℝ) (hlam : 0 < lam) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (U : Set (TimeVelocity d)) (B : CoefficientField d)
        (w F : TimeVelocity d → ℝ) (v0 : PDE.Vec d) (rho : ℝ),
        IsOpen U →
        localABPClosure v0 ⊆ U →
        IsContinuousCoefficientOn B U →
        ContDiffOn ℝ 2 w U →
        ContinuousOn F U →
        HasLowerEllipticityOn lam B (localABPClosure v0) →
        IsNonnegativeOn F (localABPInterior v0) →
        (∀ z ∈ localABPInterior v0,
          parabolicOperator B w z + rho * w z ≤ F z) →
        (∀ z ∈ localABPForwardBoundary v0, w z ≤ 0) →
        w (1, v0) ≤
          C * (1 / 2 : ℝ) ^ ((d : ℝ) / ((d : ℝ) + 1)) *
            Real.exp (-rho / 4) *
              parabolicLpNormOn d
                (fun z => Real.exp (rho * (z.1 - 3 / 4)) * F z)
                (localABPInterior v0) := by
  obtain ⟨C, hC, hcore⟩ :=
    exists_local_abp_inner_cylinder_core d hd lam hlam
  exact ⟨C, hC, hcore⟩

end HypoellipticAleksandrov.Parabolic

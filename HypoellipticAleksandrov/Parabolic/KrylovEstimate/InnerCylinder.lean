module

public import HypoellipticAleksandrov.Parabolic.KrylovCylinder
public import HypoellipticAleksandrov.Parabolic.Scaling
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.TietzeExtension

/-! # Inward compression of the unit Krylov cylinder -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.KrylovEstimate
open Set Filter
open scoped Topology

/-- Parabolic compression about the time midpoint and velocity centre. -/
def innerMap {N : ℕ} (t₀ h : ℝ) (v₀ : PDE.Vec N) (ρ : ℝ) :
    TimeVelocity N → TimeVelocity N :=
  parabolicAffine (t₀ - h + (1 - ρ ^ 2) * h / 2) v₀ ρ

/-- Strict compression sends the closed reference cylinder into the open source cylinder. -/
theorem innerMap_mapsTo
    {N : ℕ} (t₀ h : ℝ) (v₀ : PDE.Vec N) (hh : 0 < h)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    Set.MapsTo (innerMap t₀ h v₀ ρ)
      (closedParabolicCylinder h (0 : PDE.Vec N))
      (krylovCylinder t₀ h v₀) := by
  intro z hz
  rcases hz with ⟨hztime, hzvel⟩
  have hr2 : ρ ^ 2 < 1 := by nlinarith
  have hmargin : 0 < (1 - ρ ^ 2) * h / 2 := by positivity
  change (t₀ - h < t₀ - h + (1 - ρ ^ 2) * h / 2 + ρ ^ 2 * z.1 ∧
    t₀ - h + (1 - ρ ^ 2) * h / 2 + ρ ^ 2 * z.1 < t₀) ∧ _
  constructor
  · constructor
    · nlinarith [sq_nonneg ρ, hztime.1]
    · nlinarith [mul_le_mul_of_nonneg_left hztime.2 (sq_nonneg ρ)]
  · change PDE.euclideanSqDist (v₀ + ρ • z.2) v₀ < 1 ^ 2
    have hd : PDE.euclideanSqDist (v₀ + ρ • z.2) v₀ =
        ρ ^ 2 * PDE.euclideanSqDist z.2 0 := by
      simp only [PDE.euclideanSqDist, add_sub_cancel_left, PDE.vecNormSq_smul, sub_zero]
    rw [hd]
    exact (mul_le_mul_of_nonneg_left hzvel (sq_nonneg ρ)).trans_lt (by simpa using hr2)

/-- At radius one, the forward boundary maps to the original bottom and lateral faces. -/
theorem innerMap_one_boundary
    {N : ℕ} (t₀ h : ℝ) (v₀ : PDE.Vec N) :
    Set.MapsTo (innerMap t₀ h v₀ 1)
      (forwardParabolicBoundary h (0 : PDE.Vec N))
      (krylovParabolicBoundary t₀ h v₀) := by
  intro z hz
  have hm : innerMap t₀ h v₀ 1 z = (t₀ - h + z.1, v₀ + z.2) := by
    simp only [innerMap, parabolicAffine, one_pow, sub_self, zero_mul, zero_div,
      add_zero, one_mul, one_smul]
  rw [hm]
  rcases hz with hz | hz
  · left
    rcases hz with ⟨ht, hv⟩
    change z.1 = 0 at ht
    refine ⟨?_, ?_⟩
    · simpa only [ht, add_zero] using (Set.mem_singleton (t₀ - h))
    · simpa only [PDE.euclideanClosedBall, PDE.euclideanSqDist, Set.mem_setOf_eq,
        add_sub_cancel_left, sub_zero] using hv
  · right
    rcases hz with ⟨ht, hv⟩
    refine ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    simpa only [PDE.euclideanSphere, PDE.euclideanSqDist, Set.mem_setOf_eq,
      add_sub_cancel_left, sub_zero] using hv

/-- Compression can approximate the uncompressed values uniformly on the closed cylinder. -/
theorem exists_innerMap_value_close
    {N : ℕ} (t₀ h : ℝ) (v₀ : PDE.Vec N) (hh : 0 < h)
    (u : TimeVelocity N → ℝ)
    (hu : ContinuousOn u (krylovClosedCylinder t₀ h v₀))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      ∀ z ∈ closedParabolicCylinder h (0 : PDE.Vec N),
        |u (innerMap t₀ h v₀ ρ z) - u (innerMap t₀ h v₀ 1 z)| ≤ ε := by
  let K := krylovClosedCylinder t₀ h v₀
  have hK : IsCompact K := isCompact_Icc.prod (PDE.isCompact_euclideanClosedBall v₀ (by norm_num))
  let f : C(K, ℝ) := ⟨fun z => u z, hu.domRestrict⟩
  obtain ⟨g, hg⟩ := f.exists_extension' hK.isClosed.isClosedEmbedding_subtypeVal
  have hgeq (z : TimeVelocity N) (hz : z ∈ K) : g z = u z := congrFun hg ⟨z, hz⟩
  let K0 := closedParabolicCylinder h (0 : PDE.Vec N)
  have hK0 : IsCompact K0 := isCompact_closedParabolicCylinder h 0
  letI : CompactSpace K0 := isCompact_iff_compactSpace.mp hK0
  let F : ℝ → K0 → ℝ := fun ρ z => g (innerMap t₀ h v₀ ρ z)
  have hc : Continuous (Function.uncurry F) := by
    apply g.continuous.comp
    dsimp [F, innerMap, parabolicAffine]
    fun_prop
  have he : ∀ᶠ ρ in 𝓝 (1 : ℝ), ∀ z : K0, dist (F 1 z) (F ρ z) < ε :=
    (Metric.tendstoUniformly_iff.mp (hc.tendstoUniformly F 1)) ε hε
  have he' : ∀ᶠ ρ in 𝓝[<] (1 : ℝ), ∀ z : K0, dist (F 1 z) (F ρ z) < ε :=
    he.filter_mono nhdsWithin_le_nhds
  have hp : ∀ᶠ ρ : ℝ in 𝓝[<] 1, 0 < ρ :=
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  obtain ⟨ρ, hclose, hpos, hlt⟩ :=
    (he'.and (hp.and (self_mem_nhdsWithin : ∀ᶠ ρ : ℝ in 𝓝[<] 1, ρ ∈ Iio 1))).exists
  refine ⟨ρ, hpos, hlt, fun z hz => ?_⟩
  have hzρ := innerMap_mapsTo t₀ h v₀ hh hpos hlt hz
  have hzρK : innerMap t₀ h v₀ ρ z ∈ K :=
    ⟨⟨hzρ.1.1.le, hzρ.1.2.le⟩, show PDE.euclideanSqDist _ v₀ ≤ 1 ^ 2 from hzρ.2.le⟩
  have hz1K : innerMap t₀ h v₀ 1 z ∈ K := by
    rcases hz with ⟨ht, hv⟩
    change (t₀ - h ≤ _ ∧ _ ≤ t₀) ∧ _
    simp only [innerMap, parabolicAffine, one_pow, sub_self, zero_mul, zero_div,
      add_zero, one_mul, one_smul]
    refine ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    simpa only [PDE.euclideanClosedBall, PDE.euclideanSqDist, Set.mem_setOf_eq,
      add_sub_cancel_left, sub_zero] using hv
  have hdist := hclose ⟨z, hz⟩
  dsimp [F] at hdist
  rw [hgeq _ hzρK, hgeq _ hz1K, Real.dist_eq, abs_sub_comm] at hdist
  exact hdist.le

end HypoellipticAleksandrov.Parabolic.KrylovEstimate

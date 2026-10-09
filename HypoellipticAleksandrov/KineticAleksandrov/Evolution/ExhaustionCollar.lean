module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCollarGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCauchyTruncation
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierTwo

/-!
# The pre-construction collar estimate on actual finite ellipsoids

Compact comparison is applied on the intersection of the actual finite closed ellipsoid
cylinder with the collar. Every artificial lateral face has the supplied zero datum.
The estimate does not require a full-domain solution or Hörmander smoothing.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter
open scoped Topology MatrixOrder

/-- The actual finite Dirichlet solution obeys the collar estimate uniformly in the
transported truncation radius. The lower comparison time is strictly inside its slab. -/
theorem abs_le_collar_straightened_dirichlet
    {n : ℕ} {lam Lam : ℝ} {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    (hlam : 0 < lam) (hB : HasEverywhereLoewnerBounds lam Lam B)
    (hBs : IsSmoothFullKineticCoefficient B) (hbs : IsSmoothDrift b)
    {a α τ r R d L C ε : ℝ} (haα : a < α) (hατ : α < τ)
    (hr : 0 < r) (hR : 0 < R) (hd : 0 < d) (hdr : d < r)
    {g : ℝ → PDE.Vec n} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hL : 0 ≤ L)
    (hgL : ∀ s t, PDE.vecEuclideanNorm (g s - g t) ≤ L * |s - t|)
    (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (F : BoundedBorel (EvolutionAmbientState n)) (hFC : ∀ q, |F q| ≤ C)
    (hsupp : ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
      2 * d ≤ r - PDE.vecEuclideanNorm (q.1 - g τ))
    (u : TimeVelocity (n + n) → ℝ)
    (hu : IsClassicalBackwardDirichletSolution a τ
      (openEllipsoid (straightenedEllipsoidMatrix n r R))
      (straightenedCoefficient B g ε) (straightenedDrift b g)
      (fun _ _ => 0) (fun _ _ => 0)
      (fun x => F (g τ + spatialY x, spatialZ x)) (fun _ => 0) u) :
    ∀ p ∈ straightenedPoint g ⁻¹' scalarParabolicClosedCylinder α τ
      (openEllipsoid (straightenedEllipsoidMatrix n r R)),
      (r - d) ^ 2 ≤ centreSq 0 g p →
      |straightenedPullback g u p| ≤ collarSupersolution 0 r d L lam C g p := by
  let D := openEllipsoid (straightenedEllipsoidMatrix n r R)
  let K := (straightenedPoint g ⁻¹' scalarParabolicClosedCylinder α τ D) ∩
    {p | (r - d) ^ 2 ≤ centreSq 0 g p}
  let A := {p : KineticPoint n | p.time ∈ Ico α τ ∧ (straightenedPoint g p).2 ∈ D} ∩
    {p | (r - d) ^ 2 < centreSq 0 g p}
  let v := straightenedPullback g u
  let G := collarSupersolution 0 r d L lam C g
  have hDo : IsOpen D := isOpen_straightenedEllipsoid n hr hR
  have hκ : 0 < collarKappa L lam := div_pos (by linarith) hlam
  have hcoef : 0 ≤ C / barrierW (collarKappa L lam) d :=
    div_nonneg hC (barrierW_pos hκ hd).le
  have hKc : IsCompact K :=
    (isCompact_straightened_closedCylinder (isBounded_straightenedEllipsoid n hr hR)
      hg.continuous α τ).inter_right
      (isClosed_le continuous_const (continuous_centreSq 0 hg.continuous))
  have hsub (p : KineticPoint n) (hp : p ∈ K) :
      straightenedPoint g p ∈ scalarParabolicClosedCylinder a τ D :=
    ⟨⟨haα.le.trans hp.1.1.1, hp.1.1.2⟩, hp.1.2⟩
  have hv : ContinuousOn v K :=
    hu.1.comp (continuous_straightenedPoint hg.continuous).continuousOn hsub
  have hbound (p : KineticPoint n) (hp : p ∈ K) : |v p| ≤ C :=
    abs_le_straightened_dirichlet hlam hB hBs hbs (haα.trans hατ) hr hR hg hε
      F u hu hC hFC _ (hsub p hp)
  have hGn (p : KineticPoint n) (hp : p ∈ K) : 0 ≤ G p := by
    have hY := vecNormSq_spatialY_le_of_mem_closure_straightenedEllipsoid hr hR hp.1.2
    have hS : centreSq 0 g p ≤ r ^ 2 := by
      simpa only [centreSq, straightenedPoint, spatialY_spatialPack, add_zero] using hY
    exact mul_nonneg hcoef (collarBarrier_nonneg hκ hr.le hS)
  have hreg (p : KineticPoint n) (hp : p ∈ A) :
      IsSliceRegularAt v p ∧ viscousTransportedOperator B b ε v p = 0 :=
    straightenedPullback_dirichlet_sliceRegular hDo hg hu p
      ⟨⟨haα.trans_le hp.1.1.1, hp.1.1.2⟩, hp.1.2⟩
  have hSpos (p : KineticPoint n) (hp : p ∈ A) :
      0 < PDE.vecNormSq (p.position - (g p.time + 0)) :=
    lt_of_le_of_lt (sq_nonneg _) hp.2
  have hGreg (p : KineticPoint n) (hp : p ∈ A) : IsSliceRegularAt G p :=
    (isSliceRegularAt_collarBarrier (collarKappa L lam) r
      (((hg.differentiable (by simp)) p.time).add_const 0) (hSpos p hp)).const_mul _
  have hGop (p : KineticPoint n) (hp : p ∈ A) :
      viscousTransportedOperator B b ε G p ≤ 0 := by
    have hgd := (hg.differentiable (by simp)) p.time
    have hm := hgd.hasDerivAt.add_const (0 : PDE.Vec n)
    have hmL := vecEuclideanNorm_le_of_hasDerivAt_lipschitz hL hgd.hasDerivAt hgL
    have hn := viscousTransportedOperator_collarBarrier_nonpos (b := b) ε hκ hlam.le
      (div_mul_cancel₀ _ hlam.ne') r hm hmL (hSpos p hp) (hB _ _ _).1
    change viscousTransportedOperator B b ε
      (fun q => C / barrierW (collarKappa L lam) d *
        collarBarrier (collarKappa L lam) r (fun t => g t + 0) q) p ≤ 0
    rw [viscousTransportedOperator_const_mul _
      (isSliceRegularAt_collarBarrier (collarKappa L lam) r hm.differentiableAt (hSpos p hp))]
    exact mul_nonpos_of_nonneg_of_nonpos hcoef hn
  have side (s : ℝ) (hs : s = 1 ∨ s = -1) : ∀ p ∈ K, s * v p ≤ G p := by
    have hmax := le_zero_of_viscous_nonneg_compact (B := B) (b := b) (ε := ε)
      (K := K) (D := A) (w := fun p => s * v p - G p) (T := τ) hε hKc
      (fun p hp => hp.1.1.2)
      ((hv.const_smul s).sub
        (continuous_collarSupersolution 0 r d L lam C hg.continuous).continuousOn) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      have := hmax p hp
      linarith
    · intro p hp
      have hf := eventually_future_mem_straightened_closedCylinder hDo hg.continuous hp.1
      have ho : ∀ᶠ q in 𝓝 p, (r - d) ^ 2 < centreSq 0 g q :=
        (isOpen_lt continuous_const (continuous_centreSq 0 hg.continuous)).mem_nhds hp.2
      filter_upwards [hf, ho] with q hq hqS hqt
      exact ⟨hq hqt, hqS.le⟩
    · intro p hp
      exact ((hreg p hp).1.const_mul s).sub (hGreg p hp)
    · intro p _
      exact posSemidef_of_hasEverywhereLoewnerBounds hlam.le hB _ _ _
    · intro p hp
      rw [viscousTransportedOperator_sub ((hreg p hp).1.const_mul s) (hGreg p hp),
        viscousTransportedOperator_const_mul s (hreg p hp).1, (hreg p hp).2, mul_zero]
      exact sub_nonneg.mpr (hGop p hp)
    · intro p hp hn
      by_cases ht : p.time = τ
      · have hz := hu.2.2.2.1 (straightenedPoint g p).2 hp.1.2
        have he : v p = F (p.position, p.velocity) := by
          simpa only [v, straightenedPullback, straightenedPoint, ht,
            spatialY_spatialPack, spatialZ_spatialPack, add_sub_cancel] using hz
        have hF0 := terminalDatum_eq_zero_of_collar hd hdr
          (by simpa only [add_zero] using hsupp) ht hp.2
        rw [he, hF0, mul_zero]
        exact sub_nonpos.mpr (hGn p hp)
      by_cases hx : (straightenedPoint g p).2 ∈ D
      · have hS : centreSq 0 g p = (r - d) ^ 2 :=
          le_antisymm (not_lt.mp (fun h => hn
            ⟨⟨⟨hp.1.1.1, lt_of_le_of_ne hp.1.1.2 ht⟩, hx⟩, h⟩)) hp.2
        have he : G p = C := collarSupersolution_inner hdr hκ hd hS
        have hb := hbound p hp
        rw [he]
        rcases hs with rfl | rfl <;> linarith [le_abs_self (v p), neg_le_abs (v p)]
      · have hfr : (straightenedPoint g p).2 ∈ frontier D := by
          rw [hDo.frontier_eq]
          exact ⟨hp.1.2, hx⟩
        have hz := hu.2.2.2.2 (straightenedPoint g p)
          ⟨⟨haα.le.trans hp.1.1.1, hp.1.1.2⟩, hfr⟩
        change v p = 0 at hz
        rw [hz, mul_zero]
        exact sub_nonpos.mpr (hGn p hp)
  intro p hp hS
  have h1 := side 1 (Or.inl rfl) p ⟨hp, hS⟩
  have h2 := side (-1) (Or.inr rfl) p ⟨hp, hS⟩
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end HypoellipticAleksandrov.KineticAleksandrov

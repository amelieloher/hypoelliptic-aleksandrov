module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonMaximum
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonStrict
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonBoundary
import Mathlib.Topology.Order.OrderClosed

/-! # The kinetic comparison principle on the exact exit boundary -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov.Parabolic Set

/-- The terminal face supplies an exit-boundary point for every positive-radius cylinder. -/
theorem comparison_exitBoundary_nonempty {d : ℕ}
    (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) :
    (exitBoundary Z₀ R hR).Nonempty := by
  let P : KineticPoint d := ⟨Z₀.time + R ^ 2,Z₀.position + R ^ 2 • Z₀.velocity,Z₀.velocity⟩
  refine ⟨P,(mem_exitBoundary_iff Z₀ P R hR).2 ⟨?_,Or.inl rfl⟩⟩
  rw [comparison_closure_forwardCylinder_eq]
  have hx : relativePosition Z₀ P = 0 := by
    ext i
    simp only [relativePosition,P,Pi.sub_apply,Pi.add_apply,Pi.smul_apply,Pi.zero_apply,smul_eq_mul]
    ring
  change (Z₀.time ≤ Z₀.time + R ^ 2 ∧ Z₀.time + R ^ 2 ≤ Z₀.time + R ^ 2) ∧
    relativePosition Z₀ P ∈ PDE.euclideanClosedBall 0 (R ^ 3) ∧
    relativeVelocity Z₀ P ∈ PDE.euclideanClosedBall 0 R
  rw [hx]
  simp [P,relativeVelocity,PDE.euclideanClosedBall,PDE.euclideanSqDist,
    PDE.vecNormSq,PDE.vecDot,sq_nonneg]

/-- A scalar boundary bound propagates for a strict subsolution on a compact cylinder. -/
theorem comparison_strict_compact_bound {d : ℕ}
    (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    {D : Set (KineticPoint d)} (hD : IsOpen D)
    (hQD : closure (forwardCylinder Z₀ R hR) ⊆ D)
    {u : KineticPoint d → ℝ} (hu : IsKineticC112On u D)
    (A : FullKineticCoefficient d)
    (hA : ∀ P ∈ D, (A P.time P.position P.velocity).PosSemidef)
    (hstrict : ∀ P ∈ D, 0 < u P → 0 < forwardKineticOperator A u P)
    (M : ℝ) (hM : 0 ≤ M) (hboundary : ∀ P ∈ exitBoundary Z₀ R hR, u P ≤ M) :
    ∀ P ∈ closure (forwardCylinder Z₀ R hR), u P ≤ M := by
  intro P hP
  by_contra hn
  have hpos := not_le.mp hn
  obtain ⟨p,hp,hmax⟩ := (isCompact_closure_forwardCylinder Z₀ R hR).exists_isMaxOn
    ⟨P,hP⟩ (hu.continuousOn.mono hQD)
  have hpPos : 0 < u p := lt_of_le_of_lt hM (lt_of_lt_of_le hpos (hmax hP))
  have hpexit := comparison_inner_maximum_exclusion Z₀ R hR hD hQD hu A hA hstrict hp hmax hpPos
  exact (not_le.mpr hpos) ((hmax hP).trans (hboundary p hpexit))

/-- Retractions and exhaustion pass a strict comparison bound to the original closure. -/
theorem comparison_boundary_limit {d : ℕ}
    (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (A : FullKineticCoefficient d) (u : KineticPoint d → ℝ)
    (hA : ∀ P ∈ forwardCylinder Z₀ R hR, (A P.time P.position P.velocity).PosSemidef)
    (hcont : ContinuousOn u (closure (forwardCylinder Z₀ R hR)))
    (hreg : IsKineticC112On u (forwardCylinder Z₀ R hR))
    (hstrict : ∀ P ∈ forwardCylinder Z₀ R hR, 0 < u P →
      0 < forwardKineticOperator A u P)
    (M : ℝ) (hM : 0 ≤ M) (hboundary : ∀ P ∈ exitBoundary Z₀ R hR, u P ≤ M) :
    ∀ P ∈ closure (forwardCylinder Z₀ R hR), u P ≤ M := by
  have hb : sSup ((fun P => max (u P) 0) '' exitBoundary Z₀ R hR) ≤ M := by
    apply csSup_le ((comparison_exitBoundary_nonempty Z₀ R hR).image _)
    rintro _ ⟨P,hP,rfl⟩
    exact max_le (hboundary P hP) hM
  have hinterior : ∀ P ∈ forwardCylinder Z₀ R hR, u P ≤ M := by
    intro P hP
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨η,hη,hbound⟩ := comparison_exit_boundary_approx Z₀ R hR u hcont hε
    obtain ⟨τ,hτ,hexhaust⟩ := innerCylinder_exhaustion Z₀ R hR P hP
    let δ := min (R ^ 2 / 4) (min η τ / 2)
    have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
    have hδlt : δ < R ^ 2 / 2 := by
      have h := min_le_left (R ^ 2 / 4) (min η τ / 2)
      dsimp only [δ]
      nlinarith [sq_pos_of_pos hR]
    have hδη : δ < η := by
      have h1 : δ ≤ min η τ / 2 := min_le_right _ _
      have h2 := min_le_left η τ
      linarith only [h1,h2,hη]
    have hδτ : δ < τ := by
      have h1 : δ ≤ min η τ / 2 := min_le_right _ _
      have h2 := min_le_right η τ
      linarith only [h1,h2,hτ]
    obtain ⟨hr,heq⟩ := innerCylinder_eq_forwardCylinder Z₀ R hR δ hδ0 hδlt
    obtain ⟨hr',heqB⟩ := innerExitBoundary_eq_exitBoundary Z₀ R hR δ hδ0 hδlt
    have hQD : closure (forwardCylinder (innerCentre Z₀ δ)
        (innerRatio R hR δ hδ0 hδlt * R) hr) ⊆ forwardCylinder Z₀ R hR := by
      rw [← heq]
      exact closure_innerCylinder_subset Z₀ R hR δ hδ0 hδlt
    have hPinner := hexhaust δ hδ0 hδlt hδτ
    rw [heq] at hPinner
    apply comparison_strict_compact_bound (innerCentre Z₀ δ) _ hr
      (isOpen_forwardCylinder Z₀ R hR) hQD hreg A hA hstrict (M + ε)
      (by linarith only [hM,hε]) ?_ P (subset_closure hPinner)
    intro p hp
    have hpB : p ∈ innerExitBoundary Z₀ R hR δ hδ0 hδlt := by
      rw [heqB]
      exact hp
    exact (le_max_left (u p) 0).trans ((hbound δ hδ0 hδlt hδη p hpB).trans
      (by linarith only [hb]))
  exact le_on_closure hinterior hcont continuousOn_const

/-- The source kinetic comparison principle with pointwise positive semidefinite coefficients. -/
theorem kinetic_comparison {d : ℕ} (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (A : FullKineticCoefficient d) (u : KineticPoint d → ℝ)
    (hA : ∀ P ∈ forwardCylinder Z₀ R hR, (A P.time P.position P.velocity).PosSemidef)
    (hcont : ContinuousOn u (closure (forwardCylinder Z₀ R hR)))
    (hreg : IsKineticC112On u (forwardCylinder Z₀ R hR))
    (hsub : ∀ P ∈ forwardCylinder Z₀ R hR, 0 < u P →
      0 ≤ forwardKineticOperator A u P) :
    ∀ P ∈ closure (forwardCylinder Z₀ R hR), u P ≤
      sSup ((fun P => max (u P) 0) '' exitBoundary Z₀ R hR) := by
  let M := sSup ((fun P => max (u P) 0) '' exitBoundary Z₀ R hR)
  have hbd : BddAbove ((fun P => max (u P) 0) '' exitBoundary Z₀ R hR) :=
    ((isCompact_closure_forwardCylinder Z₀ R hR).bddAbove_image
      (hcont.sup continuousOn_const)).mono (image_mono (fun _ h => h.1))
  have hM : 0 ≤ M := by
    obtain ⟨p,hp⟩ := comparison_exitBoundary_nonempty Z₀ R hR
    exact (le_max_right (u p) 0).trans (le_csSup hbd (mem_image_of_mem _ hp))
  intro P hP
  apply le_of_forall_pos_le_add
  intro ε hε
  let e := ε / (R ^ 2 + 1)
  have he : 0 < e := div_pos hε (by positivity)
  obtain ⟨hle,hregular,hstrict⟩ := comparison_strictification Z₀ R hR A u hreg hsub e he
  have hc : ContinuousOn (fun p => u p + e * (p.time - Z₀.time - R ^ 2))
      (closure (forwardCylinder Z₀ R hR)) :=
    hcont.add (continuous_const.mul
      ((continuous_time.sub continuous_const).sub continuous_const)).continuousOn
  have hbound := comparison_boundary_limit Z₀ R hR A _ hA hc hregular
    (fun p hp hpos => lt_of_lt_of_le he (hstrict p hp hpos)) M hM
    (fun p hp => (hle p hp.1).trans ((le_max_left (u p) 0).trans
      (le_csSup hbd (mem_image_of_mem _ hp)))) P hP
  have ht := (closure_forwardCylinder_bounds Z₀ R hR hP).1.1
  change Z₀.time ≤ P.time at ht
  have herr : e * R ^ 2 ≤ ε := by
    dsimp only [e]
    rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity)]
    nlinarith only [hε.le]
  change u P + e * (P.time - Z₀.time - R ^ 2) ≤ M at hbound
  nlinarith only [hbound,ht,he.le,herr]

end HypoellipticAleksandrov.KineticAleksandrov

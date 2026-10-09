module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCollarGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.FiniteSlabBarriersTerminal

/-!
# Terminal comparison on the actual finite spatial cylinder

This finite-domain core is consumed by ExhaustionTerminal: its lateral-vanishing premise
is proved there from the support window, and its operator bound is discharged globally.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter
open scoped Topology MatrixOrder

/-- Finite-domain terminal comparison from the actual classical Dirichlet solution.
The lateral-vanishing and operator premises are discharged in ExhaustionTerminal. -/
theorem abs_sub_terminalDatum_le_straightened_dirichlet_core
    {n : ℕ} {D : Set (PDE.Vec (n + n))} (hD : IsOpen D) (hDb : Bornology.IsBounded D)
    {lam Lam : ℝ} {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    (hlam : 0 < lam) (hB : HasEverywhereLoewnerBounds lam Lam B)
    {a α τ ε M : ℝ} (haα : a < α) (hε : 0 ≤ ε) (hM0 : 0 ≤ M)
    {g : ℝ → PDE.Vec n} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (F : BoundedBorel (EvolutionAmbientState n))
    (hF : ContDiff ℝ (⊤ : ℕ∞) (F : EvolutionAmbientState n → ℝ))
    (hM : ∀ p : KineticPoint n,
      |viscousTransportedOperator B b ε (fun q => F (q.position, q.velocity)) p| ≤ M)
    (hFl : ∀ p ∈ straightenedPoint g ⁻¹' scalarParabolicLateralFace α τ D,
      F (p.position, p.velocity) = 0)
    (u : TimeVelocity (n + n) → ℝ)
    (hu : IsClassicalBackwardDirichletSolution a τ D
      (straightenedCoefficient B g ε) (straightenedDrift b g)
      (fun _ _ => 0) (fun _ _ => 0) (fun x => F (g τ + spatialY x, spatialZ x))
      (fun _ => 0) u) :
    ∀ p ∈ straightenedPoint g ⁻¹' scalarParabolicClosedCylinder α τ D,
      |straightenedPullback g u p - F (p.position, p.velocity)| ≤ (τ - p.time) * M := by
  let K := straightenedPoint g ⁻¹' scalarParabolicClosedCylinder α τ D
  let A := {p : KineticPoint n | p.time ∈ Ico α τ ∧ (straightenedPoint g p).2 ∈ D}
  let v := straightenedPullback g u
  let f (p : KineticPoint n) := F (p.position, p.velocity)
  have hsub (p : KineticPoint n) (hp : p ∈ K) :
      straightenedPoint g p ∈ scalarParabolicClosedCylinder a τ D :=
    ⟨⟨haα.le.trans hp.1.1, hp.1.2⟩, hp.2⟩
  have hvc : ContinuousOn v K :=
    hu.1.comp (continuous_straightenedPoint hg.continuous).continuousOn hsub
  have hfc : Continuous f := hF.continuous.comp (continuous_position.prodMk continuous_velocity)
  have hr (p : KineticPoint n) (hp : p ∈ A) :
      IsSliceRegularAt v p ∧ viscousTransportedOperator B b ε v p = 0 :=
    straightenedPullback_dirichlet_sliceRegular hD hg hu p
      ⟨⟨haα.trans_le hp.1.1, hp.1.2⟩, hp.2⟩
  have hf (p : KineticPoint n) : IsSliceRegularAt f p := isSliceRegularAt_terminalDatum hF p
  have ht (p : KineticPoint n) : IsSliceRegularAt (fun q => q.time - τ) p :=
    isSliceRegularAt_time_sub τ p
  have side (s : ℝ) (hs : s = 1 ∨ s = -1) :
      ∀ p ∈ K, s * (v p - f p) + M * (p.time - τ) ≤ 0 := by
    apply le_zero_of_viscous_nonneg_compact (B := B) (b := b) (ε := ε)
      (K := K) (D := A) (T := τ) hε (isCompact_straightened_closedCylinder hDb hg.continuous α τ)
      (fun p hp => hp.1.2)
    · exact (((hvc.sub hfc.continuousOn).const_smul s).add
        ((continuous_const.mul (continuous_time.sub continuous_const)).continuousOn))
    · intro p hp
      exact eventually_future_mem_straightened_closedCylinder hD hg.continuous hp
    · intro p hp
      exact (((hr p hp).1.sub (hf p)).const_mul s).add ((ht p).const_mul M)
    · intro p _
      exact posSemidef_of_hasEverywhereLoewnerBounds hlam.le hB _ _ _
    · intro p hp
      rw [viscousTransportedOperator_add (((hr p hp).1.sub (hf p)).const_mul s)
          ((ht p).const_mul M),
        viscousTransportedOperator_const_mul s ((hr p hp).1.sub (hf p)),
        viscousTransportedOperator_sub (hr p hp).1 (hf p), (hr p hp).2,
        viscousTransportedOperator_const_mul M (ht p), viscousTransportedOperator_time_sub]
      have hb := abs_le.mp (hM p)
      rcases hs with rfl | rfl <;> linarith
    · intro p hp hn
      by_cases hτ : p.time = τ
      · have hz := hu.2.2.2.1 (straightenedPoint g p).2 hp.2
        have he : v p = f p := by
          simpa only [v, f, straightenedPullback, straightenedPoint, hτ,
            spatialY_spatialPack, spatialZ_spatialPack, add_sub_cancel] using hz
        rw [he, sub_self, mul_zero, hτ, sub_self, mul_zero, zero_add]
      · have hx : (straightenedPoint g p).2 ∉ D := fun hx =>
          hn ⟨⟨hp.1.1, lt_of_le_of_ne hp.1.2 hτ⟩, hx⟩
        have hfr : (straightenedPoint g p).2 ∈ frontier D := by
          rw [hD.frontier_eq]
          exact ⟨hp.2, hx⟩
        have hlat : straightenedPoint g p ∈ scalarParabolicLateralFace α τ D := ⟨hp.1, hfr⟩
        have hf0 := hFl p hlat
        have hv0 := hu.2.2.2.2 (straightenedPoint g p)
          ⟨⟨haα.le.trans hp.1.1, hp.1.2⟩, hfr⟩
        change v p = 0 at hv0
        change f p = 0 at hf0
        rw [hv0, hf0, sub_self, mul_zero, zero_add]
        exact mul_nonpos_of_nonneg_of_nonpos hM0 (sub_nonpos.mpr hp.1.2)
  intro p hp
  have h1 := side 1 (Or.inl rfl) p hp
  have h2 := side (-1) (Or.inr rfl) p hp
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end HypoellipticAleksandrov.KineticAleksandrov

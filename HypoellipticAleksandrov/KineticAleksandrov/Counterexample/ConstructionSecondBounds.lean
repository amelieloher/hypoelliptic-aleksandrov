module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionLocalBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoffSecondBounds

/-! # Local integrability of the literal second cutoff representatives -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory Set

/-- A continuous scalar field has a nonnegative compact bound. -/
theorem construction_continuous_compact_bound {n : ℕ} (f : PDE.Vec n → ℝ)
    (hf : Continuous f) (K : Set (PDE.Vec n)) (hK : IsCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ K, |f x| ≤ M := by
  obtain ⟨M, hb⟩ := hK.bddAbove_image hf.abs.continuousOn
  exact ⟨max M 0, le_max_right _ _, fun x hx =>
    (hb ⟨x, hx, rfl⟩).trans (le_max_left _ _)⟩

/-- Subtraction of a smooth barrier preserves the compact bounds of the first jets. -/
theorem construction_gradient_difference_compact_bound {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r)
    (mu R t : ℝ) (i : Fin (d + d)) (K : Set (PDE.Vec (d + d))) (hK : IsCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ K,
      |spatialPackedGradient (flatProfilePositionJet h r) (flatProfileVelocityJet h r) x i -
        PDE.classicalGradient (spatialPackedBarrier d mu R t) x i| ≤ M := by
  have hc : Continuous (fun x => PDE.classicalGradient
      (spatialPackedBarrier d mu R t) x i) :=
    ((contDiff_spatialPackedBarrier d mu R t).continuous_fderiv (by simp)).clm_apply
      continuous_const
  obtain ⟨M, hM, hbM⟩ := construction_packedGradient_compact_bound h r hr i K hK
  obtain ⟨N, hN, hbN⟩ := construction_continuous_compact_bound _ hc K hK
  exact ⟨M + N, add_nonneg hM hN, fun x hx =>
    (abs_sub _ _).trans (add_le_add (hbM x hx) (hbN x hx))⟩

/-- The packed Hessian representatives of the flattening are locally integrable. -/
theorem construction_packedHessian_locallyIntegrable {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r) (i k : Fin d) :
    LocallyIntegrable (fun x => flatProfileHessian h r (spatialCoordinateCLE d x) i k)
      volume := by
  obtain ⟨_, _, hm⟩ := measurable_flatProfile_jets h r
  apply construction_locallyIntegrable_of_compact_bound _
    ((hm i k).comp (spatialCoordinateCLE d).continuous.measurable)
  intro K hK
  obtain ⟨M, hM, hb⟩ := flatProfile_jets_compact_bound_of_profile h r hr
    ((spatialCoordinateCLE d) '' K) (hK.image (spatialCoordinateCLE d).continuous)
  exact ⟨M, hM, fun x hx => (hb _ ⟨x, hx, rfl⟩).2.2 i k⟩

/-- The explicit second weak cutoff representative is locally integrable. -/
theorem construction_cutoffHessian_locallyIntegrable {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r)
    (mu R t : ℝ) (i k : Fin d) :
    LocallyIntegrable (fun x => spatialPackedCutoffVelocityHessian h r mu R t x i k)
      volume := by
  let B := spatialPackedBarrier d mu R t
  let s := fun x => selectedFlatProfile h r (spatialCoordinateCLE d x) - B x
  let g := fun j x => flatProfileVelocityJet h r (spatialCoordinateCLE d x) j -
    PDE.classicalGradient B x (Fin.natAdd d j)
  have hs : Continuous s :=
    ((continuous_selectedFlatProfile h r).comp (spatialCoordinateCLE d).continuous).sub
      (contDiff_spatialPackedBarrier d mu R t).continuous
  have hBG (j : Fin d) : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => PDE.classicalGradient B x (Fin.natAdd d j)) :=
    ((contDiff_spatialPackedBarrier d mu R t).contDiff_fderiv_apply (by simp)).comp
      (contDiff_id.prodMk contDiff_const)
  have hg (j : Fin d) : Measurable (g j) := by
    have he := (construction_packedGradient_measurable h r (Fin.natAdd d j)).sub
      (hBG j).continuous.measurable
    simpa only [g, spatialPackedGradient, Fin.addCases_right, B] using! he
  have hgb (j : Fin d) (K : Set (PDE.Vec (d + d))) (hK : IsCompact K) :
      ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ K, |g j x| ≤ M := by
    simpa only [g, spatialPackedGradient, Fin.addCases_right, B] using!
      construction_gradient_difference_compact_bound h r hr mu R t (Fin.natAdd d j) K hK
  have hprod := construction_locallyIntegrable_product (g i) (g k) (hg i) (hg k)
    (hgb i) (hgb k)
  have hH : Continuous (fun x => PDE.classicalGradient
      (fun y => PDE.classicalGradient B y (Fin.natAdd d k)) x (Fin.natAdd d i)) :=
    ((hBG k).continuous_fderiv (by simp)).clm_apply continuous_const
  have ht1 : Continuous (fun x => deriv timeCutoffTheta (s x)) :=
    (contDiff_timeCutoffTheta.continuous_deriv (by simp)).comp hs
  have ht2 : Continuous (fun x => deriv (deriv timeCutoffTheta) (s x)) := by
    have hc : Continuous (deriv (deriv timeCutoffTheta)) := by
      simpa only [funext deriv2_timeCutoffTheta] using!
        continuous_const.mul ((contDiff_flatteningSlope.continuous_deriv (by simp)).comp
          ((continuous_const.mul continuous_id).add continuous_const))
    exact hc.comp hs
  have hfirst := ((construction_packedHessian_locallyIntegrable h r hr i k).sub
    hH.locallyIntegrable).continuous_mul ht1
  have hsecond := hprod.continuous_mul ht2
  simpa only [spatialPackedCutoffVelocityHessian, B, s, g, mul_assoc] using!
    hfirst.add hsecond

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

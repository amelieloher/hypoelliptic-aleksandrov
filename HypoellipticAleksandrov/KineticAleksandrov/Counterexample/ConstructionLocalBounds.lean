module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoffGlobalJets
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.FlatteningBounds
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Compact bounds and local integrability in the packed chart -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open MeasureTheory Set

/-- Compact bounds suffice for local integrability on the packed Euclidean carrier. -/
theorem construction_locallyIntegrable_of_compact_bound {n : ℕ}
    (f : PDE.Vec n → ℝ) (hf : Measurable f)
    (hb : ∀ K : Set (PDE.Vec n), IsCompact K →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ K, |f x| ≤ M) : LocallyIntegrable f volume := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  obtain ⟨M, hM, hbM⟩ := hb K hK
  have hi : IntegrableOn (fun _ : PDE.Vec n => M) K volume :=
    integrableOn_const hK.measure_ne_top
  change Integrable (fun _ : PDE.Vec n => M) (volume.restrict K) at hi
  change Integrable f (volume.restrict K)
  apply hi.mono hf.aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg hM] using hbM x hx

/-- Products of two compactly bounded measurable representatives remain locally integrable. -/
theorem construction_locallyIntegrable_product {n : ℕ} (f g : PDE.Vec n → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hfb : ∀ K : Set (PDE.Vec n), IsCompact K →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ K, |f x| ≤ M)
    (hgb : ∀ K : Set (PDE.Vec n), IsCompact K →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ K, |g x| ≤ M) :
    LocallyIntegrable (fun x => f x * g x) volume := by
  apply construction_locallyIntegrable_of_compact_bound _ (hf.mul hg)
  intro K hK
  obtain ⟨M, hM, hbM⟩ := hfb K hK
  obtain ⟨N, hN, hbN⟩ := hgb K hK
  exact ⟨M * N, mul_nonneg hM hN, fun x hx => by
    change |f x * g x| ≤ M * N
    rw [abs_mul]
    exact mul_le_mul (hbM x hx) (hbN x hx) (abs_nonneg _) hM⟩

/-- All first flattened components have compact bounds after chart pullback. -/
theorem construction_packedGradient_compact_bound {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r)
    (i : Fin (d + d)) (K : Set (PDE.Vec (d + d))) (hK : IsCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ K,
      |spatialPackedGradient (flatProfilePositionJet h r)
        (flatProfileVelocityJet h r) x i| ≤ M := by
  obtain ⟨M, hM, hb⟩ := flatProfile_jets_compact_bound_of_profile h r hr
    ((spatialCoordinateCLE d) '' K) (hK.image (spatialCoordinateCLE d).continuous)
  refine ⟨M, hM, ?_⟩
  intro x hx
  have hb' := hb _ ⟨x, hx, rfl⟩
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [spatialPackedGradient, Fin.addCases_left, Real.norm_eq_abs] using
      (norm_le_pi_norm _ j).trans hb'.1
  · simpa only [spatialPackedGradient, Fin.addCases_right, Real.norm_eq_abs] using
      (norm_le_pi_norm _ j).trans hb'.2.1

/-- The packed first flattened representatives are measurable. -/
theorem construction_packedGradient_measurable {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (i : Fin (d + d)) :
    Measurable (fun x => spatialPackedGradient (flatProfilePositionJet h r)
      (flatProfileVelocityJet h r) x i) := by
  obtain ⟨hx, hv, _⟩ := measurable_flatProfile_jets h r
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [spatialPackedGradient, Fin.addCases_left, Function.comp_def] using!
      ((measurable_pi_apply j).comp hx).comp
      (spatialCoordinateCLE d).continuous.measurable
  · simpa only [spatialPackedGradient, Fin.addCases_right, Function.comp_def] using!
      ((measurable_pi_apply j).comp hv).comp
      (spatialCoordinateCLE d).continuous.measurable

/-- The packed first flattened representatives are locally integrable. -/
theorem construction_packedGradient_locallyIntegrable {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r)
    (i : Fin (d + d)) :
    LocallyIntegrable (fun x => spatialPackedGradient (flatProfilePositionJet h r)
      (flatProfileVelocityJet h r) x i) volume :=
  construction_locallyIntegrable_of_compact_bound _ (construction_packedGradient_measurable h r i)
    (construction_packedGradient_compact_bound h r hr i)

/-- The literal raw cutoff is continuous, hence locally integrable. -/
theorem construction_cutoffValue_continuous {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R t : ℝ) :
    Continuous (spatialPackedCutoffValue h r mu R t) :=
  contDiff_timeCutoffTheta.continuous.comp
    (((continuous_selectedFlatProfile h r).comp (spatialCoordinateCLE d).continuous).sub
      (contDiff_spatialPackedBarrier d mu R t).continuous)

/-- The literal raw first cutoff representative is locally integrable. -/
theorem construction_cutoffGradient_locallyIntegrable {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r)
    (mu R t : ℝ) (i : Fin (d + d)) :
    LocallyIntegrable (fun x => spatialPackedCutoffGradient h r mu R t x i) volume := by
  have hB : Continuous (fun x => PDE.classicalGradient
      (spatialPackedBarrier d mu R t) x i) :=
    ((contDiff_spatialPackedBarrier d mu R t).continuous_fderiv (by simp)).clm_apply
      continuous_const
  have ht : Continuous (fun x => deriv timeCutoffTheta
      (selectedFlatProfile h r (spatialCoordinateCLE d x) -
        spatialPackedBarrier d mu R t x)) :=
    (contDiff_timeCutoffTheta.continuous_deriv (by simp)).comp
      (((continuous_selectedFlatProfile h r).comp (spatialCoordinateCLE d).continuous).sub
        (contDiff_spatialPackedBarrier d mu R t).continuous)
  exact ((construction_packedGradient_locallyIntegrable h r hr i).sub
    hB.locallyIntegrable).continuous_mul ht

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

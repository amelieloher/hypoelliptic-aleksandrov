module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.DomainDominationMeasure
public import Mathlib.Topology.TietzeExtension

/-! # Bounded compact extensions of continuous local boundary data -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set
open scoped BoundedContinuousFunction

/-- Compact continuous real data extend compactly without increasing a prescribed norm bound. -/
theorem spatialData_compact_extension
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : Set E) (hK : IsCompact K) (f : E → ℝ) (hf : ContinuousOn f K)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ x ∈ K, ‖f x‖ ≤ M) :
    ∃ H : E → ℝ, Continuous H ∧ HasCompactSupport H ∧
      (∀ x, ‖H x‖ ≤ M) ∧ ∀ x ∈ K, H x = f x := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : K →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨fun x => f x, hf.domRestrict⟩
  have hF : ‖F‖ ≤ M := (BoundedContinuousFunction.norm_le hM).mpr fun x => hb x x.2
  obtain ⟨G, hG, he⟩ := F.exists_norm_eq_domRestrict_eq_of_closed hK.isClosed
  obtain ⟨χ, hχ, hc, _hs, hχb, hχone⟩ :=
    exists_smooth_bump_of_isCompact_subset_isOpen hK isOpen_univ (subset_univ K)
  refine ⟨fun x => χ x * G x, hχ.continuous.mul G.continuous,
    hc.mul_right (f' := fun x => G x), fun x => ?_, fun x hx => ?_⟩
  · rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hχb x).1]
    exact (mul_le_mul_of_nonneg_right (hχb x).2 (norm_nonneg _)).trans
      (by simpa only [one_mul] using (G.norm_coe_le_norm x).trans (hG.trans_le hF))
  · change χ x * G x = f x
    rw [hχone x hx, one_mul]
    exact congrArg (fun g : K →ᵇ ℝ => g ⟨x, hx⟩) he

/-- Uniformly continuous bounded joint data vary continuously in the bounded-function norm. -/
def spatialDataCurry {V Z : Type} [PseudoMetricSpace V] [PseudoMetricSpace Z]
    (H : V × Z → ℝ) (hH : UniformContinuous H) (M : ℝ)
    (hb : ∀ p, ‖H p‖ ≤ M) (x : V) : Z →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun z => H (x, z))
    (hH.continuous.comp (continuous_const.prodMk continuous_id)) M (fun z => hb (x, z))

/-- Currying uniformly continuous bounded data is continuous for the sup norm. -/
theorem continuous_spatialDataCurry {V Z : Type} [PseudoMetricSpace V] [PseudoMetricSpace Z]
    (H : V × Z → ℝ) (hH : UniformContinuous H) (M : ℝ) (hb : ∀ p, ‖H p‖ ≤ M) :
    Continuous (spatialDataCurry H hH M hb) := by
  apply Metric.continuous_iff.mpr
  intro x ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuous_iff.mp hH (ε / 2) (by positivity)
  refine ⟨δ, hδ, fun y hy => ?_⟩
  apply lt_of_le_of_lt (BoundedContinuousFunction.dist_le (by positivity) |>.mpr ?_)
    (half_lt_self hε)
  intro z
  apply (hd ?_).le
  simpa only [Prod.dist_eq, dist_self, max_eq_left (dist_nonneg)] using hy

end HypoellipticAleksandrov.KineticAleksandrov.LocalA

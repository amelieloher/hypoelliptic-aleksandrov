module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.OriginJetsScaling
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AnnularNormalizationGeometry

/-! # Pointwise anisotropic bounds from the actual homogeneous sphere -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set

/-- Normalize a punctured point on the literal kinetic unit sphere. -/
def bellmanUnitPoint (q : ℝ × ℝ) : ℝ × ℝ :=
  bellmanPlaneDilation (bellmanGauge q)⁻¹ q

/-- The normalization has gauge one. -/
theorem bellmanUnitPoint_gauge {q : ℝ × ℝ} (hq : q ≠ (0, 0)) :
    bellmanGauge (bellmanUnitPoint q) = 1 := by
  rw [bellmanUnitPoint, bellmanGauge_dilation _ (inv_pos.mpr (bellmanGauge_pos q hq))]
  exact inv_mul_cancel₀ (bellmanGauge_pos q hq).ne'

/-- Positive radial dilation recovers the original point. -/
theorem bellmanUnitPoint_recover {q : ℝ × ℝ} (hq : q ≠ (0, 0)) :
    bellmanPlaneDilation (bellmanGauge q) (bellmanUnitPoint q) = q := by
  rw [bellmanUnitPoint, bellmanPlaneDilation_comp,
    mul_inv_cancel₀ (bellmanGauge_pos q hq).ne']
  simp only [bellmanPlaneDilation, one_pow, one_mul, Prod.mk.eta]

/-- Every continuous homogeneous scalar function is bounded by its literal gauge degree. -/
theorem bellman_homogeneous_gauge_bound (beta : ℝ) (f : (ℝ × ℝ) → ℝ)
    (hc : ContinuousOn f bellmanPuncturedSet)
    (hs : ∀ r : ℝ, 0 < r → ∀ q ∈ bellmanPuncturedSet,
      f (bellmanPlaneDilation r q) = r ^ beta * f q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ bellmanPuncturedSet, |f q| ≤ C * bellmanGauge q ^ beta := by
  have hsU : {q : ℝ × ℝ | bellmanGauge q = 1} ⊆ bellmanPuncturedSet :=
    fun q hq => BellmanSphere.ne_zero ⟨q, hq⟩
  obtain ⟨C, hC⟩ := bellmanSphere_isCompact.bddAbove_image (hc.mono hsU).abs
  refine ⟨max C 0, le_max_right _ _, fun q hq => ?_⟩
  have hz := bellmanUnitPoint_gauge hq
  have hn : bellmanUnitPoint q ∈ bellmanPuncturedSet := hsU hz
  have hb : |f (bellmanUnitPoint q)| ≤ max C 0 :=
    (hC (mem_image_of_mem _ hz)).trans (le_max_left C 0)
  have he := hs (bellmanGauge q) (bellmanGauge_pos q hq) _ hn
  rw [bellmanUnitPoint_recover hq] at he
  rw [he, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (bellmanGauge_pos q hq) beta)]
  exact (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg (bellmanGauge_nonneg q) beta)).trans_eq
    (mul_comm _ _)

/-- The actual Bellman function and all three jets have their exact source gauge bounds. -/
theorem IsBellmanHomogeneous.origin_jet_bounds {alpha : ℝ} {phi : (ℝ × ℝ) → ℝ}
    (h : IsBellmanHomogeneous alpha phi) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ bellmanPuncturedSet,
      |phi q| ≤ C * bellmanGauge q ^ alpha) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ bellmanPuncturedSet,
      |bellmanDx phi q| ≤ C * bellmanGauge q ^ (alpha - 3)) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ bellmanPuncturedSet,
      |bellmanDv phi q| ≤ C * bellmanGauge q ^ (alpha - 1)) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ bellmanPuncturedSet,
      |bellmanDvv phi q| ≤ C * bellmanGauge q ^ (alpha - 2)) := by
  refine ⟨bellman_homogeneous_gauge_bound alpha phi h.1.continuousOn h.2, ?_, ?_, ?_⟩
  · exact bellman_homogeneous_gauge_bound (alpha - 3) (bellmanDx phi) h.dx_continuousOn
      (fun _ hr _ hq => h.dx_scaling hr hq)
  · exact bellman_homogeneous_gauge_bound (alpha - 1) (bellmanDv phi)
      (h.directional_contDiffOn (0, 1)).continuousOn (fun _ hr _ hq => h.dv_scaling hr hq)
  · exact bellman_homogeneous_gauge_bound (alpha - 2) (bellmanDvv phi) h.dvv_continuousOn
      (fun _ hr _ hq => h.dvv_scaling hr hq)

end HypoellipticAleksandrov.KineticAleksandrov

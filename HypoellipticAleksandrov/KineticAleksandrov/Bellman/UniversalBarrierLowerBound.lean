module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.UniversalBarrierScaling
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AnnularNormalizationGeometry
import Mathlib.Tactic

/-! # Compact minimum of the positive Bellman image and its global homogeneous bound -/

@[expose] public section
noncomputable section
open Set
namespace HypoellipticAleksandrov.KineticAleksandrov

/-- Normalizing a punctured point by its literal gauge puts it on the source sphere. -/
def bellmanSpherePoint (q : ℝ × ℝ) (hq : q ∈ bellmanPuncturedSet) : BellmanSphere :=
  ⟨bellmanPlaneDilation (bellmanGauge q)⁻¹ q, by
    rw [bellmanGauge_dilation _ (inv_pos.mpr (bellmanGauge_pos q hq)),
      inv_mul_cancel₀ (bellmanGauge_pos q hq).ne']⟩

/-- Dilating the normalized sphere point by its gauge recovers the original point. -/
theorem bellmanSpherePoint_reconstruct (q : ℝ × ℝ) (hq : q ∈ bellmanPuncturedSet) :
    bellmanPlaneDilation (bellmanGauge q) (bellmanSpherePoint q hq).val = q := by
  rw [bellmanSpherePoint, bellmanPlaneDilation_comp,
    mul_inv_cancel₀ (bellmanGauge_pos q hq).ne']
  simp only [bellmanPlaneDilation, one_pow, one_mul, Prod.mk.eta]

/-- Positivity on the compact sphere and diffusion interval gives the global homogeneous bound. -/
theorem positive_bellman_image_lower_bound (lam Lam : ℝ) (_hlam : 0 < lam)
    (hLam : lam ≤ Lam) (alpha : ℝ) (phi : (ℝ × ℝ) → ℝ)
    (hhom : IsBellmanHomogeneous alpha phi)
    (hpos : ∀ z : BellmanSphere, ∀ b : BellmanCoefficient lam Lam,
      0 < bellmanOperator b.val phi z.val) :
    ∃ c : ℝ, 0 < c ∧ ∀ q ∈ bellmanPuncturedSet, ∀ b ∈ Icc lam Lam,
      c * bellmanGauge q ^ (alpha - 2) ≤ bellmanOperator b phi q := by
  let : Nonempty (BellmanCoefficient lam Lam) := bellmanCoefficient_nonempty lam Lam hLam
  have hc := hhom.image_continuous (lam := lam) (Lam := Lam)
  obtain ⟨w0, _, hmin⟩ := (isCompact_univ : IsCompact
    (univ : Set (BellmanSphere × BellmanCoefficient lam Lam))).exists_isMinOn
      univ_nonempty hc.continuousOn
  refine ⟨bellmanOperator w0.2.val phi w0.1.val, hpos w0.1 w0.2, ?_⟩
  intro q hq b hb
  let z := bellmanSpherePoint q hq
  have hminq := hmin (show (z, (⟨b, hb⟩ : BellmanCoefficient lam Lam)) ∈ univ from trivial)
  have hs := bellman_homogeneous_operator_scaling hhom (bellmanGauge q)
    (bellmanGauge_pos q hq) z.val z.ne_zero b
  rw [bellmanSpherePoint_reconstruct q hq] at hs
  rw [hs, mul_comm]
  exact mul_le_mul_of_nonneg_left hminq (Real.rpow_nonneg (bellmanGauge_nonneg q) _)

end HypoellipticAleksandrov.KineticAleksandrov

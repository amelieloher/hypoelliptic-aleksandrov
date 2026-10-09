module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationMeasure
import Mathlib.Tactic

/-! # Undoing the degree weight gives the literal source radial representation -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- Undoing the degree weight on ds/s gives exactly s^(3-β) ds. -/
theorem bellmanRadialHaar_reweight (β : ℝ) :
    bellmanRadialHaar.withDensity
      (fun s : BellmanPositiveTime => ENNReal.ofReal (s.val ^ (4 - β))) =
      bellmanRadialWeight β := by
  have h1 : Measurable (fun s : BellmanPositiveTime => ENNReal.ofReal s.val⁻¹) := by
    fun_prop
  have h2 : Measurable (fun s : BellmanPositiveTime =>
      ENNReal.ofReal (s.val ^ (4 - β))) := by fun_prop
  rw [bellmanRadialHaar, ← withDensity_mul _ h1 h2]
  unfold bellmanRadialWeight
  congr 1
  funext s
  change ENNReal.ofReal s.val⁻¹ * ENNReal.ofReal (s.val ^ (4 - β)) = _
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr s.property.le),
    ← Real.rpow_neg_one, ← Real.rpow_add s.property]
  congr 1
  congr 1
  ring

/-- The inverse degree-removing weight is the reciprocal real-power weight. -/
theorem bellmanRadialDegreeWeight_inv (β : ℝ) (w : BellmanPositiveTime × ℝ) :
    (bellmanRadialDegreeWeight β w)⁻¹ = ENNReal.ofReal (w.1.val ^ (4 - β)) := by
  rw [bellmanRadialDegreeWeight,
    ← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos w.1.property _),
    ← Real.rpow_neg w.1.property.le]
  congr 1
  congr 1
  ring

/-- The actual homogeneous coordinate measure is s^(3-β) ds times its actual angular measure. -/
theorem bellmanAngularPullback_factorization (β : ℝ)
    (μ : Measure BellmanPuncturedPlane) (hμ : IsFiniteMeasureOnCompacts μ)
    (hd : HasBellmanDensityDegree β μ) :
    bellmanAngularPullback μ =
      (bellmanRadialWeight β).prod (bellmanAngularMeasure β μ) := by
  let : IsFiniteMeasureOnCompacts (bellmanAngularMeasure β μ) :=
    bellmanAngularMeasure_finiteOnCompacts β μ hμ
  have hn : ∀ᵐ w ∂bellmanAngularPullback μ, bellmanRadialDegreeWeight β w ≠ 0 :=
    ae_of_all _ fun w => (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos w.1.property _)).ne'
  have ht : ∀ᵐ w ∂bellmanAngularPullback μ, bellmanRadialDegreeWeight β w ≠ ⊤ :=
    ae_of_all _ fun _ => ENNReal.ofReal_ne_top
  have he := congrArg (fun ρ : Measure (BellmanPositiveTime × ℝ) =>
    ρ.withDensity (fun w => (bellmanRadialDegreeWeight β w)⁻¹))
      (bellmanAngularPullback_reweighted_factorization β μ hμ hd)
  rw [withDensity_inv_same (measurable_bellmanRadialDegreeWeight β) hn ht] at he
  have hw : (fun w => (bellmanRadialDegreeWeight β w)⁻¹) =
      (fun w : BellmanPositiveTime × ℝ => ENNReal.ofReal (w.1.val ^ (4 - β))) :=
    funext (bellmanRadialDegreeWeight_inv β)
  rw [hw] at he
  have hm : Measurable (fun s : BellmanPositiveTime =>
      ENNReal.ofReal (s.val ^ (4 - β))) := by fun_prop
  rw [← prod_withDensity_left (μ := bellmanRadialHaar)
    (ν := bellmanAngularMeasure β μ) hm, bellmanRadialHaar_reweight] at he
  exact he

/-- Mapping the proved product representation yields the exact positive-position restriction. -/
theorem bellmanAngularMeasure_representation (β : ℝ)
    (μ : Measure BellmanPuncturedPlane) (hμ : IsFiniteMeasureOnCompacts μ)
    (hd : HasBellmanDensityDegree β μ) :
    μ.restrict {q | 0 < q.val.1} = bellmanAngularRep β (bellmanAngularMeasure β μ) := by
  rw [← map_bellmanAngularPullback μ, bellmanAngularPullback_factorization β μ hμ hd]
  rfl

end HypoellipticAleksandrov.KineticAleksandrov

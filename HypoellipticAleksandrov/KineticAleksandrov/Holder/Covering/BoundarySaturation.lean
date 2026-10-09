module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.BoundarySaturationDensity
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.BoundarySaturationContinuity
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-! # Critical cylinders before the prescribed radius cutoff -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

open Set MeasureTheory
open scoped Topology

/-- Intersection volume minus the near-full threshold along the admissible path. -/
def saturationGap {d : ℕ} (E : Set (KineticPoint d)) (eta : ℝ)
    (X : KineticPoint d) (r : ℝ) : ℝ :=
  (volume (E ∩ backwardCylinder (saturationCenter X r) r)).toReal-
    (1-eta)*(volume (backwardCylinder (saturationCenter X r) r)).toReal

/-- The threshold gap is continuous at every positive radius. -/
theorem continuousAt_saturationGap {d : ℕ} {E : Set (KineticPoint d)}
    (hE : volume E ≠ ⊤) (eta : ℝ) (X : KineticPoint d) {r : ℝ} (hr : 0 < r) :
    ContinuousAt (saturationGap E eta X) r := by
  have hV : ContinuousAt
      (fun s : ℝ => (volume (backwardCylinder (saturationCenter X s) s)).toReal) r := by
    have heq : (fun s : ℝ => (volume (backwardCylinder (saturationCenter X s) s)).toReal)
        =ᶠ[𝓝 r] (fun s => s^(4*d+2)*(volume (unitCylinder d)).toReal) := by
      filter_upwards [eventually_gt_nhds hr] with s hs
      rw [volume_cylinder_eq_unit _ hs, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by positivity)]
      rfl
    apply ContinuousAt.congr_of_eventuallyEq ?_ heq
    fun_prop
  exact (continuousAt_cylinder_inter_volume (saturationCenter X)
    (continuous_saturationCenter X) hE hr).sub (continuousAt_const.mul hV)

/-- Almost every point away from the spatial shell has an admissible critical cylinder. -/
theorem ae_exists_critical_cylinder {d : ℕ} {E : Set (KineticPoint d)}
    (hE : NullMeasurableSet E volume) (hbounded : Bornology.IsBounded E)
    (hEQ : E ⊆ unitCylinder d) {eta R : ℝ} (heta : 0 < eta)
    (hR : 0 < R) (hR1 : R ≤ 1)
    (hcutoff : ∀ P r, 0 < r → backwardCylinder P r ⊆ unitCylinder d →
      (1-eta)*(volume (backwardCylinder P r)).toReal ≤
        (volume (E ∩ backwardCylinder P r)).toReal → r < R) :
    ∀ᵐ X ∂(volume.restrict E), PDE.vecEuclideanNorm X.position < 1-2*R^2 →
      ∃ P r, 0 < r ∧ r < R ∧ X ∈ backwardCylinder P r ∧
        backwardCylinder P r ⊆ unitCylinder d ∧
        (volume (E ∩ backwardCylinder P r)).toReal =
          (1-eta)*(volume (backwardCylinder P r)).toReal := by
  filter_upwards [ae_saturationCylinder_density hE hbounded hEQ, ae_restrict_mem₀ hE]
    with X hd hXE
  intro hx
  obtain ⟨s, hs, hsmall⟩ := hd (eta/2) (half_pos heta)
  let a := min s R/2
  have ha : 0 < a := half_pos (lt_min hs hR)
  have has : a < s := (half_lt_self (lt_min hs hR)).trans_le (min_le_left _ _)
  have haR : a < R := (half_lt_self (lt_min hs hR)).trans_le (min_le_right _ _)
  have hpos : 0 < saturationGap E eta X a := by
    have hdense := hsmall a ha has
    have hvol := ENNReal.toReal_pos
      (volume_cylinder_pos_ne_top (saturationCenter X a) ha).1.ne'
      (volume_cylinder_pos_ne_top (saturationCenter X a) ha).2
    dsimp [saturationGap]
    nlinarith
  have hneg : saturationGap E eta X R < 0 := by
    by_contra hn
    have hdense : (1-eta)*(volume (backwardCylinder (saturationCenter X R) R)).toReal ≤
        (volume (E ∩ backwardCylinder (saturationCenter X R) R)).toReal := by
      change ¬ _ < 0 at hn
      dsimp [saturationGap] at hn
      linarith
    have h := hcutoff (saturationCenter X R) R hR
      (saturationCylinder_subset_unit (hEQ hXE) hR le_rfl hR1 hx) hdense
    exact (lt_irrefl R) h
  have hc : ContinuousOn (saturationGap E eta X) (Icc a R) := by
    intro r hr
    exact (continuousAt_saturationGap (volume_bounded_ne_top hbounded) eta X
      (ha.trans_le hr.1)).continuousWithinAt
  obtain ⟨r, hr, heq⟩ := intermediate_value_Icc' haR.le hc ⟨hneg.le, hpos.le⟩
  have hrpos : 0 < r := ha.trans_le hr.1
  have hrR : r < R := lt_of_le_of_ne hr.2 (by
    intro he
    rw [he] at heq
    linarith)
  refine ⟨saturationCenter X r, r, hrpos, hrR,
    self_mem_saturationCylinder (hEQ hXE) hrpos,
    saturationCylinder_subset_unit (hEQ hXE) hrpos hrR.le hR1 hx, ?_⟩
  dsimp [saturationGap] at heq
  linarith

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.Capacity
import Mathlib.Tactic

/-! # No velocity atoms in the actual killed Green measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- Capacity implies that every exact velocity slice has zero occupation mass. -/
theorem stripGreen_velocity_slice_zero
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (T : ℝ)
    (e : StripPole H (T : WithTop ℝ)) (v : ℝ) :
    stripGreen hH hLE hlam hLam A H T e {p | p.velocity 0 = v} = 0 := by
  let Γ := stripGreen hH hLE hlam hLam A H T e
  have hfin : IsFiniteMeasure Γ := by dsimp only [Γ, stripGreen]; infer_instance
  let S : Set Point := {p | p.velocity 0 = v}
  let C : ℝ := (H.hi - H.lo) / lam
  have hC : 0 < C := div_pos (sub_pos.mpr H.ordered) hlam
  by_contra hz
  have hm : 0 < (Γ S).toReal :=
    ENNReal.toReal_pos (by simpa only [Γ, S, ne_eq] using hz) (measure_ne_top Γ S)
  let d := (Γ S).toReal / (4 * C)
  have hd : 0 < d := div_pos hm (by positivity)
  let E : Interval := ⟨v - d, v + d, by linarith⟩
  have hsub : S ⊆ {p | p.velocity 0 ∈ E.carrier} := by
    intro p hp
    change p.velocity 0 = v at hp
    change v - d < p.velocity 0 ∧ p.velocity 0 < v + d
    rw [hp]
    constructor <;> linarith
  have hcap := (measure_mono hsub).trans (strip_capacity hH hLE hlam hLam A H T e E)
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcap
  rw [ENNReal.toReal_ofReal (by
    change 0 ≤ C * ((v + d) - (v - d))
    exact mul_nonneg hC.le (by linarith))] at hr
  change (Γ S).toReal ≤ C * ((v + d) - (v - d)) at hr
  have he : C * ((v + d) - (v - d)) = (Γ S).toReal / 2 := by
    dsimp only [d]
    field_simp
    ring
  rw [he] at hr
  linarith

/-- The source's velocity capacity and absence of atoms, for every valid finite-strip pole. -/
theorem velocity_capacity_and_no_atoms
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (T : ℝ)
    (e : StripPole H (T : WithTop ℝ)) :
    (∀ E : Interval,
      stripGreen hH hLE hlam hLam A H T e {p | p.velocity 0 ∈ E.carrier} ≤
        ENNReal.ofReal ((H.hi - H.lo) / lam * (E.hi - E.lo))) ∧
    (∀ v : ℝ, stripGreen hH hLE hlam hLam A H T e {p | p.velocity 0 = v} = 0) :=
  ⟨strip_capacity hH hLE hlam hLam A H T e,
    stripGreen_velocity_slice_zero hH hLE hlam hLam A H T e⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

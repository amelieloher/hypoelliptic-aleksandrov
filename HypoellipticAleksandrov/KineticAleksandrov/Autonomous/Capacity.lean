module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CapacityIntegral
import Mathlib.Tactic

/-! # Velocity capacity of the actual finite-strip Green measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/-- Velocity occupation is bounded by strip width times interval length over ellipticity. -/
theorem strip_capacity
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (T : ℝ)
    (e : StripPole H (T : WithTop ℝ)) (E : Interval) :
    stripGreen hH hLE hlam hLam A H T e {p | p.velocity 0 ∈ E.carrier} ≤
      ENNReal.ofReal ((H.hi - H.lo) / lam * (E.hi - E.lo)) := by
  obtain ⟨chi, Phi, hchi, _hc, hn, h1, _hm, hPhi, hsecond, hd⟩ :=
    exists_capacity_test E
  let Γ := stripGreen hH hLE hlam hLam A H T e
  let U : Set Point := {p | p.velocity 0 ∈ E.carrier}
  have hU : MeasurableSet U :=
    isOpen_Ioo.measurableSet.preimage ((continuous_apply 0).comp continuous_velocity).measurable
  have hfin : IsFiniteMeasure Γ := by dsimp only [Γ, stripGreen]; infer_instance
  let g : Point → ℝ := fun p => 2 * A.a (p.position 0) (p.velocity 0) * chi (p.velocity 0)
  have hgc : Continuous g := by
    exact (continuous_const.mul (A.smooth.continuous.comp
      (((continuous_apply 0).comp continuous_position).prodMk
        ((continuous_apply 0).comp continuous_velocity)))).mul
      (hchi.continuous.comp ((continuous_apply 0).comp continuous_velocity))
  have hgn (p : Point) : 0 ≤ g p :=
    mul_nonneg (mul_nonneg (by norm_num)
      (hlam.trans_le (A.bounds _ _).1).le) (hn _).1
  have hgb (p : Point) : |g p| ≤ 2 * Lam := by
    rw [abs_of_nonneg (hgn p)]
    dsimp only [g]
    nlinarith [(A.bounds (p.position 0) (p.velocity 0)).1,
      (A.bounds (p.position 0) (p.velocity 0)).2, (hn (p.velocity 0)).1,
      (hn (p.velocity 0)).2]
  have hi : Integrable g Γ := by
    apply Integrable.mono' (integrable_const (2 * Lam)) hgc.measurable.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs] using hgb p
  have hind : Integrable (U.indicator (fun _p => (2 * lam))) Γ :=
    (integrable_const _).indicator hU
  have hlow : 2 * lam * (Γ U).toReal ≤ ∫ p, g p ∂Γ := by
    calc
      _ = ∫ p, U.indicator (fun _p => (2 * lam)) p ∂Γ := by
        rw [integral_indicator_const _ hU, Measure.real, smul_eq_mul]
        ring
      _ ≤ _ := integral_mono hind hi (fun p => by
        by_cases hp : p ∈ U
        · dsimp only [g]
          rw [indicator_of_mem hp, show chi (p.velocity 0) = 1 from
            h1 _ ⟨hp.1.le, hp.2.le⟩]
          nlinarith [(A.bounds (p.position 0) (p.velocity 0)).1]
        · rw [indicator_of_notMem hp]
          exact hgn p)
  have hD : 0 ≤ 2 * (E.hi - E.lo) := by linarith [E.ordered]
  have hupper := capacity_diffusion_integral_le hH hLE hlam hLam A H T e Phi chi
    hPhi hchi hn hsecond hD hd
  have hr : (Γ U).toReal ≤ (H.hi - H.lo) / lam * (E.hi - E.lo) := by
    have heq : ((H.hi - H.lo) / lam * (E.hi - E.lo)) * lam =
        (H.hi - H.lo) * (E.hi - E.lo) := by field_simp
    have hmul : (Γ U).toReal * lam ≤
        ((H.hi - H.lo) / lam * (E.hi - E.lo)) * lam := by
      rw [heq]
      change (∫ p, g p ∂Γ) ≤ _ at hupper
      nlinarith
    nlinarith
  have hnon : 0 ≤ (H.hi - H.lo) / lam * (E.hi - E.lo) :=
    mul_nonneg (div_nonneg (sub_pos.mpr H.ordered).le hlam.le)
      (sub_pos.mpr E.ordered).le
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top Γ U) hnon).mpr hr

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.Setting
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.DomainDominationMeasure
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! # Compact smooth majorants of velocity intervals -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory

/-- A compact smooth majorant with integral at most twice the interval length. -/
theorem exists_capacity_cutoff (E : Interval) :
    ∃ chi : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) chi ∧ HasCompactSupport chi ∧
      tsupport chi ⊆ Ioo (E.lo - (E.hi - E.lo) / 2) (E.hi + (E.hi - E.lo) / 2) ∧
      (∀ v, 0 ≤ chi v ∧ chi v ≤ 1) ∧ (∀ v ∈ Icc E.lo E.hi, chi v = 1) ∧
      (∫ v, chi v) ≤ 2 * (E.hi - E.lo) := by
  let a := E.lo - (E.hi - E.lo) / 2
  let b := E.hi + (E.hi - E.lo) / 2
  have hsub : Icc E.lo E.hi ⊆ Ioo a b := by
    intro v hv
    dsimp only [a, b]
    constructor <;> linarith [E.ordered, hv.1, hv.2]
  obtain ⟨chi, hs, hc, hsup, h01, h1⟩ :=
    exists_smooth_bump_of_isCompact_subset_isOpen (isCompact_Icc : IsCompact (Icc E.lo E.hi))
      isOpen_Ioo hsub
  refine ⟨chi, hs, hc, hsup, h01, h1, ?_⟩
  have hi : Integrable chi volume := hs.continuous.integrable_of_hasCompactSupport hc
  have he : (∫ v, chi v) = ∫ v in Ioo a b, chi v := by
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun v hv => image_eq_zero_of_notMem_tsupport (fun ht => hv (hsup ht)))).symm
  rw [he]
  have hm := integral_mono (hi.restrict (s := Ioo a b)) (integrable_const (1 : ℝ))
    (fun v => (h01 v).2)
  have hab : 0 ≤ b - a := by dsimp only [a, b]; linarith [E.ordered]
  have hv : (∫ _v in Ioo a b, (1 : ℝ)) = b - a := by
    simp only [integral_const, smul_eq_mul, mul_one, Measure.real,
      Measure.restrict_apply_univ, Real.volume_Ioo,
      ENNReal.toReal_ofReal hab]
  rw [hv] at hm
  exact hm.trans_eq (by dsimp only [a, b]; ring)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

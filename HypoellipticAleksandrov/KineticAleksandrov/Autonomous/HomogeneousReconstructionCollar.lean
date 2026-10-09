module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionProfile
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.HomogeneousReconstructionComparison
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Exponential collar barriers

The barrier has height at most `2 delta^2 / lambda` and absorbs the two
exponential weights at the velocity faces. No coefficient derivatives occur.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic Evolution Set

/-- Positive exponential weights at the two velocity faces. -/
def reconstructionCollarWeight (H : Interval) (δ v : ℝ) : ℝ :=
  Real.exp ((H.lo - v) / δ) + Real.exp ((v - H.hi) / δ)

/-- Scalar diffused profile of the collar supersolution. -/
def reconstructionCollarProfile (H : Interval) (lam δ v : ℝ) : ℝ :=
  δ ^ 2 / lam * (2 - reconstructionCollarWeight H δ v)

/-- Both exponential weights are strictly positive. -/
theorem reconstructionCollarWeight_nonneg (H : Interval) (δ v : ℝ) :
    0 ≤ reconstructionCollarWeight H δ v :=
  add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le

/-- Inside the closed interval each exponential weight is at most one. -/
theorem reconstructionCollarWeight_le_two (H : Interval) {δ v : ℝ}
    (hδ : 0 < δ) (hv : H.lo ≤ v ∧ v ≤ H.hi) :
    reconstructionCollarWeight H δ v ≤ 2 := by
  have hl : Real.exp ((H.lo - v) / δ) ≤ 1 := Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hv.1) hδ.le)
  have hh : Real.exp ((v - H.hi) / δ) ≤ 1 := Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hv.2) hδ.le)
  exact (add_le_add hl hh).trans_eq (by norm_num)

/-- The collar profile is nonnegative and uniformly small on the closed interval. -/
theorem reconstructionCollarProfile_bounds (H : Interval) {lam δ v : ℝ}
    (hlam : 0 < lam) (hδ : 0 < δ) (hv : H.lo ≤ v ∧ v ≤ H.hi) :
    0 ≤ reconstructionCollarProfile H lam δ v ∧
      reconstructionCollarProfile H lam δ v ≤ 2 * δ ^ 2 / lam := by
  have hc : 0 ≤ δ ^ 2 / lam := div_nonneg (sq_nonneg δ) hlam.le
  refine ⟨mul_nonneg hc (sub_nonneg.mpr (reconstructionCollarWeight_le_two H hδ hv)), ?_⟩
  have h := mul_le_mul_of_nonneg_left
    (sub_le_self (2 : ℝ) (reconstructionCollarWeight_nonneg H δ v)) hc
  exact h.trans_eq (by ring)

/-- The two exponential collar weights are globally smooth. -/
theorem reconstructionCollarWeight_smooth (H : Interval) (δ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (reconstructionCollarWeight H δ) :=
  ((contDiff_const.sub contDiff_id).div_const δ).exp.add
    ((contDiff_id.sub contDiff_const).div_const δ).exp

/-- The collar profile is smooth on the whole scalar line. -/
theorem reconstructionCollarProfile_smooth (H : Interval) (lam δ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (reconstructionCollarProfile H lam δ) :=
  contDiff_const.mul (contDiff_const.sub
    (((contDiff_const.sub contDiff_id).div_const δ).exp.add
      ((contDiff_id.sub contDiff_const).div_const δ).exp))

private theorem collar_left_deriv (H : Interval) (δ v : ℝ) :
    HasDerivAt (fun w => Real.exp ((H.lo - w) / δ))
      (Real.exp ((H.lo - v) / δ) * (-1 / δ)) v := by
  simpa only [zero_sub, Pi.sub_apply, id_eq] using!
    (((hasDerivAt_const v H.lo).sub (hasDerivAt_id v)).div_const δ).exp

private theorem collar_right_deriv (H : Interval) (δ v : ℝ) :
    HasDerivAt (fun w => Real.exp ((w - H.hi) / δ))
      (Real.exp ((v - H.hi) / δ) * (1 / δ)) v := by
  simpa only [sub_zero, Pi.sub_apply, id_eq] using!
    (((hasDerivAt_id v).sub (hasDerivAt_const v H.hi)).div_const δ).exp

private theorem collar_profile_deriv (H : Interval) (lam δ v : ℝ) :
    deriv (reconstructionCollarProfile H lam δ) v =
      δ ^ 2 / lam * (Real.exp ((H.lo - v) / δ) - Real.exp ((v - H.hi) / δ)) / δ := by
  have h := ((hasDerivAt_const v (2 : ℝ)).sub
    ((collar_left_deriv H δ v).add (collar_right_deriv H δ v))).const_mul (δ ^ 2 / lam)
  change HasDerivAt (reconstructionCollarProfile H lam δ) _ v at h
  rw [h.deriv]
  ring

/-- The second derivative exactly absorbs the collar weights. -/
theorem reconstructionCollarProfile_secondDeriv (H : Interval) (lam : ℝ) {δ : ℝ}
    (hδ : 0 < δ) (v : ℝ) :
    deriv (deriv (reconstructionCollarProfile H lam δ)) v =
      -reconstructionCollarWeight H δ v / lam := by
  have heq : deriv (reconstructionCollarProfile H lam δ) =
      fun w => δ ^ 2 / lam *
        (Real.exp ((H.lo - w) / δ) - Real.exp ((w - H.hi) / δ)) / δ :=
    funext (collar_profile_deriv H lam δ)
  rw [heq]
  have h := (((collar_left_deriv H δ v).sub (collar_right_deriv H δ v)).const_mul
    (δ ^ 2 / lam)).div_const δ
  simp only [Pi.sub_apply] at h
  rw [h.deriv]
  unfold reconstructionCollarWeight
  by_cases hl : lam = 0
  · simp [hl]
  · field_simp [hl, ne_of_gt hδ]
    ring

/-- The actual native collar barrier dominates its positive forcing weight. -/
theorem reconstructionCollarProfile_operator_le {lam Lam : ℝ}
    (hlam : 0 < lam) (A : SmoothAutonomous lam Lam) (H : Interval)
    {δ : ℝ} (hδ : 0 < δ) (p : Point) :
    transportedForwardOperator (evolutionCoefficient A.a) (SectionTwo.identityDrift 1)
      (reconstructionProfile (reconstructionCollarProfile H lam δ)) p ≤
        -reconstructionCollarWeight H δ (p.position 0) := by
  rw [reconstructionProfile_operator A.a
    ((reconstructionCollarProfile_smooth H lam δ).of_le (by simp)),
    reconstructionCollarProfile_secondDeriv H lam hδ]
  have hk := reconstructionCollarWeight_nonneg H δ (p.position 0)
  have ha := (A.bounds (p.velocity 0) (p.position 0)).1
  have hr : 1 ≤ A.a (p.velocity 0) (p.position 0) / lam :=
    (le_div_iff₀ hlam).mpr (by simpa only [one_mul] using ha)
  have hm := mul_le_mul_of_nonneg_right hr hk
  calc
    A.a (p.velocity 0) (p.position 0) *
        (-reconstructionCollarWeight H δ (p.position 0) / lam) =
      -(A.a (p.velocity 0) (p.position 0) / lam *
        reconstructionCollarWeight H δ (p.position 0)) := by ring
    _ ≤ -reconstructionCollarWeight H δ (p.position 0) := by
      simpa only [one_mul] using neg_le_neg hm

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

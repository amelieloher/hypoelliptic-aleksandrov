module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnHolderPatch
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnIterationCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnIterationAbsorption
import Mathlib.Tactic

/-! # Supremum iteration removes the larger return-box supremum -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic Set Holder

/-- The nested radii in the source iteration. -/
def returnIterationRadius (n : ℕ) : ℝ := 1 - (1 / 2 : ℝ) ^ (n + 1)

/-- Every radius belongs to the permitted half-to-one interval. -/
theorem returnIterationRadius_bounds (n : ℕ) :
    1 / 2 ≤ returnIterationRadius n ∧ returnIterationRadius n < 1 := by
  have hp := pow_pos (by norm_num : (0 : ℝ) < 1 / 2) (n + 1)
  have hb : (1 / 2 : ℝ) ^ (n + 1) ≤ 1 / 2 := by
    rw [pow_succ]
    have h := pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) (n := n)
    nlinarith
  dsimp [returnIterationRadius]
  constructor <;> linarith

/-- The consecutive radius gap is the exact dyadic gap in the source. -/
theorem returnIterationRadius_gap (n : ℕ) :
    returnIterationRadius (n + 1) - returnIterationRadius n =
      (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ n := by
  simp only [returnIterationRadius, pow_succ]
  ring

/-- The error term grows by the fixed factor `2^beta` at each iteration. -/
theorem returnIterationRadius_gap_power (n : ℕ) (beta : ℝ) :
    (returnIterationRadius (n + 1) - returnIterationRadius n) ^ (-beta) =
      (4 : ℝ) ^ beta * ((2 : ℝ) ^ beta) ^ n := by
  rw [returnIterationRadius_gap,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 4) (pow_nonneg (by norm_num) n),
    ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_neg_eq_inv_rpow]
  norm_num

/-- The larger supremum disappears, leaving a uniform unit-scale return comparison. -/
theorem return_time_unit_solution (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (hp6 : SmoothAutonomousP6Statement lam Lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (u : Point → ℝ),
      IsNonnegativeHomogeneousSolution A u → ∀ v : ℝ, |v| ≤ 1 →
      ∀ zStar ∈ returnFutureRegion, u (point 1 0 v) ≤ C * u zStar := by
  obtain ⟨alpha, beta, c₀, ha, _ha1, hb, hc, hheight⟩ :=
    return_holder_patch_solution lam Lam hlam hLam hp6
  let r := (2 : ℝ) ^ beta
  let eps := 1 / (2 * r)
  let K := (c₀ * eps ^ (beta / alpha))⁻¹
  let C := 2 * K * (4 : ℝ) ^ beta
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : 1 ≤ r := Real.one_le_rpow (by norm_num) hb.le
  have heps : 0 < eps := by dsimp [eps]; positivity
  have heps1 : eps < 1 := by
    apply (div_lt_one (by positivity : 0 < 2 * r)).mpr
    linarith
  have her : eps * r = 1 / 2 := by dsimp [eps]; field_simp
  have hK : 0 < K := by dsimp [K]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro A u hu v hv zStar hstar
  obtain ⟨M, hM⟩ := hu.1
  have hprops (R : ℝ) (hRlo : 1 / 2 ≤ R) (hRhi : R ≤ 1) :
      BddAbove (u '' returnBox v R) ∧ 0 ≤ sSup (u '' returnBox v R) ∧
        sSup (u '' returnBox v R) ≤ M := by
    have hpos : returnBox v R ⊆ {q | 0 < q.time} := by
      intro q hq
      have href := returnBox_subset_reference v R hv hRhi hq
      change 0 < q.time
      linarith [href.1.1]
    have hbd : BddAbove (u '' returnBox v R) := ⟨M, by
      rintro _ ⟨q, hq, rfl⟩
      exact (le_abs_self _).trans (hM q (hpos hq))⟩
    have hcenter := returnBox_center v R (by linarith)
    have hne := (show (returnBox v R).Nonempty from ⟨point 1 0 v, hcenter⟩).image u
    exact ⟨hbd, (hu.2.1 _ (by norm_num [point])).trans
      (le_csSup hbd (mem_image_of_mem u hcenter)), csSup_le hne (by
        rintro _ ⟨q, hq, rfl⟩
        exact (le_abs_self _).trans (hM q (hpos hq)))⟩
  let f : ℕ → ℝ := fun n => sSup (u '' returnBox v (returnIterationRadius n))
  have hf0 (n : ℕ) : 0 ≤ f n :=
    (hprops _ (returnIterationRadius_bounds n).1 (returnIterationRadius_bounds n).2.le).2.1
  have hfM (n : ℕ) : f n ≤ M :=
    (hprops _ (returnIterationRadius_bounds n).1 (returnIterationRadius_bounds n).2.le).2.2
  have hU : 0 ≤ u zStar := hu.2.1 zStar (by linarith [hstar.1.1])
  have hstep (n : ℕ) : f n ≤ eps * f (n + 1) +
      (K * (4 : ℝ) ^ beta * u zStar) * r ^ n := by
    have hgap : 0 < returnIterationRadius (n + 1) - returnIterationRadius n := by
      rw [returnIterationRadius_gap]
      positivity
    have hfmono : f n ≤ f (n + 1) := by
      apply csSup_le
      · exact ⟨u (point 1 0 v), mem_image_of_mem u (returnBox_center v _
          (by linarith [(returnIterationRadius_bounds n).1]))⟩
      · intro x hx
        exact le_csSup (hprops _ (returnIterationRadius_bounds (n + 1)).1
          (returnIterationRadius_bounds (n + 1)).2.le).1
          (image_mono (returnBox_mono v (by linarith)) hx)
    have hh := return_height_absorption beta (beta / alpha) c₀ eps
      (returnIterationRadius (n + 1) - returnIterationRadius n) (f n) (f (n + 1))
      (u zStar) (by positivity) hc heps hgap (hf0 n) hfmono hU
      (fun hMb => by
        simpa only [f, neg_div] using hheight A u hu _ _ v (returnIterationRadius_bounds n).1
          (by linarith) (returnIterationRadius_bounds (n + 1)).2.le hv zStar hstar hMb)
    rw [returnIterationRadius_gap_power] at hh
    convert hh using 1; dsimp [K, r]; ring
  have hbound := return_recurrence_bound f eps r (K * (4 : ℝ) ^ beta * u zStar) M
    heps.le heps1 hr.le (by rw [her]; norm_num) (by positivity) hfM hstep
  rw [her] at hbound
  have hcenter : u (point 1 0 v) ≤ f 0 :=
    le_csSup (hprops _ (returnIterationRadius_bounds 0).1
      (returnIterationRadius_bounds 0).2.le).1
      (mem_image_of_mem u (returnBox_center v _ (by norm_num [returnIterationRadius])))
  exact (hcenter.trans hbound).trans_eq (by dsimp [C]; ring)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
